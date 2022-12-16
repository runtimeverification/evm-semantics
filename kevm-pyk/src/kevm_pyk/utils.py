import logging
from pathlib import Path
from typing import Callable, Collection, Final, Iterable, List, Optional, Tuple

from pyk.cterm import CTerm
from pyk.kast.inner import KApply, KInner, KRewrite, KVariable, Subst
from pyk.kast.manip import abstract_term_safely, bottom_up, is_anon_var, split_config_and_constraints, split_config_from
from pyk.kast.outer import KDefinition, KFlatModule, KImport
from pyk.kcfg import KCFG
from pyk.ktool import KPrint, KProve
from pyk.prelude.ml import is_bottom, is_top, mlAnd, mlTop
from pyk.utils import shorten_hashes

_LOGGER: Final = logging.getLogger(__name__)


def write_cfg(_cfg: KCFG, _cfgpath: Path) -> None:
    _cfgpath.write_text(_cfg.to_json())
    _LOGGER.info(f'Updated CFG file: {_cfgpath}')


def byte_offset_to_lines(lines: Iterable[str], byte_start: int, byte_width: int) -> Tuple[List[str], int, int]:
    text_lines = []
    line_start = 0
    for l in lines:
        if len(l) < byte_start:
            byte_start -= len(l) + 1
            line_start += 1
        else:
            break
    line_end = line_start
    for l in list(lines)[line_start:]:
        if byte_start + byte_width < 0:
            break
        else:
            text_lines.append(l)
            byte_width -= len(l) + 1
            line_end += 1
    return (text_lines, line_start, line_end)


def rpc_prove(
    kprove: KProve,
    cfgid: str,
    cfg: KCFG,
    cfgpath: Path,
    rpc_port: int,
    is_terminal: Optional[Callable[[CTerm], bool]] = None,
    extract_branches: Optional[Callable[[CTerm], Iterable[KInner]]] = None,
    auto_abstract: Optional[Callable[[CTerm], CTerm]] = None,
    max_iterations: Optional[int] = None,
    max_depth: Optional[int] = None,
    cut_point_rules: Iterable[str] = (),
    terminal_rules: Iterable[str] = (),
    simplify_init: bool = True,
    implication_every_block: bool = False,
) -> bool:
    kprove.set_kore_rpc_port(rpc_port)

    if simplify_init:
        for node in cfg.nodes:
            _LOGGER.info(f'Simplifying node {cfgid}: {shorten_hashes(node.id)}')
            new_term = kprove.simplify(node.cterm)
            if is_top(new_term):
                raise ValueError(f'Node simplified to #Top {cfgid}: {shorten_hashes(node.id)}')
            if is_bottom(new_term):
                raise ValueError(f'Node simplified to #Bottom {cfgid}: {shorten_hashes(node.id)}')
            if new_term != node.cterm.kast:
                KCFG__replace_node(cfg, node.id, CTerm(new_term))
    write_cfg(cfg, cfgpath)

    target_node = cfg.get_unique_target()
    iterations = 0

    while cfg.frontier:
        write_cfg(cfg, cfgpath)
        if max_iterations is not None and max_iterations <= iterations:
            _LOGGER.warning(f'Reached iteration bound: {max_iterations}')
            break
        iterations += 1
        curr_node = cfg.frontier[0]

        if implication_every_block or (is_terminal is not None and is_terminal(curr_node.cterm)):
            _LOGGER.info(
                f'Checking subsumption into target state {cfgid}: {shorten_hashes((curr_node.id, target_node.id))}'
            )
            impl = kprove.implies(curr_node.cterm, target_node.cterm)
            if impl is not None:
                subst, pred = impl
                cfg.create_cover(curr_node.id, target_node.id, subst=subst, constraint=pred)
                _LOGGER.info(f'Subsumed into target node: {shorten_hashes((curr_node.id, target_node.id))}')
                continue

        if is_terminal is not None:
            _LOGGER.info(f'Checking terminal {cfgid}: {shorten_hashes(curr_node.id)}')
            if is_terminal(curr_node.cterm):
                _LOGGER.info(f'Terminal node {cfgid}: {shorten_hashes(curr_node.id)}.')
                cfg.add_expanded(curr_node.id)
                continue

        if auto_abstract is not None:
            _LOGGER.info(f'Auto abstraction {cfgid}: {shorten_hashes(curr_node.id)}')
            abstracted = auto_abstract(curr_node.cterm)
            if abstracted != curr_node.cterm:
                abstracted_node = cfg.get_or_create_node(abstracted)
                cfg.create_cover(curr_node.id, abstracted_node.id)
                _LOGGER.info(f'Abstracted node: {shorten_hashes((curr_node.id, abstracted_node.id))}')
                continue

        cfg.add_expanded(curr_node.id)

        _LOGGER.info(f'Advancing proof from node {cfgid}: {shorten_hashes(curr_node.id)}')
        depth, cterm, next_cterms = kprove.execute(
            curr_node.cterm, depth=max_depth, cut_point_rules=cut_point_rules, terminal_rules=terminal_rules
        )

        # Nonsense case.
        if len(next_cterms) == 1:
            raise ValueError(f'Found a single successor cterm: {(depth, cterm, next_cterms)}')

        if len(next_cterms) == 0 and depth == 0:
            _LOGGER.info(f'Found stuck node {cfgid}: {shorten_hashes(curr_node.id)}')
            continue

        if depth > 0:
            next_node = cfg.get_or_create_node(cterm)
            cfg.create_edge(curr_node.id, next_node.id, mlTop(), depth)
            _LOGGER.info(
                f'Found basic block at depth {depth} for {cfgid}: {shorten_hashes((curr_node.id, next_node.id))}.'
            )

            branches = extract_branches(cterm) if extract_branches is not None else []
            if len(list(branches)) > 0:
                cfg.add_expanded(next_node.id)
                _LOGGER.info(
                    f'Found {len(list(branches))} branches {cfgid}: {[kprove.pretty_print(b) for b in branches]}'
                )
                splits = cfg.split_node(next_node.id, branches)
                _LOGGER.info(f'Made split for {cfgid}: {shorten_hashes((next_node.id, splits))}')
                continue

        else:
            _LOGGER.warning(f'Falling back to manual branch extraction {cfgid}: {shorten_hashes(curr_node.id)}')
            branch_constraints = [[c for c in s.constraints if c not in cterm.constraints] for s in next_cterms]
            _LOGGER.info(
                f'Found {len(list(next_cterms))} branches manually at depth 1 for {cfgid}: {[kprove.pretty_print(mlAnd(bc)) for bc in branch_constraints]}'
            )
            for bs, bc in zip(next_cterms, branch_constraints, strict=True):
                branch_node = cfg.get_or_create_node(bs)
                cfg.create_edge(curr_node.id, branch_node.id, mlAnd(bc), 1)

    write_cfg(cfg, cfgpath)
    kprove.close()

    failure_nodes = cfg.frontier + cfg.stuck
    if len(failure_nodes) == 0:
        _LOGGER.info(f'Proof passed: {cfgid}')
        return True
    else:
        _LOGGER.error(f'Proof failed: {cfgid}')
        return False


def KDefinition__expand_macros(defn: KDefinition, term: KInner) -> KInner:  # noqa: N802
    def _expand_macros(_term: KInner) -> KInner:
        if type(_term) is KApply:
            prod = defn.production_for_klabel(_term.label)
            if 'macro' in prod.att or 'alias' in prod.att or 'macro-rec' in prod.att or 'alias-rec' in prod.att:
                for r in defn.macro_rules:
                    assert type(r.body) is KRewrite
                    _new_term = r.body.apply_top(_term)
                    if _new_term != _term:
                        _term = _new_term
                        break
        return _term

    old_term = None
    while term != old_term:
        old_term = term
        term = bottom_up(_expand_macros, term)

    return term


def KCFG__replace_node(cfg: KCFG, node_id: str, new_cterm: CTerm) -> Tuple[KCFG, str]:  # noqa: N802

    # Remove old node, record data
    node = cfg.node(node_id)
    in_edges = cfg.edges(target_id=node.id)
    out_edges = cfg.edges(source_id=node.id)
    in_covers = cfg.covers(target_id=node.id)
    out_covers = cfg.covers(source_id=node.id)
    init = cfg.is_init(node.id)
    target = cfg.is_target(node.id)
    expanded = cfg.is_expanded(node.id)
    in_expanded = {edge.source.id: cfg.is_expanded(edge.source.id) for edge in in_edges}
    cfg.remove_node(node.id)

    # Add the new, update data
    new_node = cfg.get_or_create_node(new_cterm)
    for in_edge in in_edges:
        cfg.create_edge(in_edge.source.id, new_node.id, in_edge.condition, in_edge.depth)
    for out_edge in out_edges:
        cfg.create_edge(new_node.id, out_edge.target.id, out_edge.condition, out_edge.depth)
    for in_cover in in_covers:
        cfg.create_cover(in_cover.source.id, new_node.id, subst=in_cover.subst, constraint=in_cover.constraint)
    for out_cover in out_covers:
        cfg.create_cover(new_node.id, out_cover.target.id, subst=in_cover.subst, constraint=in_cover.constraint)
    if init:
        cfg.add_init(new_node.id)
    if target:
        cfg.add_target(new_node.id)
    if expanded:
        cfg.add_expanded(new_node.id)
    for nid in in_expanded:
        if in_expanded[nid]:
            cfg.add_expanded(nid)

    return (cfg, new_node.id)


def KPrint_make_unparsing(_self: KPrint, extra_modules: Iterable[KFlatModule] = ()) -> KPrint:  # noqa: N802
    modules = _self.definition.modules + tuple(extra_modules)
    main_module = KFlatModule('UNPARSING', [], [KImport(_m.name) for _m in modules])
    defn = KDefinition('UNPARSING', (main_module,) + modules)
    kprint = KPrint(_self.definition_dir)
    kprint._definition = defn
    kprint._symbol_table = None
    return kprint


def add_include_arg(includes: Iterable[str]) -> List[str]:
    return [arg for include in includes for arg in ['-I', include]]


def abstract_cell_vars(cterm: KInner, keep_vars: Collection[KVariable] = ()) -> KInner:
    state, _ = split_config_and_constraints(cterm)
    config, subst = split_config_from(state)
    for s in subst:
        if type(subst[s]) is KVariable and not is_anon_var(subst[s]) and subst[s] not in keep_vars:
            subst[s] = abstract_term_safely(KVariable('_'), base_name=s)
    return Subst(subst)(config)


def replace_special_chars(inp: str, c: str) -> str:
    return inp.replace('.', c).replace('-', c).replace('_', c).replace('/', c)
