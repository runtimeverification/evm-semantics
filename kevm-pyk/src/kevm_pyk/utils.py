from logging import Logger
from typing import Callable, Collection, Iterable, List, Optional, Tuple, TypeVar

from pyk.cterm import CTerm
from pyk.kast.inner import KApply, KInner, KRewrite, KVariable, Subst
from pyk.kast.manip import (
    abstract_term_safely,
    bool_to_ml_pred,
    bottom_up,
    flatten_label,
    free_vars,
    is_anon_var,
    ml_pred_to_bool,
    remove_generated_cells,
    split_config_and_constraints,
    split_config_from,
    undo_aliases,
)
from pyk.kast.outer import KClaim, KDefinition, KRule
from pyk.kcfg import KCFG
from pyk.ktool.kprove import KProve
from pyk.prelude.kbool import FALSE
from pyk.prelude.ml import mlAnd

T1 = TypeVar('T1')
T2 = TypeVar('T2')


def arg_pair_of(
    fst_type: Callable[[str], T1], snd_type: Callable[[str], T2], delim: str = ','
) -> Callable[[str], Tuple[T1, T2]]:
    def parse(s: str) -> Tuple[T1, T2]:
        elems = s.split(delim)
        length = len(elems)
        if length != 2:
            raise ValueError(f'Expected 2 elements, found {length}')
        return fst_type(elems[0]), snd_type(elems[1])

    return parse


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


def KCFG__replace_node(cfg: KCFG, node_id: str, new_cterm: CTerm) -> KCFG:  # noqa: N802
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
        cfg.create_cover(in_cover.source.id, new_node.id)
    for out_cover in out_covers:
        cfg.create_cover(new_node.id, out_cover.target.id)
    if init:
        cfg.add_init(new_node.id)
    if target:
        cfg.add_target(new_node.id)
    if expanded:
        cfg.add_expanded(new_node.id)
    for nid in in_expanded:
        if in_expanded[nid]:
            cfg.add_expanded(nid)

    return cfg


def KProve_prove_claim(  # noqa: N802
    kprove: KProve,
    claim: KClaim,
    claim_id: str,
    logger: Logger,
    depth: Optional[int] = None,
    lemmas: Iterable[KRule] = (),
) -> Tuple[bool, KInner]:
    logger.info(f'Proving claim: {claim_id}')
    prove_args = []
    if depth is not None:
        prove_args += ['--depth', str(depth)]
    result = kprove.prove_claim(claim, claim_id, args=prove_args, lemmas=lemmas)
    failed = False
    if type(result) is KApply and result.label.name == '#Top':
        logger.info(f'Proved claim: {claim_id}')
    else:
        logger.error(f'Failed to prove claim: {claim_id}')
        failed = True
    return failed, result


def add_include_arg(includes: Iterable[str]) -> List[str]:
    return [arg for include in includes for arg in ['-I', include]]


def abstract_cell_vars(cterm: KInner, keep_vars: Collection[KVariable] = ()) -> KInner:
    state, _ = split_config_and_constraints(cterm)
    config, subst = split_config_from(state)
    for s in subst:
        if type(subst[s]) is KVariable and not is_anon_var(subst[s]) and subst[s] not in keep_vars:
            subst[s] = abstract_term_safely(KVariable('_'), base_name=s)
    return Subst(subst)(config)


def sanitize_config(defn: KDefinition, init_term: KInner) -> KInner:
    def _var_name(vname: str) -> str:
        new_vname = vname
        while new_vname.startswith('_') or new_vname.startswith('?'):
            new_vname = new_vname[1:]
        return new_vname

    free_vars_subst = {vname: KVariable(_var_name(vname)) for vname in free_vars(init_term)}

    # TODO: This is somewhat hacky. We shouldn't have to touch the config this much.
    # Likely, the frontend should just be giving us initial states with these already in place.
    def _remove_cell_map_definedness(_kast: KInner) -> KInner:
        if type(_kast) is KApply:
            if _kast.label.name.endswith('CellMap:in_keys'):
                return FALSE
            elif _kast.label.name.endswith('CellMapItem'):
                return _kast.args[1]
        return _kast

    new_term = Subst(free_vars_subst)(init_term)
    new_term = remove_generated_cells(new_term)
    new_term = bottom_up(_remove_cell_map_definedness, new_term)

    if not (type(new_term) is KApply and new_term.label.name in ['#Top', '#Bottom']):
        config, constraint = split_config_and_constraints(new_term)
        constraints = [bool_to_ml_pred(ml_pred_to_bool(c, unsafe=True)) for c in flatten_label('#And', constraint)]
        new_term = mlAnd([config] + constraints)
        new_term = undo_aliases(defn, new_term)

    return new_term
