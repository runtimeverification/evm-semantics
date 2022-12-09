from typing import Collection, Iterable, List, Tuple

from pyk.cterm import CTerm
from pyk.kast.inner import KApply, KInner, KRewrite, KVariable, Subst
from pyk.kast.manip import abstract_term_safely, bottom_up, is_anon_var, split_config_and_constraints, split_config_from
from pyk.kast.outer import KDefinition, KFlatModule, KImport
from pyk.kcfg import KCFG
from pyk.ktool import KPrint


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
