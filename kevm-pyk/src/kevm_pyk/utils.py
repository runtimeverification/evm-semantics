from logging import Logger
from pathlib import Path
from typing import Collection, Iterable, List, Optional, Tuple

from pyk.cfg_manager import instantiate_cell_vars, rename_generated_vars
from pyk.cterm import CTerm
from pyk.kast import (
    KApply,
    KClaim,
    KDefinition,
    KFlatModule,
    KFlatModuleList,
    KImport,
    KInner,
    KRule,
    KVariable,
    read_kast,
)
from pyk.kastManip import (
    abstract_term_safely,
    bool_to_ml_pred,
    bottom_up,
    extract_lhs,
    extract_rhs,
    flatten_label,
    free_vars,
    is_anon_var,
    ml_pred_to_bool,
    remove_generated_cells,
    split_config_and_constraints,
    split_config_from,
    substitute,
    undo_aliases,
)
from pyk.kcfg import KCFG
from pyk.ktool import KPrint, KProve
from pyk.prelude import Bool, mlAnd


def KProve_prove_claim(  # noqa: N802
    kprove: KProve,
    claim: KClaim,
    claim_id: str,
    logger: Logger,
    depth: Optional[int] = None,
    lemmas: Iterable[KRule] = (),
) -> Tuple[bool, KInner]:
    logger.info(f'Proving KCFG: {claim_id}')
    prove_args = []
    if depth is not None:
        prove_args += ['--depth', str(depth)]
    result = kprove.prove_claim(claim, claim_id, args=prove_args, lemmas=lemmas)
    failed = False
    if type(result) is KApply and result.label.name == '#Top':
        logger.info(f'Proved KCFG: {claim_id}')
    else:
        logger.error(f'Failed to prove KCFG: {claim_id}')
        failed = True
    return failed, result


def read_kast_flatmodulelist(ifile: Path) -> KFlatModuleList:
    _flat_module_list = read_kast(ifile)
    assert isinstance(_flat_module_list, KFlatModuleList)
    return _flat_module_list


def KCFG_from_claim(defn: KDefinition, claim: KClaim) -> KCFG:  # noqa: N802
    def _make_cterm(_kinner: KInner, _cond: KInner) -> CTerm:
        _kinner = _kinner if _cond == Bool.true else mlAnd([_kinner, bool_to_ml_pred(_cond)])
        _kinner = sanitize_config(defn, _kinner)
        return CTerm(_kinner)

    cfg = KCFG()
    claim_body = claim.body
    claim_body = instantiate_cell_vars(defn, claim_body)
    claim_body = rename_generated_vars(CTerm(claim_body)).kast

    claim_lhs = _make_cterm(extract_lhs(claim_body), claim.requires)
    init_node = cfg.create_node(claim_lhs)
    cfg.add_init(init_node.id)

    claim_rhs = _make_cterm(extract_rhs(claim_body), claim.ensures)
    target_node = cfg.create_node(claim_rhs)
    cfg.add_target(target_node.id)

    return cfg


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


def abstract_cell_vars(cterm, keep_vars: Collection[KVariable] = ()):
    state, _ = split_config_and_constraints(cterm)
    config, subst = split_config_from(state)
    for s in subst:
        if type(subst[s]) is KVariable and not is_anon_var(subst[s]) and subst[s] not in keep_vars:
            subst[s] = abstract_term_safely(KVariable('_'), base_name=s)
    return substitute(config, subst)


def sanitize_config(defn: KDefinition, init_term: KInner) -> KInner:
    def _var_name(vname):
        new_vname = vname
        while new_vname.startswith('_') or new_vname.startswith('?'):
            new_vname = new_vname[1:]
        return new_vname

    free_vars_subst = {vname: KVariable(_var_name(vname)) for vname in free_vars(init_term)}

    # TODO: This is somewhat hacky. We shouldn't have to touch the config this much.
    # Likely, the frontend should just be giving us initial states with these already in place.
    def _remove_cell_map_definedness(_kast):
        if type(_kast) is KApply:
            if _kast.label.name.endswith('CellMap:in_keys'):
                return Bool.false
            elif _kast.label.name.endswith('CellMapItem'):
                return _kast.args[1]
        return _kast

    new_term = substitute(init_term, free_vars_subst)
    new_term = remove_generated_cells(new_term)
    new_term = bottom_up(_remove_cell_map_definedness, new_term)

    if not (type(new_term) is KApply and new_term.label.name in ['#Top', '#Bottom']):
        config, constraint = split_config_and_constraints(new_term)
        constraints = [bool_to_ml_pred(ml_pred_to_bool(c, unsafe=True)) for c in flatten_label('#And', constraint)]
        new_term = mlAnd([config] + constraints)
        new_term = undo_aliases(defn, new_term)

    return new_term
