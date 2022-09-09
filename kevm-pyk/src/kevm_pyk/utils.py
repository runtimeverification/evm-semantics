from typing import Collection, Iterable, List

from pyk.cfg_manager import instantiate_cell_vars, rename_generated_vars
from pyk.cterm import CTerm
from pyk.kast import KClaim, KDefinition, KFlatModule, KImport, KTerminal, KVariable
from pyk.kastManip import (
    abstract_term_safely,
    bool_to_ml_pred,
    extract_lhs,
    extract_rhs,
    is_anon_var,
    split_config_and_constraints,
    split_config_from,
    substitute,
)
from pyk.kcfg import KCFG
from pyk.ktool import KPrint
from pyk.prelude import Bool, mlAnd


def KCFG_from_claim(defn: KDefinition, claim: KClaim) -> KCFG:  # noqa: N802
    cfg = KCFG()
    claim_body = claim.body
    claim_body = instantiate_cell_vars(defn, claim_body)
    claim_body = rename_generated_vars(CTerm(claim_body)).kast

    claim_lhs = extract_lhs(claim_body)
    claim_lhs = claim_lhs if claim.requires == Bool.true else mlAnd([claim_lhs, bool_to_ml_pred(claim.requires)])
    claim_lhs_cterm = CTerm(claim_lhs)
    init_state = cfg.create_node(claim_lhs_cterm)
    cfg.add_init(init_state.id)

    claim_rhs = extract_rhs(claim_body)
    claim_rhs = claim_rhs if claim.ensures == Bool.true else mlAnd([claim_rhs, bool_to_ml_pred(claim.ensures)])
    claim_rhs_cterm = CTerm(claim_rhs)
    target_state = cfg.create_node(claim_rhs_cterm)
    cfg.add_target(target_state.id)

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


def get_productions(definition):
    return [prod for module in definition.modules for prod in module.productions]


def get_production_for_klabel(definition, klabel):
    productions = [prod for prod in get_productions(definition) if prod.klabel and prod.klabel == klabel]
    if len(productions) != 1:
        raise ValueError(f'Expected 1 production for label {klabel}, not {productions}.')
    return productions[0]


def get_label_for_cell_sorts(definition, sort):
    productions = []
    for production in get_productions(definition):
        if production.sort == sort and len(production.items) >= 2:
            first_arg = production.items[0]
            if type(first_arg) is KTerminal and not (
                first_arg.value.startswith('project:')
                or first_arg.value.startswith('init')
                or first_arg.value.startswith('get')
            ):
                productions.append(production)
    if len(productions) != 1:
        raise ValueError(f'Expected 1 production for sort {sort}, not {productions}!')
    return productions[0].klabel
