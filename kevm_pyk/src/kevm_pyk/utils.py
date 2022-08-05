from typing import List

from pyk.kast import KDefinition, KFlatModule, KImport, KTerminal, KVariable
from pyk.kastManip import (
    abstract_term_safely,
    isAnonVariable,
    split_config_and_constraints,
    splitConfigFrom,
    substitute,
)
from pyk.ktool import KPrint
from pyk.ktool.kprint import build_symbol_table
from pyk.utils import hash_str


def KPrint_make_unparsing(_self: KPrint, extra_modules: List[KFlatModule] = []) -> KPrint:
    modules = list(_self.definition.modules) + extra_modules
    main_module = KFlatModule('UNPARSING', [], [KImport(_m.name) for _m in modules])
    defn = KDefinition('UNPARSING', [main_module] + modules)
    kprint = KPrint(str(_self.kompiled_directory))
    kprint.definition = defn
    kprint.symbol_table = build_symbol_table(kprint.definition, opinionated=True)
    kprint.definition_hash = hash_str(kprint.definition)
    return kprint


def add_include_arg(includes):
    return [arg for include in includes for arg in ['-I', include]]


def abstract_cell_vars(cterm):
    state, _ = split_config_and_constraints(cterm)
    config, subst = splitConfigFrom(state)
    for s in subst:
        if type(subst[s]) is KVariable and not isAnonVariable(subst[s]):
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
            if type(first_arg) is KTerminal and not (first_arg.value.startswith('project:') or first_arg.value.startswith('init') or first_arg.value.startswith('get')):
                productions.append(production)
    if len(productions) != 1:
        raise ValueError(f'Expected 1 production for sort {sort}, not {productions}!')
    return productions[0].klabel
