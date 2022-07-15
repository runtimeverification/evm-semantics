from pyk.kast import (
    KApply,
    KDefinition,
    KInner,
    KNonTerminal,
    KSort,
    KTerminal,
    KVariable,
)
from pyk.kastManip import (
    abstract_term_safely,
    isAnonVariable,
    remove_generated_cells,
    splitConfigAndConstraints,
    splitConfigFrom,
    substitute,
)


def KDefinition_empty_config(definition: KDefinition, sort: KSort) -> KInner:

    def _kdefinition_empty_config(_sort):
        label = get_label_for_cell_sorts(definition, _sort)
        production = get_production_for_klabel(definition, label)
        args = []
        num_nonterminals = 0
        num_freshvars = 0
        for p_item in production.items:
            if type(p_item) is KNonTerminal:
                num_nonterminals += 1
                if p_item.sort.name.endswith('Cell'):
                    args.append(_kdefinition_empty_config(p_item.sort))
                else:
                    num_freshvars += 1
                    args.append(KVariable(_sort.name[0:-4].upper() + '_CELL'))
        if num_nonterminals > 1 and num_freshvars > 0:
            sort_name = sort.name
            raise ValueError(f'Found mixed cell and non-cell arguments to cell constructor for {sort_name}!')
        return KApply(label, args)

    return remove_generated_cells(_kdefinition_empty_config(sort))


def add_include_arg(includes):
    return [arg for include in includes for arg in ['-I', include]]


def abstract_cell_vars(cterm):
    state, _ = splitConfigAndConstraints(cterm)
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
