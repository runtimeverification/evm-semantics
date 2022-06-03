from typing import List

from pyk.kast import (
    KApply,
    KInner,
    KNonTerminal,
    KTerminal,
    KVariable,
    flattenLabel,
)
from pyk.kastManip import (
    abstractTermSafely,
    getCell,
    isAnonVariable,
    splitConfigAndConstraints,
    splitConfigFrom,
    substitute,
)
from pyk.prelude import intToken, stringToken


def pow256():
    return KApply('pow256_EVM-TYPES_Int', [])


def rangeUInt160(i: KInner) -> KApply:
    return KApply('#rangeUInt(_,_)_EVM-TYPES_Bool_Int_Int', [intToken(160), i])


def rangeUInt256(i: KInner) -> KApply:
    return KApply('#rangeUInt(_,_)_EVM-TYPES_Bool_Int_Int', [intToken(256), i])


def rangeAddress(i: KInner) -> KApply:
    return KApply('#rangeAddress(_)_EVM-TYPES_Bool_Int', [i])


def rangeBool(i: KInner) -> KApply:
    return KApply('#rangeBool(_)_EVM-TYPES_Bool_Int', [i])


def sizeByteArray(ba: KInner) -> KApply:
    return KApply('#sizeByteArray(_)_EVM-TYPES_Int_ByteArray', [ba])


def infGas(g: KInner) -> KApply:
    return KApply('infGas', [g])


def computeValidJumpDests(p: KInner) -> KApply:
    return KApply('#computeValidJumpDests(_)_EVM_Set_ByteArray', [p])


def binRuntime(c: KInner) -> KApply:
    return KApply('#binRuntime', [c])


def abiCallData(n: str, args: List[KInner]):
    token: KInner = stringToken(n)
    return KApply('#abiCallData', [token] + args)


def abiAddress(a: KInner) -> KApply:
    return KApply('#address(_)_EVM-ABI_TypedArg_Int', [a])


def abiBool(b: KInner) -> KApply:
    return KApply('#bool(_)_EVM-ABI_TypedArg_Int', [b])


def emptyTypedArgs() -> KApply:
    return KApply('.List{"_,__EVM-ABI_TypedArgs_TypedArg_TypedArgs"}_TypedArgs')


def bytesAppend(b1: KInner, b2: KInner) -> KApply:
    return KApply('_++__EVM-TYPES_ByteArray_ByteArray_ByteArray', [b1, b2])


def kevmAccountCell(
    id: KInner,
    balance: KInner,
    code: KInner,
    storage: KInner,
    origStorage: KInner,
    nonce: KInner,
) -> KApply:
    return KApply('<account>', [KApply('<acctID>', [id]),
                                KApply('<balance>', [balance]),
                                KApply('<code>', [code]),
                                KApply('<storage>', [storage]),
                                KApply('<origStorage>', [origStorage]),
                                KApply('<nonce>', [nonce])])


def kevmWordStackLen(constrainedTerm: KInner) -> int:
    return len(flattenLabel('_:__EVM-TYPES_WordStack_Int_WordStack', getCell(constrainedTerm, 'WORDSTACK_CELL')))


def abstract_cell_vars(cterm):
    state, _ = splitConfigAndConstraints(cterm)
    config, subst = splitConfigFrom(state)
    for s in subst:
        if type(subst[s]) is KVariable and not isAnonVariable(subst[s]):
            subst[s] = abstractTermSafely(KVariable('_'), baseName=s)
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


def build_empty_configuration_cell(definition, sort):
    label = get_label_for_cell_sorts(definition, sort)
    production = get_production_for_klabel(definition, label)
    args = []
    num_nonterminals = 0
    num_freshvars = 0
    for p_item in production.items:
        if type(p_item) is KNonTerminal:
            num_nonterminals += 1
            if p_item.sort.name.endswith('Cell'):
                args.append(build_empty_configuration_cell(definition, p_item.sort))
            else:
                num_freshvars += 1
                args.append(KVariable(sort.name[0:-4].upper() + '_CELL'))
    if num_nonterminals > 1 and num_freshvars > 0:
        sort_name = sort.name
        raise ValueError(f'Found mixed cell and non-cell arguments to cell constructor for {sort_name}!')
    return KApply(label, args)
