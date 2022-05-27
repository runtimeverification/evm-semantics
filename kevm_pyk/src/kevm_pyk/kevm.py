from typing import Any, Dict, List

from pyk.kast import KApply, KInner, KSort
from pyk.kastManip import flattenLabel, getCell
from pyk.ktool import KProve, paren
from pyk.prelude import intToken, stringToken

from .utils import build_empty_configuration_cell

# KEVM helpers


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


def inf_gas(g: KInner) -> KApply:
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


def kevm_account_cell(id: KInner, balance: KInner, code: KInner, storage: KInner, origStorage: KInner, nonce: KInner) -> KApply:
    return KApply('<account>', [KApply('<acctID>', [id]),
                                KApply('<balance>', [balance]),
                                KApply('<code>', [code]),
                                KApply('<storage>', [storage]),
                                KApply('<origStorage>', [origStorage]),
                                KApply('<nonce>', [nonce])])


def kevm_wordstack_len(constrainedTerm: KInner) -> int:
    return len(flattenLabel('_:__EVM-TYPES_WordStack_Int_WordStack', getCell(constrainedTerm, 'WORDSTACK_CELL')))


# KEVM class


class KEVM(KProve):

    def __init__(self, kompiled_directory, main_file_name=None, use_directory=None):
        super().__init__(kompiled_directory, main_file_name=main_file_name, use_directory=use_directory)
        KEVM._patch_symbol_table(self.symbol_table)

    def empty_config(self, top_cell: KSort = KSort('GeneratedTopCell')) -> KInner:
        return build_empty_configuration_cell(self.definition, top_cell)

    @staticmethod
    def _patch_symbol_table(symbol_table: Dict[str, Any]) -> None:
        symbol_table['_orBool_']                                      = paren(symbol_table['_orBool_'])                                     # noqa
        symbol_table['_andBool_']                                     = paren(symbol_table['_andBool_'])                                    # noqa
        symbol_table['_impliesBool_']                                 = paren(symbol_table['_impliesBool_'])                                # noqa
        symbol_table['notBool_']                                      = paren(symbol_table['notBool_'])                                     # noqa
        symbol_table['_/Int_']                                        = paren(symbol_table['_/Int_'])                                       # noqa
        symbol_table['#Or']                                           = paren(symbol_table['#Or'])                                          # noqa
        symbol_table['#And']                                          = paren(symbol_table['#And'])                                         # noqa
        symbol_table['#Implies']                                      = paren(symbol_table['#Implies'])                                     # noqa
        symbol_table['_Set_']                                         = paren(symbol_table['_Set_'])                                        # noqa
        symbol_table['_|->_']                                         = paren(symbol_table['_|->_'])                                        # noqa
        symbol_table['_Map_']                                         = paren(lambda m1, m2: m1 + '\n' + m2)                                # noqa
        symbol_table['_AccountCellMap_']                              = paren(lambda a1, a2: a1 + '\n' + a2)                                # noqa
        symbol_table['AccountCellMapItem']                            = lambda k, v: v                                                      # noqa
        symbol_table['_[_:=_]_EVM-TYPES_Memory_Memory_Int_ByteArray'] = lambda m, k, v: m + ' [ '  + k + ' := (' + v + '):ByteArray ]'      # noqa
        symbol_table['_[_.._]_EVM-TYPES_ByteArray_ByteArray_Int_Int'] = lambda m, s, w: '(' + m + ' [ ' + s + ' .. ' + w + ' ]):ByteArray'  # noqa
        symbol_table['_<Word__EVM-TYPES_Int_Int_Int']                 = paren(lambda a1, a2: '(' + a1 + ') <Word ('  + a2 + ')')            # noqa
        symbol_table['_>Word__EVM-TYPES_Int_Int_Int']                 = paren(lambda a1, a2: '(' + a1 + ') >Word ('  + a2 + ')')            # noqa
        symbol_table['_<=Word__EVM-TYPES_Int_Int_Int']                = paren(lambda a1, a2: '(' + a1 + ') <=Word (' + a2 + ')')            # noqa
        symbol_table['_>=Word__EVM-TYPES_Int_Int_Int']                = paren(lambda a1, a2: '(' + a1 + ') >=Word (' + a2 + ')')            # noqa
        symbol_table['_==Word__EVM-TYPES_Int_Int_Int']                = paren(lambda a1, a2: '(' + a1 + ') ==Word (' + a2 + ')')            # noqa
        symbol_table['_s<Word__EVM-TYPES_Int_Int_Int']                = paren(lambda a1, a2: '(' + a1 + ') s<Word (' + a2 + ')')            # noqa
