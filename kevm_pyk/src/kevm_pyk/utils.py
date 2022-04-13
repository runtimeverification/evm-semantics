from typing import List

from pyk.kast import KApply, KInner, flattenLabel
from pyk.kastManip import getCell
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


def abiUInt256(i: KInner) -> KApply:
    return KApply('#uint256(_)_EVM-ABI_TypedArg_Int', [i])


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
