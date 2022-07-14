import logging
import os
import sys
from pathlib import Path
from subprocess import CalledProcessError
from typing import Any, Dict, Final, List, Optional

from pyk.cli_utils import run_process
from pyk.kast import KApply, KInner
from pyk.kastManip import flattenLabel, getCell
from pyk.ktool import KProve, paren
from pyk.prelude import intToken, stringToken

from .utils import add_include_arg

_LOGGER: Final = logging.getLogger(__name__)


# KEVM class


class KEVM(KProve):

    def __init__(self, kompiled_directory, main_file_name=None, use_directory=None):
        super().__init__(kompiled_directory, main_file_name=main_file_name, use_directory=use_directory)
        KEVM._patch_symbol_table(self.symbol_table)

    @staticmethod
    def kompile(
        definition_dir: Path,
        main_file_name: Path,
        includes: List[str] = [],
        main_module_name: Optional[str] = None,
        syntax_module_name: Optional[str] = None,
        md_selector: Optional[str] = None,
        hook_namespaces: Optional[List[str]] = None,
        concrete_rules_file: Optional[Path] = None,
    ) -> 'KEVM':
        command = ['kompile', '--output-definition', str(definition_dir), str(main_file_name)]
        command += ['--emit-json', '--backend', 'haskell']
        command += ['--main-module', main_module_name] if main_module_name else []
        command += ['--syntax-module', syntax_module_name] if syntax_module_name else []
        command += ['--md-selector', md_selector] if md_selector else []
        command += ['--hook-namespaces', ' '.join(hook_namespaces)] if hook_namespaces else []
        command += add_include_arg(includes)
        if concrete_rules_file and os.path.exists(concrete_rules_file):
            with open(concrete_rules_file, 'r') as crf:
                concrete_rules = ','.join(crf.read().split('\n'))
                command += ['--concrete-rules', concrete_rules]
        try:
            run_process(command, _LOGGER)
        except CalledProcessError as err:
            sys.stderr.write(f'\nkompile stdout:\n{err.stdout}\n')
            sys.stderr.write(f'\nkompile stderr:\n{err.stderr}\n')
            sys.stderr.write(f'\nkompile returncode:\n{err.returncode}\n')
            sys.stderr.flush()
            raise
        return KEVM(definition_dir, main_file_name=main_file_name)

    @staticmethod
    def _patch_symbol_table(symbol_table: Dict[str, Any]) -> None:
        symbol_table['_orBool_']                                      = paren(symbol_table['_orBool_'])                                     # noqa
        symbol_table['_andBool_']                                     = paren(symbol_table['_andBool_'])                                    # noqa
        symbol_table['_impliesBool_']                                 = paren(symbol_table['_impliesBool_'])                                # noqa
        symbol_table['notBool_']                                      = paren(symbol_table['notBool_'])                                     # noqa
        symbol_table['_/Int_']                                        = paren(symbol_table['_/Int_'])                                       # noqa
        symbol_table['_*Int_']                                        = paren(symbol_table['_*Int_'])                                       # noqa
        symbol_table['_-Int_']                                        = paren(symbol_table['_-Int_'])                                       # noqa
        symbol_table['_+Int_']                                        = paren(symbol_table['_+Int_'])                                       # noqa
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

    @staticmethod
    def halt() -> KInner:
        return KApply('#halt_EVM_KItem')

    @staticmethod
    def execute() -> KInner:
        return KApply('#execute_EVM_KItem')

    @staticmethod
    def jumpi() -> KInner:
        return KApply('JUMPI_EVM_BinStackOp')

    @staticmethod
    def jump() -> KInner:
        return KApply('JUMP_EVM_UnStackOp')

    @staticmethod
    def jumpi_applied(pc: KInner, cond: KInner) -> KInner:
        return KApply('____EVM_InternalOp_BinStackOp_Int_Int', [KEVM.jumpi(), pc, cond])

    @staticmethod
    def jump_applied(pc: KInner) -> KInner:
        return KApply('___EVM_InternalOp_UnStackOp_Int', [KEVM.jump(), pc])

    @staticmethod
    def pow256():
        return KApply('pow256_EVM-TYPES_Int', [])

    @staticmethod
    def range_uint160(i: KInner) -> KApply:
        return KApply('#rangeUInt(_,_)_EVM-TYPES_Bool_Int_Int', [intToken(160), i])

    @staticmethod
    def range_uint256(i: KInner) -> KApply:
        return KApply('#rangeUInt(_,_)_EVM-TYPES_Bool_Int_Int', [intToken(256), i])

    @staticmethod
    def range_address(i: KInner) -> KApply:
        return KApply('#rangeAddress(_)_EVM-TYPES_Bool_Int', [i])

    @staticmethod
    def range_bool(i: KInner) -> KApply:
        return KApply('#rangeBool(_)_EVM-TYPES_Bool_Int', [i])

    @staticmethod
    def bool_2_word(cond: KInner) -> KInner:
        return KApply('bool2Word(_)_EVM-TYPES_Int_Bool', [cond])

    @staticmethod
    def size_bytearray(ba: KInner) -> KApply:
        return KApply('#sizeByteArray(_)_EVM-TYPES_Int_ByteArray', [ba])

    @staticmethod
    def inf_gas(g: KInner) -> KApply:
        return KApply('infGas', [g])

    @staticmethod
    def compute_valid_jumpdests(p: KInner) -> KApply:
        return KApply('#computeValidJumpDests(_)_EVM_Set_ByteArray', [p])

    @staticmethod
    def bin_runtime(c: KInner) -> KApply:
        return KApply('#binRuntime', [c])

    @staticmethod
    def abi_calldata(n: str, args: List[KInner]):
        token: KInner = stringToken(n)
        return KApply('#abiCallData', [token] + args)

    @staticmethod
    def abi_address(a: KInner) -> KApply:
        return KApply('#address(_)_EVM-ABI_TypedArg_Int', [a])

    @staticmethod
    def abi_bool(b: KInner) -> KApply:
        return KApply('#bool(_)_EVM-ABI_TypedArg_Int', [b])

    @staticmethod
    def empty_typedargs() -> KApply:
        return KApply('.List{"_,__EVM-ABI_TypedArgs_TypedArg_TypedArgs"}_TypedArgs')

    @staticmethod
    def bytes_append(b1: KInner, b2: KInner) -> KApply:
        return KApply('_++__EVM-TYPES_ByteArray_ByteArray_ByteArray', [b1, b2])

    @staticmethod
    def account_cell(id: KInner, balance: KInner, code: KInner, storage: KInner, origStorage: KInner, nonce: KInner) -> KApply:
        return KApply('<account>', [KApply('<acctID>', [id]),
                                    KApply('<balance>', [balance]),
                                    KApply('<code>', [code]),
                                    KApply('<storage>', [storage]),
                                    KApply('<origStorage>', [origStorage]),
                                    KApply('<nonce>', [nonce])])

    @staticmethod
    def wordstack_len(constrainedTerm: KInner) -> int:
        return len(flattenLabel('_:__EVM-TYPES_WordStack_Int_WordStack', getCell(constrainedTerm, 'WORDSTACK_CELL')))
