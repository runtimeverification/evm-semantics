import logging
import sys
from pathlib import Path
from subprocess import CalledProcessError
from typing import Any, Dict, Final, Iterable, List, Optional

from pyk.cli_utils import run_process
from pyk.kast import KApply, KInner, KLabel, KSort, KToken, KVariable, build_assoc
from pyk.kastManip import flatten_label, get_cell
from pyk.ktool import KProve, KRun
from pyk.ktool.kprint import paren
from pyk.prelude.kbool import notBool
from pyk.prelude.kint import intToken
from pyk.prelude.string import stringToken

from .utils import add_include_arg

_LOGGER: Final = logging.getLogger(__name__)


# KEVM class


class KEVM(KProve, KRun):
    def __init__(
        self,
        definition_dir: Path,
        main_file: Optional[Path] = None,
        use_directory: Optional[Path] = None,
        profile: bool = False,
    ) -> None:
        # I'm going for the simplest version here, we can change later if there is an advantage.
        # https://stackoverflow.com/questions/9575409/calling-parent-class-init-with-multiple-inheritance-whats-the-right-way
        # Note that they say using `super` supports dependency injection, but I have never liked dependency injection anyway.
        KProve.__init__(self, definition_dir, use_directory=use_directory, main_file=main_file, profile=profile)
        KRun.__init__(self, definition_dir, use_directory=use_directory, profile=profile)
        KEVM._patch_symbol_table(self.symbol_table)

    @staticmethod
    def kompile(
        definition_dir: Path,
        main_file: Path,
        emit_json: bool = True,
        includes: Iterable[str] = (),
        main_module_name: Optional[str] = None,
        syntax_module_name: Optional[str] = None,
        md_selector: Optional[str] = None,
        profile: bool = False,
    ) -> 'KEVM':
        command = ['kompile', '--output-definition', str(definition_dir), str(main_file)]
        command += ['--backend', 'haskell']
        command += ['--main-module', main_module_name] if main_module_name else []
        command += ['--syntax-module', syntax_module_name] if syntax_module_name else []
        command += ['--md-selector', md_selector] if md_selector else []
        command += ['--hook-namespaces', ' '.join(KEVM.hook_namespaces())]
        command += add_include_arg(includes)
        if emit_json:
            command += ['--emit-json']
        command += ['--concrete-rules', ','.join(KEVM.concrete_rules())]
        try:
            run_process(command, logger=_LOGGER, profile=profile)
        except CalledProcessError as err:
            sys.stderr.write(f'\nkompile stdout:\n{err.stdout}\n')
            sys.stderr.write(f'\nkompile stderr:\n{err.stderr}\n')
            sys.stderr.write(f'\nkompile returncode:\n{err.returncode}\n')
            sys.stderr.flush()
            raise
        return KEVM(definition_dir, main_file=main_file)

    @staticmethod
    def _patch_symbol_table(symbol_table: Dict[str, Any]) -> None:
        # fmt: off
        symbol_table['_orBool_']                                      = paren(symbol_table['_orBool_'])
        symbol_table['_andBool_']                                     = paren(symbol_table['_andBool_'])
        symbol_table['_impliesBool_']                                 = paren(symbol_table['_impliesBool_'])
        symbol_table['notBool_']                                      = paren(symbol_table['notBool_'])
        symbol_table['_/Int_']                                        = paren(symbol_table['_/Int_'])
        symbol_table['_*Int_']                                        = paren(symbol_table['_*Int_'])
        symbol_table['_-Int_']                                        = paren(symbol_table['_-Int_'])
        symbol_table['_+Int_']                                        = paren(symbol_table['_+Int_'])
        symbol_table['#Or']                                           = paren(symbol_table['#Or'])
        symbol_table['#And']                                          = paren(symbol_table['#And'])
        symbol_table['#Implies']                                      = paren(symbol_table['#Implies'])
        symbol_table['_Set_']                                         = paren(symbol_table['_Set_'])
        symbol_table['_|->_']                                         = paren(symbol_table['_|->_'])
        symbol_table['_Map_']                                         = paren(lambda m1, m2: m1 + '\n' + m2)
        symbol_table['_AccountCellMap_']                              = paren(lambda a1, a2: a1 + '\n' + a2)
        symbol_table['.AccountCellMap']                               = lambda: '.Bag'
        symbol_table['AccountCellMapItem']                            = lambda k, v: v
        symbol_table['_[_:=_]_EVM-TYPES_Memory_Memory_Int_ByteArray'] = lambda m, k, v: m + ' [ '  + k + ' := (' + v + '):ByteArray ]'
        symbol_table['_[_.._]_EVM-TYPES_ByteArray_ByteArray_Int_Int'] = lambda m, s, w: '(' + m + ' [ ' + s + ' .. ' + w + ' ]):ByteArray'
        symbol_table['_<Word__EVM-TYPES_Int_Int_Int']                 = paren(lambda a1, a2: '(' + a1 + ') <Word ('  + a2 + ')')
        symbol_table['_>Word__EVM-TYPES_Int_Int_Int']                 = paren(lambda a1, a2: '(' + a1 + ') >Word ('  + a2 + ')')
        symbol_table['_<=Word__EVM-TYPES_Int_Int_Int']                = paren(lambda a1, a2: '(' + a1 + ') <=Word (' + a2 + ')')
        symbol_table['_>=Word__EVM-TYPES_Int_Int_Int']                = paren(lambda a1, a2: '(' + a1 + ') >=Word (' + a2 + ')')
        symbol_table['_==Word__EVM-TYPES_Int_Int_Int']                = paren(lambda a1, a2: '(' + a1 + ') ==Word (' + a2 + ')')
        symbol_table['_s<Word__EVM-TYPES_Int_Int_Int']                = paren(lambda a1, a2: '(' + a1 + ') s<Word (' + a2 + ')')
        # fmt: on

    class Sorts:
        KEVM_CELL: Final = KSort('KevmCell')

    @staticmethod
    def hook_namespaces() -> List[str]:
        return ['JSON', 'KRYPTO', 'BLOCKCHAIN']

    @staticmethod
    def concrete_rules() -> List[str]:
        return [
            'EVM.allBut64th.pos',
            'EVM.Caddraccess',
            'EVM.Cbalance.new',
            'EVM.Cbalance.old',
            'EVM.Cextcodecopy.new',
            'EVM.Cextcodecopy.old',
            'EVM.Cextcodehash.new',
            'EVM.Cextcodehash.old',
            'EVM.Cextcodesize.new',
            'EVM.Cextcodesize.old',
            'EVM.Cextra.new',
            'EVM.Cextra.old',
            'EVM.Cgascap',
            'EVM.Cmem',
            'EVM.Cmodexp.new',
            'EVM.Cmodexp.old',
            'EVM.Csload.new',
            'EVM.Csstore.new',
            'EVM.Csstore.old',
            'EVM.Cstorageaccess',
            'EVM.ecrec',
            'EVM.#memoryUsageUpdate.some',
            'EVM.Rsstore.new',
            'EVM.Rsstore.old',
            'EVM-TYPES.#asByteStack',
            'EVM-TYPES.#asByteStackAux.recursive',
            'EVM-TYPES.#asWord.recursive',
            'EVM-TYPES.ByteArray.range',
            'EVM-TYPES.bytesRange',
            'EVM-TYPES.mapWriteBytes.recursive',
            'EVM-TYPES.#padRightToWidth',
            'EVM-TYPES.#padToWidth',
            'EVM-TYPES.padToWidthNonEmpty',
            'EVM-TYPES.powmod.nonzero',
            'EVM-TYPES.powmod.zero',
            'EVM-TYPES.#range',
            'EVM-TYPES.signextend.invalid',
            'EVM-TYPES.signextend.negative',
            'EVM-TYPES.signextend.positive',
            'EVM-TYPES.upDivInt',
            'SERIALIZATION.keccak',
            'SERIALIZATION.#newAddr',
            'SERIALIZATION.#newAddrCreate2',
        ]

    @staticmethod
    def halt() -> KApply:
        return KApply('#halt_EVM_KItem')

    @staticmethod
    def execute() -> KApply:
        return KApply('#execute_EVM_KItem')

    @staticmethod
    def jumpi() -> KApply:
        return KApply('JUMPI_EVM_BinStackOp')

    @staticmethod
    def jump() -> KApply:
        return KApply('JUMP_EVM_UnStackOp')

    @staticmethod
    def jumpi_applied(pc: KInner, cond: KInner) -> KApply:
        return KApply('____EVM_InternalOp_BinStackOp_Int_Int', [KEVM.jumpi(), pc, cond])

    @staticmethod
    def jump_applied(pc: KInner) -> KApply:
        return KApply('___EVM_InternalOp_UnStackOp_Int', [KEVM.jump(), pc])

    @staticmethod
    def pow256() -> KApply:
        return KApply('pow256_WORD_Int', [])

    @staticmethod
    def range_uint(width: int, i: KInner) -> KApply:
        return KApply('#rangeUInt(_,_)_WORD_Bool_Int_Int', [intToken(width), i])

    @staticmethod
    def range_sint(width: int, i: KInner) -> KApply:
        return KApply('#rangeSInt(_,_)_WORD_Bool_Int_Int', [intToken(width), i])

    @staticmethod
    def range_address(i: KInner) -> KApply:
        return KApply('#rangeAddress(_)_WORD_Bool_Int', [i])

    @staticmethod
    def range_bool(i: KInner) -> KApply:
        return KApply('#rangeBool(_)_WORD_Bool_Int', [i])

    @staticmethod
    def range_bytes(width: KInner, ba: KInner) -> KApply:
        return KApply('#rangeBytes(_,_)_WORD_Bool_Int_Int', [width, ba])

    @staticmethod
    def bool_2_word(cond: KInner) -> KApply:
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
        return KApply('binRuntime', [c])

    @staticmethod
    def hashed_location(compiler: str, base: KInner, offset: KInner, member_offset: int = 0) -> KApply:
        location = KApply(
            '#hashedLocation(_,_,_)_HASHED-LOCATIONS_Int_String_Int_IntList', [stringToken(compiler), base, offset]
        )
        if member_offset > 0:
            location = KApply('_+Int_', [location, intToken(member_offset)])
        return location

    @staticmethod
    def loc(accessor: KInner) -> KApply:
        return KApply('contract_access_loc', [accessor])

    @staticmethod
    def lookup(map: KInner, key: KInner) -> KApply:
        return KApply('#lookup(_,_)_EVM-TYPES_Int_Map_Int', [map, key])

    @staticmethod
    def abi_calldata(name: str, args: List[KInner]) -> KApply:
        return KApply(
            '#abiCallData(_,_)_EVM-ABI_ByteArray_String_TypedArgs', [stringToken(name), KEVM.typed_args(args)]
        )

    @staticmethod
    def abi_selector(name: str) -> KApply:
        return KApply('abi_selector', [stringToken(name)])

    @staticmethod
    def abi_address(a: KInner) -> KApply:
        return KApply('#address(_)_EVM-ABI_TypedArg_Int', [a])

    @staticmethod
    def abi_bool(b: KInner) -> KApply:
        return KApply('#bool(_)_EVM-ABI_TypedArg_Int', [b])

    @staticmethod
    def abi_type(type: str, value: KInner) -> KApply:
        return KApply('abi_type_' + type, [value])

    @staticmethod
    def empty_typedargs() -> KApply:
        return KApply('.List{"_,__EVM-ABI_TypedArgs_TypedArg_TypedArgs"}_TypedArgs')

    @staticmethod
    def bytes_append(b1: KInner, b2: KInner) -> KApply:
        return KApply('_++__EVM-TYPES_ByteArray_ByteArray_ByteArray', [b1, b2])

    @staticmethod
    def account_cell(
        id: KInner, balance: KInner, code: KInner, storage: KInner, orig_storage: KInner, nonce: KInner
    ) -> KApply:
        return KApply(
            '<account>',
            [
                KApply('<acctID>', [id]),
                KApply('<balance>', [balance]),
                KApply('<code>', [code]),
                KApply('<storage>', [storage]),
                KApply('<origStorage>', [orig_storage]),
                KApply('<nonce>', [nonce]),
            ],
        )

    @staticmethod
    def wordstack_len(constrained_term: KInner) -> int:
        return len(flatten_label('_:__EVM-TYPES_WordStack_Int_WordStack', get_cell(constrained_term, 'WORDSTACK_CELL')))

    @staticmethod
    def parse_bytestack(s: KInner) -> KApply:
        return KApply('#parseByteStack(_)_SERIALIZATION_ByteArray_String', [s])

    @staticmethod
    def bytearray_empty() -> KApply:
        return KApply('.ByteArray_EVM-TYPES_ByteArray')

    @staticmethod
    def intlist(ints: List[KInner]) -> KApply:
        res = KApply('.List{"___HASHED-LOCATIONS_IntList_Int_IntList"}_IntList')
        for i in reversed(ints):
            res = KApply('___HASHED-LOCATIONS_IntList_Int_IntList', [i, res])
        return res

    @staticmethod
    def typed_args(args: List[KInner]) -> KApply:
        res = KApply('.List{"_,__EVM-ABI_TypedArgs_TypedArg_TypedArgs"}_TypedArgs')
        for i in reversed(args):
            res = KApply('_,__EVM-ABI_TypedArgs_TypedArg_TypedArgs', [i, res])
        return res

    @staticmethod
    def accounts(accts: List[KInner]) -> KInner:
        return build_assoc(KApply('.AccountCellMap'), KLabel('_AccountCellMap_'), accts)


class Foundry(KEVM):
    def __init__(
        self,
        definition_dir: Path,
        main_file: Optional[Path] = None,
        use_directory: Optional[Path] = None,
        profile: bool = False,
    ) -> None:
        # copied from KEVM class and adapted to inherit KPrint instead
        KEVM.__init__(self, definition_dir, main_file=main_file, use_directory=use_directory, profile=profile)
        Foundry._patch_symbol_table(self.symbol_table)

    class Sorts:
        FOUNDRY_CELL: Final = KSort('FoundryCell')

    @staticmethod
    def _patch_symbol_table(symbol_table: Dict[str, Any]) -> None:
        KEVM._patch_symbol_table(symbol_table)

    @staticmethod
    def success(s: KInner, dst: KInner) -> KApply:
        return KApply('foundry_success ', [s, dst])

    @staticmethod
    def fail(s: KInner, dst: KInner) -> KApply:
        return notBool(Foundry.success(s, dst))

    # address(uint160(uint256(keccak256("foundry default caller"))))

    @staticmethod
    def address_CALLER() -> KToken:  # noqa: N802
        return intToken(0x1804C8AB1F12E6BBF3894D4083F33E07309D1F38)

    @staticmethod
    def account_CALLER() -> KApply:  # noqa: N802
        return KEVM.account_cell(
            Foundry.address_CALLER(), intToken(0), KEVM.bytearray_empty(), KApply('.Map'), KApply('.Map'), intToken(0)
        )

    @staticmethod
    def address_TEST_CONTRACT() -> KToken:  # noqa: N802
        return intToken(0xB4C79DAB8F259C7AEE6E5B2AA729821864227E84)

    @staticmethod
    def account_TEST_CONTRACT_ADDRESS() -> KApply:  # noqa: N802
        return KEVM.account_cell(
            Foundry.address_TEST_CONTRACT(),
            intToken(0),
            KVariable('TEST_CODE'),
            KApply('.Map'),
            KApply('.Map'),
            intToken(0),
        )

    @staticmethod
    def address_CHEATCODE() -> KToken:  # noqa: N802
        return intToken(0x7109709ECFA91A80626FF3989D68F67F5B1DD12D)

    # Same address as the one used in DappTools's HEVM
    # address(bytes20(uint160(uint256(keccak256('hevm cheat code')))))
    @staticmethod
    def account_CHEATCODE_ADDRESS(store_var: KInner) -> KApply:  # noqa: N802
        return KEVM.account_cell(
            Foundry.address_CHEATCODE(),  # Hardcoded for now
            intToken(0),
            KToken('b"\\x00"', 'Bytes'),
            store_var,
            KApply('.Map'),
            intToken(0),
        )

    @staticmethod
    def address_HARDHAT_CONSOLE() -> KToken:  # noqa: N802
        return intToken(0x000000000000000000636F6E736F6C652E6C6F67)

    # Hardhat console address (0x000000000000000000636F6e736F6c652e6c6f67)
    # https://github.com/nomiclabs/hardhat/blob/master/packages/hardhat-core/console.sol
    @staticmethod
    def account_HARDHAT_CONSOLE_ADDRESS() -> KApply:  # noqa: N802
        return KEVM.account_cell(
            Foundry.address_HARDHAT_CONSOLE(),
            intToken(0),
            KEVM.bytearray_empty(),
            KApply('.Map'),
            KApply('.Map'),
            intToken(0),
        )
