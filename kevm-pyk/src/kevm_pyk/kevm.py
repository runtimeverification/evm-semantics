from __future__ import annotations

import logging
from typing import TYPE_CHECKING

from pyk.cterm import CTerm
from pyk.kast.inner import KApply, KLabel, KSequence, KSort, KVariable, build_assoc, build_cons
from pyk.kast.manip import abstract_term_safely, bottom_up, flatten_label
from pyk.kast.pretty import paren
from pyk.kcfg.semantics import KCFGSemantics
from pyk.kcfg.show import NodePrinter
from pyk.ktool.kprove import KProve
from pyk.ktool.krun import KRun
from pyk.prelude.kint import intToken, ltInt
from pyk.prelude.ml import mlEqualsFalse, mlEqualsTrue
from pyk.prelude.string import stringToken
from pyk.proof.reachability import APRBMCProof, APRProof
from pyk.proof.show import APRBMCProofNodePrinter, APRProofNodePrinter

if TYPE_CHECKING:
    from collections.abc import Iterable
    from pathlib import Path
    from typing import Final

    from pyk.kast import KInner
    from pyk.kast.outer import KFlatModule
    from pyk.kcfg import KCFG
    from pyk.ktool.kprint import SymbolTable
    from pyk.utils import BugReport

_LOGGER: Final = logging.getLogger(__name__)


# KEVM class


class KEVMSemantics(KCFGSemantics):
    auto_abstract_gas: bool

    def __init__(self, auto_abstract_gas: bool = False) -> None:
        self.auto_abstract_gas = auto_abstract_gas

    def is_terminal(self, cterm: CTerm) -> bool:
        k_cell = cterm.cell('K_CELL')
        # <k> #halt </k>
        if k_cell == KEVM.halt():
            return True
        elif type(k_cell) is KSequence:
            # <k> . </k>
            if k_cell.arity == 0:
                return True
            # <k> #halt </k>
            elif k_cell.arity == 1 and k_cell[0] == KEVM.halt():
                return True
            # <k> #halt ~> X:K </k>
            elif k_cell.arity == 2 and k_cell[0] == KEVM.halt() and type(k_cell[1]) is KVariable:
                return True
        return False

    def same_loop(self, cterm1: CTerm, cterm2: CTerm) -> bool:
        # In the same program, at the same calldepth, at the same program counter
        for cell in ['PC_CELL', 'CALLDEPTH_CELL', 'PROGRAM_CELL']:
            if cterm1.cell(cell) != cterm2.cell(cell):
                return False
        # duplicate from KEVM.extract_branches
        jumpi_pattern = KEVM.jumpi_applied(KVariable('###PCOUNT'), KVariable('###COND'))
        pc_next_pattern = KApply('#pc[_]_EVM_InternalOp_OpCode', [KEVM.jumpi()])
        branch_pattern = KSequence([jumpi_pattern, pc_next_pattern, KEVM.sharp_execute(), KVariable('###CONTINUATION')])
        subst1 = branch_pattern.match(cterm1.cell('K_CELL'))
        subst2 = branch_pattern.match(cterm2.cell('K_CELL'))
        # Jumping to the same program counter
        if subst1 is not None and subst2 is not None and subst1['###PCOUNT'] == subst2['###PCOUNT']:
            # Same wordstack structure
            if KEVM.wordstack_len(cterm1.cell('WORDSTACK_CELL')) == KEVM.wordstack_len(cterm2.cell('WORDSTACK_CELL')):
                return True
        return False

    def extract_branches(self, cterm: CTerm) -> list[KInner]:
        k_cell = cterm.cell('K_CELL')
        jumpi_pattern = KEVM.jumpi_applied(KVariable('###PCOUNT'), KVariable('###COND'))
        pc_next_pattern = KApply('#pc[_]_EVM_InternalOp_OpCode', [KEVM.jumpi()])
        branch_pattern = KSequence([jumpi_pattern, pc_next_pattern, KEVM.sharp_execute(), KVariable('###CONTINUATION')])
        if subst := branch_pattern.match(k_cell):
            cond = subst['###COND']
            if cond_subst := KEVM.bool_2_word(KVariable('###BOOL_2_WORD')).match(cond):
                cond = cond_subst['###BOOL_2_WORD']
            else:
                cond = KApply('_==Int_', [cond, intToken(0)])
            return [mlEqualsTrue(cond), mlEqualsTrue(KApply('notBool_', [cond]))]
        return []

    def abstract_node(self, cterm: CTerm) -> CTerm:
        if not self.auto_abstract_gas:
            return cterm

        def _replace(term: KInner) -> KInner:
            if type(term) is KApply and term.label.name == '<gas>':
                gas_term = term.args[0]
                if type(gas_term) is KApply and gas_term.label.name == 'infGas':
                    if type(gas_term.args[0]) is KVariable:
                        return term
                    return KApply(
                        '<gas>', KApply('infGas', abstract_term_safely(term, base_name='VGAS', sort=KSort('Int')))
                    )
                return term
            elif type(term) is KApply and term.label.name == '<refund>':
                if type(term.args[0]) is KVariable:
                    return term
                return KApply('<refund>', abstract_term_safely(term, base_name='VREFUND', sort=KSort('Int')))
            else:
                return term

        return CTerm(config=bottom_up(_replace, cterm.config), constraints=cterm.constraints)

    @staticmethod
    def cut_point_rules(
        break_on_jumpi: bool, break_on_calls: bool, break_on_storage: bool, break_on_basic_blocks: bool
    ) -> list[str]:
        cut_point_rules = []
        if break_on_jumpi:
            cut_point_rules.extend(['EVM.jumpi.true', 'EVM.jumpi.false'])
        if break_on_basic_blocks:
            cut_point_rules.append('EVM.end-basic-block')
        if break_on_calls or break_on_basic_blocks:
            cut_point_rules.extend(
                [
                    'EVM.call',
                    'EVM.callcode',
                    'EVM.delegatecall',
                    'EVM.staticcall',
                    'EVM.create',
                    'EVM.create2',
                    'EVM.end',
                    'EVM.return.exception',
                    'EVM.return.revert',
                    'EVM.return.success',
                ]
            )
        if break_on_storage:
            cut_point_rules.extend(['EVM.sstore', 'EVM.sload'])
        return cut_point_rules

    @staticmethod
    def terminal_rules(break_every_step: bool) -> list[str]:
        terminal_rules = ['EVM.halt']
        if break_every_step:
            terminal_rules.append('EVM.step')
        return terminal_rules


class KEVM(KProve, KRun):
    def __init__(
        self,
        definition_dir: Path,
        main_file: Path | None = None,
        use_directory: Path | None = None,
        kprove_command: str = 'kprove',
        krun_command: str = 'krun',
        extra_unparsing_modules: Iterable[KFlatModule] = (),
        bug_report: BugReport | None = None,
    ) -> None:
        # I'm going for the simplest version here, we can change later if there is an advantage.
        # https://stackoverflow.com/questions/9575409/calling-parent-class-init-with-multiple-inheritance-whats-the-right-way
        # Note that they say using `super` supports dependency injection, but I have never liked dependency injection anyway.
        KProve.__init__(
            self,
            definition_dir,
            use_directory=use_directory,
            main_file=main_file,
            command=kprove_command,
            extra_unparsing_modules=extra_unparsing_modules,
            bug_report=bug_report,
            patch_symbol_table=KEVM._kevm_patch_symbol_table,
        )
        KRun.__init__(
            self,
            definition_dir,
            use_directory=use_directory,
            command=krun_command,
            extra_unparsing_modules=extra_unparsing_modules,
            bug_report=bug_report,
            patch_symbol_table=KEVM._kevm_patch_symbol_table,
        )

    @classmethod
    def _kevm_patch_symbol_table(cls, symbol_table: SymbolTable) -> None:
        # fmt: off
        symbol_table['#Bottom']                                       = lambda: '#Bottom'
        symbol_table['_Map_']                                         = paren(lambda m1, m2: m1 + '\n' + m2)
        symbol_table['_AccountCellMap_']                              = paren(lambda a1, a2: a1 + '\n' + a2)
        symbol_table['.AccountCellMap']                               = lambda: '.Bag'
        symbol_table['AccountCellMapItem']                            = lambda k, v: v
        symbol_table['_<Word__EVM-TYPES_Int_Int_Int']                 = paren(lambda a1, a2: '(' + a1 + ') <Word ('  + a2 + ')')
        symbol_table['_>Word__EVM-TYPES_Int_Int_Int']                 = paren(lambda a1, a2: '(' + a1 + ') >Word ('  + a2 + ')')
        symbol_table['_<=Word__EVM-TYPES_Int_Int_Int']                = paren(lambda a1, a2: '(' + a1 + ') <=Word (' + a2 + ')')
        symbol_table['_>=Word__EVM-TYPES_Int_Int_Int']                = paren(lambda a1, a2: '(' + a1 + ') >=Word (' + a2 + ')')
        symbol_table['_==Word__EVM-TYPES_Int_Int_Int']                = paren(lambda a1, a2: '(' + a1 + ') ==Word (' + a2 + ')')
        symbol_table['_s<Word__EVM-TYPES_Int_Int_Int']                = paren(lambda a1, a2: '(' + a1 + ') s<Word (' + a2 + ')')
        paren_symbols = [
            '_|->_',
            '#And',
            '_andBool_',
            '#Implies',
            '_impliesBool_',
            '_&Int_',
            '_*Int_',
            '_+Int_',
            '_-Int_',
            '_/Int_',
            '_|Int_',
            '_modInt_',
            'notBool_',
            '#Or',
            '_orBool_',
            '_Set_',
            'typedArgs',
            '_up/Int__EVM-TYPES_Int_Int_Int',
            '_:__EVM-TYPES_WordStack_Int_WordStack',
        ]
        for symb in paren_symbols:
            if symb in symbol_table:
                symbol_table[symb] = paren(symbol_table[symb])
        # fmt: on

    class Sorts:
        KEVM_CELL: Final = KSort('KevmCell')

    def short_info(self, cterm: CTerm) -> list[str]:
        k_cell = cterm.try_cell('K_CELL')
        if k_cell is not None:
            pretty_cell = self.pretty_print(k_cell).replace('\n', ' ')
            if len(pretty_cell) > 80:
                pretty_cell = pretty_cell[0:80] + ' ...'
            k_str = f'k: {pretty_cell}'
            ret_strs = [k_str]
            for cell, name in [('PC_CELL', 'pc'), ('CALLDEPTH_CELL', 'callDepth'), ('STATUSCODE_CELL', 'statusCode')]:
                if cell in cterm.cells:
                    ret_strs.append(f'{name}: {self.pretty_print(cterm.cell(cell))}')
        else:
            ret_strs = ['(empty configuration)']
        return ret_strs

    @staticmethod
    def add_invariant(cterm: CTerm) -> CTerm:
        def _add_account_invariant(account: KApply) -> list[KApply]:
            _account_constraints = []
            acct_id, balance, nonce = account.args[0], account.args[1], account.args[5]

            if type(acct_id) is KApply and type(acct_id.args[0]) is KVariable:
                _account_constraints.append(mlEqualsTrue(KEVM.range_address(acct_id.args[0])))
                _account_constraints.append(
                    mlEqualsFalse(KEVM.is_precompiled_account(acct_id.args[0], cterm.cell('SCHEDULE_CELL')))
                )
            if type(balance) is KApply and type(balance.args[0]) is KVariable:
                _account_constraints.append(mlEqualsTrue(KEVM.range_uint(256, balance.args[0])))
            if type(nonce) is KApply and type(nonce.args[0]) is KVariable:
                _account_constraints.append(mlEqualsTrue(KEVM.range_nonce(nonce.args[0])))
            return _account_constraints

        constraints = []
        word_stack = cterm.cell('WORDSTACK_CELL')
        if type(word_stack) is not KVariable:
            word_stack_items = flatten_label('_:__EVM-TYPES_WordStack_Int_WordStack', word_stack)
            for i in word_stack_items[:-1]:
                constraints.append(mlEqualsTrue(KEVM.range_uint(256, i)))

        accounts_cell = cterm.cell('ACCOUNTS_CELL')
        if type(accounts_cell) is not KApply('.AccountCellMap'):
            accounts = flatten_label('_AccountCellMap_', cterm.cell('ACCOUNTS_CELL'))
            for wrapped_account in accounts:
                if not (type(wrapped_account) is KApply and wrapped_account.label.name == 'AccountCellMapItem'):
                    continue

                account = wrapped_account.args[1]
                if type(account) is KApply:
                    constraints.extend(_add_account_invariant(account))

        constraints.append(mlEqualsTrue(KEVM.range_address(cterm.cell('ID_CELL'))))
        constraints.append(mlEqualsTrue(KEVM.range_address(cterm.cell('CALLER_CELL'))))
        constraints.append(mlEqualsTrue(KEVM.range_address(cterm.cell('ORIGIN_CELL'))))
        constraints.append(mlEqualsTrue(ltInt(KEVM.size_bytes(cterm.cell('CALLDATA_CELL')), KEVM.pow128())))

        constraints.append(mlEqualsTrue(KEVM.range_blocknum(cterm.cell('NUMBER_CELL'))))

        for c in constraints:
            cterm = cterm.add_constraint(c)
        return cterm

    @staticmethod
    def halt() -> KApply:
        return KApply('#halt_EVM_KItem')

    @staticmethod
    def sharp_execute() -> KApply:
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
    def pow128() -> KApply:
        return KApply('pow128_WORD_Int', [])

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
    def range_nonce(i: KInner) -> KApply:
        return KApply('#rangeNonce(_)_WORD_Bool_Int', [i])

    @staticmethod
    def range_blocknum(ba: KInner) -> KApply:
        return KApply('#rangeBlockNum(_)_WORD_Bool_Int', [ba])

    @staticmethod
    def bool_2_word(cond: KInner) -> KApply:
        return KApply('bool2Word(_)_EVM-TYPES_Int_Bool', [cond])

    @staticmethod
    def size_bytes(ba: KInner) -> KApply:
        return KApply('lengthBytes(_)_BYTES-HOOKED_Int_Bytes', [ba])

    @staticmethod
    def inf_gas(g: KInner) -> KApply:
        return KApply('infGas', [g])

    @staticmethod
    def compute_valid_jumpdests(p: KInner) -> KApply:
        return KApply('#computeValidJumpDests(_)_EVM_Set_Bytes', [p])

    @staticmethod
    def bin_runtime(c: KInner) -> KApply:
        return KApply('binRuntime', [c])

    @staticmethod
    def init_bytecode(c: KInner) -> KApply:
        return KApply('initBytecode', [c])

    @staticmethod
    def is_precompiled_account(i: KInner, s: KInner) -> KApply:
        return KApply('#isPrecompiledAccount(_,_)_EVM_Bool_Int_Schedule', [i, s])

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
    def abi_calldata(name: str, args: list[KInner]) -> KApply:
        return KApply('#abiCallData(_,_)_EVM-ABI_Bytes_String_TypedArgs', [stringToken(name), KEVM.typed_args(args)])

    @staticmethod
    def abi_symbolic_calldata(name: str, args: list[KInner]) -> KApply:
        # TODO(palina): hardcoded structured calldata with `BYTES_DATA` having SYMBOLIC LENGTH `BYTES_SIZE`,
        # and `bytes[]` having 10 elements, each (`BYTES_N`) 600 bytes long
        return KEVM.structured_symbolic_data_calldata(name, args)

    @staticmethod
    def structured_symbolic_data_calldata(name: str, args: list[KInner]) -> KApply:
        term_one = KApply(
            '_+Bytes__BYTES-HOOKED_Bytes_Bytes_Bytes',
            [
                KApply(
                    '#signatureCallData(_,_)_EVM-ABI_Bytes_String_TypedArgs', [stringToken(name), KEVM.typed_args(args)]
                ),
                KApply(
                    '_+Bytes__BYTES-HOOKED_Bytes_Bytes_Bytes',
                    [
                        KApply('#buf(_,_)_BUF-SYNTAX_Bytes_Int_Int', [intToken(32), intToken(224)]),
                        KApply(
                            '_+Bytes__BYTES-HOOKED_Bytes_Bytes_Bytes',
                            [
                                KApply(
                                    '#buf(_,_)_BUF-SYNTAX_Bytes_Int_Int',
                                    [intToken(32), KVariable('l2OutputIndex', 'Int')],
                                ),
                                KApply(
                                    '_+Bytes__BYTES-HOOKED_Bytes_Bytes_Bytes',
                                    [
                                        KApply(
                                            '#buf(_,_)_BUF-SYNTAX_Bytes_Int_Int',
                                            [intToken(32), KVariable('version', 'Int')],
                                        ),
                                        KApply(
                                            '_+Bytes__BYTES-HOOKED_Bytes_Bytes_Bytes',
                                            [
                                                KApply(
                                                    '#buf(_,_)_BUF-SYNTAX_Bytes_Int_Int',
                                                    [intToken(32), KVariable('stateRoot', 'Int')],
                                                ),
                                                KApply(
                                                    '_+Bytes__BYTES-HOOKED_Bytes_Bytes_Bytes',
                                                    [
                                                        KApply(
                                                            '#buf(_,_)_BUF-SYNTAX_Bytes_Int_Int',
                                                            [
                                                                intToken(32),
                                                                KVariable('messagePasserStorageRoot', 'Int'),
                                                            ],
                                                        ),
                                                        KApply(
                                                            '_+Bytes__BYTES-HOOKED_Bytes_Bytes_Bytes',
                                                            [
                                                                KApply(
                                                                    '#buf(_,_)_BUF-SYNTAX_Bytes_Int_Int',
                                                                    [
                                                                        intToken(32),
                                                                        KVariable('latestBlockhash', 'Int'),
                                                                    ],
                                                                ),
                                                                KApply(
                                                                    '_+Bytes__BYTES-HOOKED_Bytes_Bytes_Bytes',
                                                                    [
                                                                        # TODO(palina): rewrite to `448 + SIZE_BYTES`
                                                                        # KApply(
                                                                        #     '#buf(_,_)_BUF-SYNTAX_Bytes_Int_Int',
                                                                        #     [intToken(32), intToken(768)],
                                                                        # ),
                                                                        KApply(
                                                                            '#buf(_,_)_BUF-SYNTAX_Bytes_Int_Int',
                                                                            [
                                                                                intToken(32),
                                                                                KApply(
                                                                                    '_+Int_',
                                                                                    [
                                                                                        intToken(448),
                                                                                        KVariable('BYTES_SIZE', 'Int'),
                                                                                    ],
                                                                                ),
                                                                            ],
                                                                        ),
                                                                        KApply(
                                                                            '_+Bytes__BYTES-HOOKED_Bytes_Bytes_Bytes',
                                                                            [
                                                                                KApply(
                                                                                    '#buf(_,_)_BUF-SYNTAX_Bytes_Int_Int',
                                                                                    [
                                                                                        intToken(32),
                                                                                        KVariable('nonce', 'Int'),
                                                                                    ],
                                                                                ),
                                                                                KApply(
                                                                                    '_+Bytes__BYTES-HOOKED_Bytes_Bytes_Bytes',
                                                                                    [
                                                                                        KApply(
                                                                                            '#buf(_,_)_BUF-SYNTAX_Bytes_Int_Int',
                                                                                            [
                                                                                                intToken(32),
                                                                                                KVariable(
                                                                                                    'sender',
                                                                                                    'Int',
                                                                                                ),
                                                                                            ],
                                                                                        ),
                                                                                        KApply(
                                                                                            '_+Bytes__BYTES-HOOKED_Bytes_Bytes_Bytes',
                                                                                            [
                                                                                                KApply(
                                                                                                    '#buf(_,_)_BUF-SYNTAX_Bytes_Int_Int',
                                                                                                    [
                                                                                                        intToken(32),
                                                                                                        KVariable(
                                                                                                            'target',
                                                                                                            'Int',
                                                                                                        ),
                                                                                                    ],
                                                                                                ),
                                                                                                KApply(
                                                                                                    '_+Bytes__BYTES-HOOKED_Bytes_Bytes_Bytes',
                                                                                                    [
                                                                                                        KApply(
                                                                                                            '#buf(_,_)_BUF-SYNTAX_Bytes_Int_Int',
                                                                                                            [
                                                                                                                intToken(
                                                                                                                    32
                                                                                                                ),
                                                                                                                KVariable(
                                                                                                                    'value',
                                                                                                                    'Int',
                                                                                                                ),
                                                                                                            ],
                                                                                                        ),
                                                                                                        KApply(
                                                                                                            '_+Bytes__BYTES-HOOKED_Bytes_Bytes_Bytes',
                                                                                                            [
                                                                                                                KApply(
                                                                                                                    '#buf(_,_)_BUF-SYNTAX_Bytes_Int_Int',
                                                                                                                    [
                                                                                                                        intToken(
                                                                                                                            32
                                                                                                                        ),
                                                                                                                        KVariable(
                                                                                                                            'gasLimit',
                                                                                                                            'Int',
                                                                                                                        ),
                                                                                                                    ],
                                                                                                                ),
                                                                                                                KApply(
                                                                                                                    '_+Bytes__BYTES-HOOKED_Bytes_Bytes_Bytes',
                                                                                                                    [
                                                                                                                        KApply(
                                                                                                                            '#buf(_,_)_BUF-SYNTAX_Bytes_Int_Int',
                                                                                                                            [
                                                                                                                                intToken(
                                                                                                                                    32
                                                                                                                                ),
                                                                                                                                intToken(
                                                                                                                                    192
                                                                                                                                ),
                                                                                                                            ],
                                                                                                                        ),
                                                                                                                        KApply(
                                                                                                                            '_+Bytes__BYTES-HOOKED_Bytes_Bytes_Bytes',
                                                                                                                            [
                                                                                                                                KApply(
                                                                                                                                    '#buf(_,_)_BUF-SYNTAX_Bytes_Int_Int',
                                                                                                                                    [
                                                                                                                                        intToken(
                                                                                                                                            32
                                                                                                                                        ),
                                                                                                                                        KVariable(
                                                                                                                                            'BYTES_SIZE',
                                                                                                                                            'Int',
                                                                                                                                        ),
                                                                                                                                    ],
                                                                                                                                ),
                                                                                                                                KVariable(
                                                                                                                                    'BYTES_DATA',
                                                                                                                                    'Bytes',
                                                                                                                                ),
                                                                                                                            ],
                                                                                                                        ),
                                                                                                                    ],
                                                                                                                ),
                                                                                                            ],
                                                                                                        ),
                                                                                                    ],
                                                                                                ),
                                                                                            ],
                                                                                        ),
                                                                                    ],
                                                                                ),
                                                                            ],
                                                                        ),
                                                                    ],
                                                                ),
                                                            ],
                                                        ),
                                                    ],
                                                ),
                                            ],
                                        ),
                                    ],
                                ),
                            ],
                        ),
                    ],
                ),
            ],
        )

        term_two = KApply(
            '_+Bytes__BYTES-HOOKED_Bytes_Bytes_Bytes',
            [
                term_one,
                KApply(
                    '_+Bytes__BYTES-HOOKED_Bytes_Bytes_Bytes',
                    [
                        KApply('#buf(_,_)_BUF-SYNTAX_Bytes_Int_Int', [intToken(32), intToken(10)]),
                        KApply(
                            '_+Bytes__BYTES-HOOKED_Bytes_Bytes_Bytes',
                            [
                                KApply('#buf(_,_)_BUF-SYNTAX_Bytes_Int_Int', [intToken(32), intToken(320)]),
                                KApply(
                                    '_+Bytes__BYTES-HOOKED_Bytes_Bytes_Bytes',
                                    [
                                        KApply('#buf(_,_)_BUF-SYNTAX_Bytes_Int_Int', [intToken(32), intToken(960)]),
                                        KApply(
                                            '_+Bytes__BYTES-HOOKED_Bytes_Bytes_Bytes',
                                            [
                                                KApply(
                                                    '#buf(_,_)_BUF-SYNTAX_Bytes_Int_Int', [intToken(32), intToken(1600)]
                                                ),
                                                KApply(
                                                    '_+Bytes__BYTES-HOOKED_Bytes_Bytes_Bytes',
                                                    [
                                                        KApply(
                                                            '#buf(_,_)_BUF-SYNTAX_Bytes_Int_Int',
                                                            [intToken(32), intToken(2240)],
                                                        ),
                                                        KApply(
                                                            '_+Bytes__BYTES-HOOKED_Bytes_Bytes_Bytes',
                                                            [
                                                                KApply(
                                                                    '#buf(_,_)_BUF-SYNTAX_Bytes_Int_Int',
                                                                    [intToken(32), intToken(2880)],
                                                                ),
                                                                KApply(
                                                                    '_+Bytes__BYTES-HOOKED_Bytes_Bytes_Bytes',
                                                                    [
                                                                        KApply(
                                                                            '#buf(_,_)_BUF-SYNTAX_Bytes_Int_Int',
                                                                            [intToken(32), intToken(3520)],
                                                                        ),
                                                                        KApply(
                                                                            '_+Bytes__BYTES-HOOKED_Bytes_Bytes_Bytes',
                                                                            [
                                                                                KApply(
                                                                                    '#buf(_,_)_BUF-SYNTAX_Bytes_Int_Int',
                                                                                    [intToken(32), intToken(4160)],
                                                                                ),
                                                                                KApply(
                                                                                    '_+Bytes__BYTES-HOOKED_Bytes_Bytes_Bytes',
                                                                                    [
                                                                                        KApply(
                                                                                            '#buf(_,_)_BUF-SYNTAX_Bytes_Int_Int',
                                                                                            [
                                                                                                intToken(32),
                                                                                                intToken(4800),
                                                                                            ],
                                                                                        ),
                                                                                        KApply(
                                                                                            '_+Bytes__BYTES-HOOKED_Bytes_Bytes_Bytes',
                                                                                            [
                                                                                                KApply(
                                                                                                    '#buf(_,_)_BUF-SYNTAX_Bytes_Int_Int',
                                                                                                    [
                                                                                                        intToken(32),
                                                                                                        intToken(5440),
                                                                                                    ],
                                                                                                ),
                                                                                                KApply(
                                                                                                    '_+Bytes__BYTES-HOOKED_Bytes_Bytes_Bytes',
                                                                                                    [
                                                                                                        KApply(
                                                                                                            '#buf(_,_)_BUF-SYNTAX_Bytes_Int_Int',
                                                                                                            [
                                                                                                                intToken(
                                                                                                                    32
                                                                                                                ),
                                                                                                                intToken(
                                                                                                                    6080
                                                                                                                ),
                                                                                                            ],
                                                                                                        ),
                                                                                                        KApply(
                                                                                                            '#buf(_,_)_BUF-SYNTAX_Bytes_Int_Int',
                                                                                                            [
                                                                                                                intToken(
                                                                                                                    32
                                                                                                                ),
                                                                                                                intToken(
                                                                                                                    600
                                                                                                                ),
                                                                                                            ],
                                                                                                        ),
                                                                                                    ],
                                                                                                ),
                                                                                            ],
                                                                                        ),
                                                                                    ],
                                                                                ),
                                                                            ],
                                                                        ),
                                                                    ],
                                                                ),
                                                            ],
                                                        ),
                                                    ],
                                                ),
                                            ],
                                        ),
                                    ],
                                ),
                            ],
                        ),
                    ],
                ),
            ],
        )

        bytes_one = KApply(
            '_+Bytes__BYTES-HOOKED_Bytes_Bytes_Bytes',
            [
                KVariable('BYTES_1', 'Bytes'),
                KApply(
                    '_+Bytes__BYTES-HOOKED_Bytes_Bytes_Bytes',
                    [
                        KApply('#buf(_,_)_BUF-SYNTAX_Bytes_Int_Int', [intToken(8), intToken(0)]),
                        KApply('#buf(_,_)_BUF-SYNTAX_Bytes_Int_Int', [intToken(32), intToken(600)]),
                    ],
                ),
            ],
        )

        bytes_two = KApply(
            '_+Bytes__BYTES-HOOKED_Bytes_Bytes_Bytes',
            [
                bytes_one,
                KApply(
                    '_+Bytes__BYTES-HOOKED_Bytes_Bytes_Bytes',
                    [
                        KVariable('BYTES_2', 'Bytes'),
                        KApply(
                            '_+Bytes__BYTES-HOOKED_Bytes_Bytes_Bytes',
                            [
                                KApply('#buf(_,_)_BUF-SYNTAX_Bytes_Int_Int', [intToken(8), intToken(0)]),
                                KApply('#buf(_,_)_BUF-SYNTAX_Bytes_Int_Int', [intToken(32), intToken(600)]),
                            ],
                        ),
                    ],
                ),
            ],
        )

        bytes_three = KApply(
            '_+Bytes__BYTES-HOOKED_Bytes_Bytes_Bytes',
            [
                bytes_two,
                KApply(
                    '_+Bytes__BYTES-HOOKED_Bytes_Bytes_Bytes',
                    [
                        KVariable('BYTES_3', 'Bytes'),
                        KApply(
                            '_+Bytes__BYTES-HOOKED_Bytes_Bytes_Bytes',
                            [
                                KApply('#buf(_,_)_BUF-SYNTAX_Bytes_Int_Int', [intToken(8), intToken(0)]),
                                KApply('#buf(_,_)_BUF-SYNTAX_Bytes_Int_Int', [intToken(32), intToken(600)]),
                            ],
                        ),
                    ],
                ),
            ],
        )

        bytes_four = KApply(
            '_+Bytes__BYTES-HOOKED_Bytes_Bytes_Bytes',
            [
                bytes_three,
                KApply(
                    '_+Bytes__BYTES-HOOKED_Bytes_Bytes_Bytes',
                    [
                        KVariable('BYTES_4', 'Bytes'),
                        KApply(
                            '_+Bytes__BYTES-HOOKED_Bytes_Bytes_Bytes',
                            [
                                KApply('#buf(_,_)_BUF-SYNTAX_Bytes_Int_Int', [intToken(8), intToken(0)]),
                                KApply('#buf(_,_)_BUF-SYNTAX_Bytes_Int_Int', [intToken(32), intToken(600)]),
                            ],
                        ),
                    ],
                ),
            ],
        )

        bytes_five = KApply(
            '_+Bytes__BYTES-HOOKED_Bytes_Bytes_Bytes',
            [
                bytes_four,
                KApply(
                    '_+Bytes__BYTES-HOOKED_Bytes_Bytes_Bytes',
                    [
                        KVariable('BYTES_5', 'Bytes'),
                        KApply(
                            '_+Bytes__BYTES-HOOKED_Bytes_Bytes_Bytes',
                            [
                                KApply('#buf(_,_)_BUF-SYNTAX_Bytes_Int_Int', [intToken(8), intToken(0)]),
                                KApply('#buf(_,_)_BUF-SYNTAX_Bytes_Int_Int', [intToken(32), intToken(600)]),
                            ],
                        ),
                    ],
                ),
            ],
        )

        bytes_six = KApply(
            '_+Bytes__BYTES-HOOKED_Bytes_Bytes_Bytes',
            [
                bytes_five,
                KApply(
                    '_+Bytes__BYTES-HOOKED_Bytes_Bytes_Bytes',
                    [
                        KVariable('BYTES_6', 'Bytes'),
                        KApply(
                            '_+Bytes__BYTES-HOOKED_Bytes_Bytes_Bytes',
                            [
                                KApply('#buf(_,_)_BUF-SYNTAX_Bytes_Int_Int', [intToken(8), intToken(0)]),
                                KApply('#buf(_,_)_BUF-SYNTAX_Bytes_Int_Int', [intToken(32), intToken(600)]),
                            ],
                        ),
                    ],
                ),
            ],
        )

        bytes_seven = KApply(
            '_+Bytes__BYTES-HOOKED_Bytes_Bytes_Bytes',
            [
                bytes_six,
                KApply(
                    '_+Bytes__BYTES-HOOKED_Bytes_Bytes_Bytes',
                    [
                        KVariable('BYTES_7', 'Bytes'),
                        KApply(
                            '_+Bytes__BYTES-HOOKED_Bytes_Bytes_Bytes',
                            [
                                KApply('#buf(_,_)_BUF-SYNTAX_Bytes_Int_Int', [intToken(8), intToken(0)]),
                                KApply('#buf(_,_)_BUF-SYNTAX_Bytes_Int_Int', [intToken(32), intToken(600)]),
                            ],
                        ),
                    ],
                ),
            ],
        )

        bytes_eight = KApply(
            '_+Bytes__BYTES-HOOKED_Bytes_Bytes_Bytes',
            [
                bytes_seven,
                KApply(
                    '_+Bytes__BYTES-HOOKED_Bytes_Bytes_Bytes',
                    [
                        KVariable('BYTES_8', 'Bytes'),
                        KApply(
                            '_+Bytes__BYTES-HOOKED_Bytes_Bytes_Bytes',
                            [
                                KApply('#buf(_,_)_BUF-SYNTAX_Bytes_Int_Int', [intToken(8), intToken(0)]),
                                KApply('#buf(_,_)_BUF-SYNTAX_Bytes_Int_Int', [intToken(32), intToken(600)]),
                            ],
                        ),
                    ],
                ),
            ],
        )

        bytes_nine = KApply(
            '_+Bytes__BYTES-HOOKED_Bytes_Bytes_Bytes',
            [
                bytes_eight,
                KApply(
                    '_+Bytes__BYTES-HOOKED_Bytes_Bytes_Bytes',
                    [
                        KVariable('BYTES_9', 'Bytes'),
                        KApply(
                            '_+Bytes__BYTES-HOOKED_Bytes_Bytes_Bytes',
                            [
                                KApply('#buf(_,_)_BUF-SYNTAX_Bytes_Int_Int', [intToken(8), intToken(0)]),
                                KApply('#buf(_,_)_BUF-SYNTAX_Bytes_Int_Int', [intToken(32), intToken(600)]),
                            ],
                        ),
                    ],
                ),
            ],
        )

        bytes_all = KApply(
            '_+Bytes__BYTES-HOOKED_Bytes_Bytes_Bytes',
            [
                bytes_nine,
                KApply(
                    '_+Bytes__BYTES-HOOKED_Bytes_Bytes_Bytes',
                    [
                        KVariable('BYTES_10', 'Bytes'),
                        KApply('#buf(_,_)_BUF-SYNTAX_Bytes_Int_Int', [intToken(8), intToken(0)]),
                    ],
                ),
            ],
        )

        return KApply('_+Bytes__BYTES-HOOKED_Bytes_Bytes_Bytes', [term_two, bytes_all])

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
    def abi_tuple(values: list[KInner]) -> KApply:
        return KApply('abi_type_tuple', [KEVM.typed_args(values)])

    @staticmethod
    def abi_array(elem_type: KInner, length: KInner, elems: list[KInner]) -> KApply:
        return KApply('abi_type_array', [elem_type, length, KEVM.typed_args(elems)])

    @staticmethod
    def abi_dynamic_array(elem_type: KInner) -> KApply:
        return KApply('abi_type_dynamic_array', [elem_type])

    @staticmethod
    def abi_dynamic_bytes_array(elem_type: KInner) -> KApply:
        return KApply('abi_type_dynamic_bytes_array', [elem_type])

    @staticmethod
    def empty_typedargs() -> KApply:
        return KApply('.List{"_,__EVM-ABI_TypedArgs_TypedArg_TypedArgs"}_TypedArgs')

    @staticmethod
    def bytes_append(b1: KInner, b2: KInner) -> KApply:
        return KApply('_+Bytes__BYTES-HOOKED_Bytes_Bytes_Bytes', [b1, b2])

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
    def wordstack_len(wordstack: KInner) -> int:
        return len(flatten_label('_:__EVM-TYPES_WordStack_Int_WordStack', wordstack))

    @staticmethod
    def parse_bytestack(s: KInner) -> KApply:
        return KApply('#parseByteStack(_)_SERIALIZATION_Bytes_String', [s])

    @staticmethod
    def bytes_empty() -> KApply:
        return KApply('.Bytes_BYTES-HOOKED_Bytes')

    @staticmethod
    def intlist(ints: list[KInner]) -> KApply:
        res = KApply('.List{"___HASHED-LOCATIONS_IntList_Int_IntList"}_IntList')
        for i in reversed(ints):
            res = KApply('___HASHED-LOCATIONS_IntList_Int_IntList', [i, res])
        return res

    @staticmethod
    def typed_args(args: list[KInner]) -> KInner:
        res = KEVM.empty_typedargs()
        return build_cons(res, '_,__EVM-ABI_TypedArgs_TypedArg_TypedArgs', args)

    @staticmethod
    def accounts(accts: list[KInner]) -> KInner:
        wrapped_accounts: list[KInner] = []
        for acct in accts:
            if type(acct) is KApply and acct.label.name == '<account>':
                acct_id = acct.args[0]
                wrapped_accounts.append(KApply('AccountCellMapItem', [acct_id, acct]))
            else:
                wrapped_accounts.append(acct)
        return build_assoc(KApply('.AccountCellMap'), KLabel('_AccountCellMap_'), wrapped_accounts)

    def prove_legacy(
        self,
        spec_file: Path,
        includes: Iterable[Path] = (),
        bug_report: bool = False,
        spec_module: str | None = None,
        claim_labels: Iterable[str] | None = None,
        exclude_claim_labels: Iterable[str] = (),
        debug: bool = False,
        debugger: bool = False,
        max_depth: int | None = None,
        max_counterexamples: int | None = None,
        branching_allowed: int | None = None,
        haskell_backend_args: Iterable[str] = (),
    ) -> list[CTerm]:
        md_selector = 'k'
        args: list[str] = []
        haskell_args: list[str] = []
        if claim_labels:
            args += ['--claims', ','.join(claim_labels)]
        if exclude_claim_labels:
            args += ['--exclude', ','.join(exclude_claim_labels)]
        if debug:
            args.append('--debug')
        if debugger:
            args.append('--debugger')
        if branching_allowed:
            args += ['--branching-allowed', f'{branching_allowed}']
        if max_counterexamples:
            haskell_args += ['--max-counterexamples', f'{max_counterexamples}']
        if bug_report:
            haskell_args += ['--bug-report', f'kevm-bug-{spec_file.name.removesuffix("-spec.k")}']
        if haskell_backend_args:
            haskell_args += list(haskell_backend_args)

        final_state = self.prove(
            spec_file=spec_file,
            spec_module_name=spec_module,
            args=args,
            include_dirs=includes,
            md_selector=md_selector,
            haskell_args=haskell_args,
            depth=max_depth,
        )
        return final_state


class KEVMNodePrinter(NodePrinter):
    kevm: KEVM

    def __init__(self, kevm: KEVM):
        NodePrinter.__init__(self, kevm)
        self.kevm = kevm

    def print_node(self, kcfg: KCFG, node: KCFG.Node) -> list[str]:
        ret_strs = super().print_node(kcfg, node)
        ret_strs += self.kevm.short_info(node.cterm)
        return ret_strs


class KEVMAPRNodePrinter(KEVMNodePrinter, APRProofNodePrinter):
    def __init__(self, kevm: KEVM, proof: APRProof):
        KEVMNodePrinter.__init__(self, kevm)
        APRProofNodePrinter.__init__(self, proof, kevm)


class KEVMAPRBMCNodePrinter(KEVMNodePrinter, APRBMCProofNodePrinter):
    def __init__(self, kevm: KEVM, proof: APRBMCProof):
        KEVMNodePrinter.__init__(self, kevm)
        APRBMCProofNodePrinter.__init__(self, proof, kevm)


def kevm_node_printer(kevm: KEVM, proof: APRProof) -> NodePrinter:
    if type(proof) is APRBMCProof:
        return KEVMAPRBMCNodePrinter(kevm, proof)
    if type(proof) is APRProof:
        return KEVMAPRNodePrinter(kevm, proof)
    raise ValueError(f'Cannot build NodePrinter for proof type: {type(proof)}')
