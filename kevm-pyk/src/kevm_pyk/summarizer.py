from __future__ import annotations

import logging
import shutil
import time
import traceback
from multiprocessing import Pool
from pathlib import Path
from typing import TYPE_CHECKING, Final

from frozendict import frozendict
from pyk.cterm import CSubst, CTerm, CTermSymbolic, cterm_build_claim
from pyk.kast.inner import KApply, KSequence, KToken, KVariable, Subst
from pyk.kast.outer import KSort
from pyk.kcfg import KCFG, KCFGExplore
from pyk.kdist import kdist
from pyk.kore.rpc import KoreClient
from pyk.prelude.kint import addInt, euclidModInt, leInt
from pyk.prelude.ml import mlEquals, mlEqualsFalse, mlEqualsTrue, mlNot
from pyk.proof import APRProof
from pyk.proof.show import APRProofShow
from pyk.utils import ensure_dir_path

from kevm_pyk.kevm import KEVM, KEVMSemantics, kevm_node_printer
from kevm_pyk.utils import initialize_apr_proof, legacy_explore, run_prover

if TYPE_CHECKING:
    from collections.abc import Iterable

    from pyk.kast.inner import KInner
    from pyk.kcfg.kcfg import NodeIdLike

_LOGGER = logging.getLogger(__name__)


OPCODES: Final = frozendict(
    {
        'STOP': KApply('STOP_EVM_NullStackOp'),
        'ADD': KApply('ADD_EVM_BinStackOp'),
        'MUL': KApply('MUL_EVM_BinStackOp'),
        'SUB': KApply('SUB_EVM_BinStackOp'),
        'DIV': KApply('DIV_EVM_BinStackOp'),
        'SDIV': KApply('SDIV_EVM_BinStackOp'),
        'MOD': KApply('MOD_EVM_BinStackOp'),
        'SMOD': KApply('SMOD_EVM_BinStackOp'),
        'ADDMOD': KApply('ADDMOD_EVM_TernStackOp'),
        'MULMOD': KApply('MULMOD_EVM_TernStackOp'),
        'EXP': KApply('EXP_EVM_BinStackOp'),
        'SIGNEXTEND': KApply('SIGNEXTEND_EVM_BinStackOp'),
        'LT': KApply('LT_EVM_BinStackOp'),
        'GT': KApply('GT_EVM_BinStackOp'),
        'SLT': KApply('SLT_EVM_BinStackOp'),
        'SGT': KApply('SGT_EVM_BinStackOp'),
        'EQ': KApply('EQ_EVM_BinStackOp'),
        'ISZERO': KApply('ISZERO_EVM_UnStackOp'),
        'AND': KApply('AND_EVM_BinStackOp'),
        'EVMOR': KApply('EVMOR_EVM_BinStackOp'),
        'XOR': KApply('XOR_EVM_BinStackOp'),
        'NOT': KApply('NOT_EVM_UnStackOp'),
        'BYTE': KApply('BYTE_EVM_BinStackOp'),
        'SHL': KApply('SHL_EVM_BinStackOp'),
        'SHR': KApply('SHR_EVM_BinStackOp'),
        'SAR': KApply('SAR_EVM_BinStackOp'),
        'SHA3': KApply('SHA3_EVM_BinStackOp'),
        'ADDRESS': KApply('ADDRESS_EVM_NullStackOp'),
        'BALANCE': KApply('BALANCE_EVM_UnStackOp'),
        'ORIGIN': KApply('ORIGIN_EVM_NullStackOp'),
        'CALLER': KApply('CALLER_EVM_NullStackOp'),
        'CALLVALUE': KApply('CALLVALUE_EVM_NullStackOp'),
        'CALLDATALOAD': KApply('CALLDATALOAD_EVM_UnStackOp'),
        'CALLDATASIZE': KApply('CALLDATASIZE_EVM_NullStackOp'),
        'CALLDATACOPY': KApply('CALLDATACOPY_EVM_TernStackOp'),
        'CODESIZE': KApply('CODESIZE_EVM_NullStackOp'),
        'CODECOPY': KApply('CODECOPY_EVM_TernStackOp'),
        'GASPRICE': KApply('GASPRICE_EVM_NullStackOp'),
        'EXTCODESIZE': KApply('EXTCODESIZE_EVM_UnStackOp'),
        'EXTCODECOPY': KApply('EXTCODECOPY_EVM_QuadStackOp'),
        'RETURNDATASIZE': KApply('RETURNDATASIZE_EVM_NullStackOp'),
        'RETURNDATACOPY': KApply('RETURNDATACOPY_EVM_TernStackOp'),
        'EXTCODEHASH': KApply('EXTCODEHASH_EVM_UnStackOp'),
        'BLOCKHASH': KApply('BLOCKHASH_EVM_UnStackOp'),
        'COINBASE': KApply('COINBASE_EVM_NullStackOp'),
        'TIMESTAMP': KApply('TIMESTAMP_EVM_NullStackOp'),
        'NUMBER': KApply('NUMBER_EVM_NullStackOp'),
        'PREVRANDAO': KApply('PREVRANDAO_EVM_NullStackOp'),
        'DIFFICULTY': KApply('DIFFICULTY_EVM_NullStackOp'),
        'GASLIMIT': KApply('GASLIMIT_EVM_NullStackOp'),
        'CHAINID': KApply('CHAINID_EVM_NullStackOp'),
        'SELFBALANCE': KApply('SELFBALANCE_EVM_NullStackOp'),
        'BASEFEE': KApply('BASEFEE_EVM_NullStackOp'),
        'POP': KApply('POP_EVM_UnStackOp'),
        'MLOAD': KApply('MLOAD_EVM_UnStackOp'),
        'MSTORE': KApply('MSTORE_EVM_BinStackOp'),
        'MSTORE8': KApply('MSTORE8_EVM_BinStackOp'),
        'SLOAD': KApply('SLOAD_EVM_UnStackOp'),
        'SSTORE': KApply('SSTORE_EVM_BinStackOp'),
        'JUMP': KApply('JUMP_EVM_UnStackOp'),
        'JUMPI': KApply('JUMPI_EVM_BinStackOp'),
        'PC': KApply('PC_EVM_NullStackOp'),
        'MSIZE': KApply('MSIZE_EVM_NullStackOp'),
        'GAS': KApply('GAS_EVM_NullStackOp'),
        'JUMPDEST': KApply('JUMPDEST_EVM_NullStackOp'),
        'TLOAD': KApply('TLOAD_EVM_UnStackOp'),
        'TSTORE': KApply('TSTORE_EVM_BinStackOp'),
        'MCOPY': KApply('MCOPY_EVM_TernStackOp'),
        'PUSHZERO': KApply('PUSHZERO_EVM_PushOp'),
        'PUSH': KApply('PUSH', KVariable('N', KSort('Int'))),
        'DUP': KApply('DUP', KVariable('N', KSort('Int'))),
        'SWAP': KApply('SWAP', KVariable('N', KSort('Int'))),
        'LOG': KApply('LOG', KVariable('N', KSort('Int'))),
        'CREATE': KApply('CREATE_EVM_TernStackOp'),
        'CALL': KApply('CALL_EVM_CallOp'),
        'CALLCODE': KApply('CALLCODE_EVM_CallOp'),
        'RETURN': KApply('RETURN_EVM_BinStackOp'),
        'DELEGATECALL': KApply('DELEGATECALL_EVM_CallSixOp'),
        'CREATE2': KApply('CREATE2_EVM_QuadStackOp'),
        'STATICCALL': KApply('STATICCALL_EVM_CallSixOp'),
        'REVERT': KApply('REVERT_EVM_BinStackOp'),
        'INVALID': KApply('INVALID_EVM_InvalidOp'),
        'SELFDESTRUCT': KApply('SELFDESTRUCT_EVM_UnStackOp'),
        'UNDEFINED': KApply('UNDEFINED(_)_EVM_InvalidOp_Int', KVariable('W', KSort('Int'))),
        # OpCode Variable
        # 'ALL': KVariable('OP_CODE', KSort('OpCode'))
    }
)


OPCODES_SUMMARY_STATUS: Final = frozendict(
    {
        'STOP': 'PASSED, One rule? Several rules?',
        'ADD': 'PASSED, No underflow check in KCFG',
        'MUL': 'FAILED, No underflow check in KCFG',
        'SUB': 'PASSED, No underflow check in KCFG',
        'DIV': 'PASSED, No underflow check in KCFG',
        'SDIV': 'PASSED, No underflow check in KCFG',
        'MOD': 'PASSED, No underflow check in KCFG',
        'SMOD': 'PASSED, No underflow check in KCFG',
        'ADDMOD': 'PASSED, No underflow check in KCFG',
        'MULMOD': 'PASSED, No underflow check in KCFG',
        'EXP': 'PASSED, No underflow check in KCFG',
        'SIGNEXTEND': 'PASSED, No underflow check in KCFG',
        'LT': 'PASSED, No underflow check in KCFG',
        'GT': 'PASSED, No underflow check in KCFG',
        'SLT': 'PASSED, No underflow check in KCFG',
        'SGT': 'PASSED, No underflow check in KCFG',
        'EQ': 'PASSED, No underflow check in KCFG',
        'ISZERO': 'PASSED, No underflow check in KCFG',
        'AND': 'PASSED, No underflow check in KCFG',
        'EVMOR': 'PASSED, No underflow check in KCFG',
        'XOR': 'PASSED, No underflow check in KCFG',
        'NOT': 'PASSED, No underflow check in KCFG',
        'BYTE': 'PASSED, No underflow check in KCFG',
        'SHL': 'PASSED, No underflow check in KCFG',
        'SHR': 'PASSED, No underflow check in KCFG',
        'SAR': 'PASSED, No underflow check in KCFG',
        'SHA3': 'PASSED, No underflow check in KCFG',
        'ADDRESS': 'PASSED, No underflow check, no .Account',
        'BALANCE': 'PASSED, no underflow check, no gas usage',
        'ORIGIN': 'PASSED, no underflow check, no .Account in origin cell',
        'CALLER': 'PASSED, no underflow check, no gas usage',
        'CALLVALUE': 'FAILED, No underflow check in KCFG',
        'CALLDATALOAD': 'PASSED, No underflow check in KCFG',
        'CALLDATASIZE': 'PASSED, No underflow check in KCFG',
        'CALLDATACOPY': 'PASSED, No underflow check in KCFG',
        'CODESIZE': 'PASSED, No underflow check in KCFG',
        'CODECOPY': 'PASSED, No underflow check in KCFG',
        'GASPRICE': 'PASSED, No underflow check in KCFG',
        'EXTCODESIZE': 'FAILED, generate ndbranch, No underflow check, No gas usage',
        'EXTCODECOPY': 'FAILED, generate ndbranch, No underflow check, No gas usage',
        'RETURNDATASIZE': 'PASSED, No underflow check, No gas usage',
        'RETURNDATACOPY': 'PASSED, No underflow check in KCFG',
        'EXTCODEHASH': 'FAILED, generate ndbranch, No underflow check, No gas usage',
        'BLOCKHASH': 'PASSED, No underflow check in KCFG',
        'COINBASE': 'PASSED, No underflow check, No gas usage',
        'TIMESTAMP': 'PASSED, No underflow check in KCFG',
        'NUMBER': 'PASSED, No underflow check in KCFG',
        'PREVRANDAO': 'PASSED, No underflow check in KCFG',
        'DIFFICULTY': 'PASSED, No underflow check in KCFG',
        'GASLIMIT': 'PASSED, No underflow check in KCFG',
        'CHAINID': 'PASSED, No underflow check in KCFG',
        'SELFBALANCE': 'PASSED, No underflow check in KCFG',
        'BASEFEE': 'FAILED, No underflow check in KCFG',
        'POP': 'PASSED, No underflow check, no gas usage',
        'MLOAD': 'PASSED, No underflow check, no gas usage',
        'MSTORE': 'PASSED, No underflow check in KCFG',
        'MSTORE8': 'PASSED, No underflow check, no gas usage',
        'SLOAD': 'PASSED, No underflow check in KCFG',
        'SSTORE': 'PASSED, No underflow check in KCFG',
        'JUMP': 'FAILED, No underflow check, wierd ndbranch that looks like a split',
        'JUMPI': 'FAILED, No underflow check, no gas usage, weird ndbranch that looks like a split',
        'PC': 'PASSED, No underflow check in KCFG',
        'MSIZE': 'PASSED, No underflow check in KCFG, no gas usage',
        'GAS': 'PASSED, No underflow check in KCFG',
        'JUMPDEST': 'PASSED, No underflow check in KCFG',
        'TLOAD': 'PASSED, No underflow check, no gas usage',
        'TSTORE': 'PASSED, No underflow check, no gas usage, strange info about smt reason timeout',
        'MCOPY': 'PASSED, No underflow check in KCFG',
        'PUSHZERO': 'PASSED, No underflow check in KCFG',
        'PUSH': 'PASSED, No underflow check, no gas usage',
        'DUP': 'PASSED, No underflow check in KCFG',
        'SWAP': 'PASSED, No underflow check in KCFG',
        'LOG': 'PASSED, No underflow check, no gas usage',
        'CREATE': 'TODO, Proof crashed',
        'CALL': 'UNCHECKED',
        'CALLCODE': 'UNCHECKED',
        'RETURN': 'PASSED, no underflow check, no gas usage',
        'DELEGATECALL': 'UNCHECKED',
        'CREATE2': 'UNCHECKED',
        'STATICCALL': 'UNCHECKED',
        'REVERT': 'PASSED',
        'INVALID': 'PASSED',
        'SELFDESTRUCT': 'UNCHECKED',
        'UNDEFINED': 'PASSED',
        # 'ALL': 'TODICUSS, failed to summarize, the optimized rule applies one step to obtain the target, the failure process rules are applied to obtain the failure, we need to summarize these ndbranches and exclude these conditions from individual opcode spec',
    }
)


NOT_USEGAS_OPCODES: Final = frozenset(
    [
        'BALANCE',
        'EXTCODESIZE',
        'EXTCODECOPY',
        'CALLER',
        'RETURNDATASIZE',
        'EXTCODEHASH',
        'COINBASE',
        'SELFBALANCE',
        'POP',
        'MLOAD',
        'MSTORE8',
        'SLOAD',
        'SSTORE',
        'JUMP',
        'JUMPI',
        'MSIZE',
        'TLOAD',
        'TSTORE',
        'PUSH',
        'CREATE',
        'CALL',
    ]
)

ACCOUNT_QUERIES_OPCODES: Final = frozenset(
    [
        'BALANCE',
        'EXTCODESIZE',
        'EXTCODEHASH',
        'EXTCODECOPY',
    ]
)

ACCOUNT_STORAGE_OPCODES: Final = frozenset(
    [
        'SLOAD',
        'SSTORE',
        'TLOAD',
        'TSTORE',
    ]
)


def get_passed_opcodes() -> list[str]:
    passed_opcodes = []
    for opcode in OPCODES_SUMMARY_STATUS:
        if get_summary_status(opcode) == 'PASSED':
            passed_opcodes.append(opcode)
    return passed_opcodes


def get_summary_status(opcode: str) -> str:
    assert opcode in OPCODES_SUMMARY_STATUS
    return OPCODES_SUMMARY_STATUS[opcode].split(',')[0]


def get_todo_list() -> list[str]:
    todo_list = []
    _LOGGER.info(f'Number of opcodes: {len(OPCODES)}')
    for opcode in OPCODES:
        if get_summary_status(opcode) != 'PASSED':
            todo_list.append(opcode)
    _LOGGER.info(f'Number of passed opcodes: {len(OPCODES)-len(todo_list)}')
    _LOGGER.info(f'Number of todo opcodes: {len(todo_list)}')
    _LOGGER.info(f'Todo opcodes: {todo_list}')
    return todo_list


def stack_needed(opcode_id: str) -> int:
    """
    Return the stack size needed for the opcode, corresponding `#stackNeeded` in the semantics.
    """
    opcode = OPCODES[opcode_id].label.name
    if 'CallOp' in opcode:
        return 7
    elif 'CallSixOp' in opcode:
        return 6
    elif 'LOG' in opcode:
        return 2
    elif 'SWAP' in opcode:
        return 1
    elif 'QuadStackOp' in opcode:
        return 4
    elif 'TernStackOp' in opcode:
        return 3
    elif 'BinStackOp' in opcode:
        return 2
    elif 'UnStackOp' in opcode:
        return 1
    return 0


def accounts_cell(acct_id: str | KInner, exists: bool = True) -> tuple[KInner, KInner]:
    """Construct an account cell map with constraints.

    Args:
        acct_id: Account identifier, either as a string variable name or KInner term.
        exists: Flag indicating if this account should exist in the resulting cell map.

    Returns:
        tuple[KInner, KInner]:
        - First element is the account cell map containing either the account or a symbolic `AccountCellMap` without this account
        - Second element is a constraint ensuring the account ID isn't in the symbolic `AccountCellMap`

    Constructs an account cell with standard Ethereum account components including balance, code, storage, and nonce.
    Creates a constraint that the account ID must not exist in the
    base map variable (DotAccountVar).
    The exists flag determines if the account is included in the final cell map or just the base map variable.
    """
    if isinstance(acct_id, str):
        acct_id = KVariable(acct_id, KSort('Int'))

    account_cell = KEVM.account_cell(
        acct_id,
        KVariable('BALANCE_CELL', 'Int'),
        KVariable('CODE_CELL', 'AccountCode'),
        KVariable('STORAGE_CELL', 'Map'),
        KVariable('ORIG_STORAGE_CELL', 'Map'),
        KVariable('TRANSIENT_STORAGE_CELL', 'Map'),
        KVariable('NONCE_CELL', 'Int'),
    )

    dot_account_var = KVariable('DotAccountVar', 'AccountCellMap')
    constraint = mlEqualsFalse(KEVM.account_cell_in_keys(acct_id, dot_account_var))

    if exists:
        return KApply('_AccountCellMap_', [account_cell, dot_account_var]), constraint
    else:
        return KApply('_AccountCellMap_', [dot_account_var]), constraint


class KEVMSummarizer:
    """
    A class for summarizing the instructions of the KEVM.

    1. `build_spec` builds the proof to symbolically execute one abitrary opcode.
    2. `explore` runs the proof to get the KCFG.
    3. `summarize` minimizes the KCFG to get the summarized rules for opcodes.
    """

    _cterm_symbolic: CTermSymbolic
    kevm: KEVM
    proof_dir: Path
    save_directory: Path

    def __init__(self, proof_dir: Path, save_directory: Path) -> None:
        self.kevm = KEVM(kdist.get('evm-semantics.summary'))
        self.proof_dir = proof_dir
        self.save_directory = save_directory

    def build_stack_underflow_spec(self) -> APRProof | None:
        """Build the specification to symbolically execute abitrary instruction with stack underflow."""
        ...

    def show_proof(
        self,
        proof: APRProof,
        nodes: Iterable[NodeIdLike] = (),
        node_deltas: Iterable[tuple[NodeIdLike, NodeIdLike]] = (),
        to_module: bool = False,
        minimize: bool = True,
        sort_collections: bool = False,
        omit_cells: Iterable[str] = (),
    ) -> list[str]:
        node_printer = kevm_node_printer(self.kevm, proof)
        proof_show = APRProofShow(self.kevm, node_printer=node_printer)
        return proof_show.show(
            proof,
            nodes=nodes,
            node_deltas=node_deltas,
            to_module=to_module,
            minimize=minimize,
        )

    def _build_spec(
        self,
        opcode: KApply,
        stack_needed: int,
        init_map: dict[str, KInner] | None = None,
        init_constraints: list[KInner] | None = None,
        final_map: dict[str, KInner] | None = None,
        final_constraints: list[KInner] | None = None,
        id_str: str = '',
    ) -> APRProof:
        """Build a specification for symbolically executing an Ethereum opcode with configurable initial/final states.

        Args:
            opcode: The EVM opcode to execute as a KApply term.
            stack_needed: Number of stack elements required to prevent underflow.
            init_map: Optional initial state substitutions for symbolic execution.
            init_constraints: Optional initial state constraints.
            final_map: Optional final state substitutions to verify against.
            final_constraints: Optional final state constraints to verify.
            id_str: Optional identifier suffix for the specification.

        Returns:
            APRProof: A proof object containing the constructed specification for the opcode execution.
        """
        init_map = init_map or {}
        init_constraints = init_constraints or []
        final_map = final_map or {}
        final_constraints = final_constraints or []

        cterm = CTerm(self.kevm.definition.empty_config(KSort('GeneratedTopCell')))
        opcode_symbol = opcode.label.name.split('_')[0]

        # construct the initial substitution
        _init_subst: dict[str, KInner] = {}
        next_opcode = KEVM.next_opcode(opcode)
        _init_subst['K_CELL'] = KSequence([next_opcode, KVariable('K_CELL')])  # #next [ OPCODE ] ~> K_CELL
        _init_subst['WORDSTACK_CELL'] = KEVM.wordstack(stack_needed)  # W0 : W1 : ... : Wn for not underflow
        _init_subst['ID_CELL'] = KVariable('ID_CELL', KSort('Int'))  # ID_CELL should be Int for ADDRESS, LOG.
        # This is because #push doesn't handle `.Account`. And it's okay to be Int for other opcodes.
        _init_subst['CALLER_CELL'] = KVariable('CALLER_CELL', KSort('Int'))  # CALLER_CELL should be Int for CALLER.
        _init_subst['ORIGIN_CELL'] = KVariable('ORIGIN_CELL', KSort('Int'))  # ORIGIN_CELL should be Int for ORIGIN.
        _init_subst['GAS_CELL'] = KEVM.inf_gas(KVariable('GAS_CELL', 'Gas'))  # SLOAD & SSTORE must use infinite gas.
        _init_subst.update(init_map)
        init_subst = CSubst(Subst(_init_subst), init_constraints)

        # construct the final substitution
        _final_subst: dict[str, KInner] = {vname: KVariable('FINAL_' + vname) for vname in cterm.free_vars}
        _final_subst['K_CELL'] = KVariable('K_CELL')
        _final_subst.update(final_map)
        final_subst = CSubst(Subst(_final_subst), final_constraints)

        spec_id = f'{opcode_symbol}{id_str}_{stack_needed}_SPEC'
        kclaim = cterm_build_claim(spec_id, init_subst(cterm), final_subst(cterm))
        return APRProof.from_claim(self.kevm.definition, kclaim[0], {}, self.proof_dir)

    def build_spec(self, opcode_symbol: str) -> list[APRProof]:

        def _ws_size(s: int) -> KInner:
            return KEVM.size_wordstack(KEVM.wordstack(s))

        def _le(a: KInner, b: KInner) -> KInner:
            return mlEqualsTrue(leInt(a, b))

        need = stack_needed(opcode_symbol)
        opcode = OPCODES[opcode_symbol]

        if opcode_symbol in ['DUP', 'SWAP', 'LOG']:
            opcode = KApply(opcode.label.name, KVariable('N', KSort('Int')))

        # (opcode, init_subst, init_constraints, final_subst, final_constraints, id_str)
        specs: list[tuple[KApply, dict[str, KInner], list[KInner], dict[str, KInner], list[KInner], str]] = []
        init_subst: dict[str, KInner] = {}
        final_subst: dict[str, KInner] = {}

        if opcode_symbol == 'SSTORE':
            init_subst['STATIC_CELL'] = KToken('false', KSort('Bool'))

        if opcode_symbol in NOT_USEGAS_OPCODES:
            # TODO: Should allow infGas to calculate gas. Skip for now.
            init_subst['USEGAS_CELL'] = KToken('false', KSort('Bool'))

        if opcode_symbol in ACCOUNT_QUERIES_OPCODES:
            w0 = KVariable('W0', KSort('Int'))
            pow160 = KToken(str(pow(2, 160)), KSort('Int'))

            cell, constraint = accounts_cell(euclidModInt(w0, pow160), exists=False)
            init_subst['ACCOUNTS_CELL'] = cell
            # TODO: BALANCE doesn't need the above spec. Maybe a bug in the backend.
            specs.append((opcode, init_subst, [constraint], {}, [], '_OWISE'))

            cell, constraint = accounts_cell(euclidModInt(w0, pow160), exists=True)
            init_subst['ACCOUNTS_CELL'] = cell
            specs.append((opcode, init_subst, [constraint], {}, [], '_NORMAL'))
        elif opcode_symbol in ACCOUNT_STORAGE_OPCODES or opcode_symbol == 'SELFBALANCE':
            cell, constraint = accounts_cell('ID_CELL')
            init_subst['ACCOUNTS_CELL'] = cell
            specs.append((opcode, init_subst, [constraint], {}, [], ''))
        elif opcode_symbol == 'JUMP':
            final_subst['K_CELL'] = KSequence([KEVM.end_basic_block(), KVariable('K_CELL')])
            specs.append((opcode, init_subst, [], final_subst, [], ''))
        elif opcode_symbol == 'JUMPI':
            constraint = mlEquals(KVariable('W1', KSort('Int')), KToken('0', KSort('Int')), 'Int')
            specs.append((opcode, init_subst, [constraint], {}, [], '_FALSE'))

            constraint = mlNot(mlEquals(KVariable('W1', KSort('Int')), KToken('0', KSort('Int')), 'Int'))
            final_subst['K_CELL'] = KSequence([KEVM.end_basic_block(), KVariable('K_CELL')])
            specs.append((opcode, init_subst, [], final_subst, [], '_TRUE'))
        elif opcode_symbol == 'DUP':
            init_constraints: list[KInner] = [_le(KVariable('N', 'Int'), _ws_size(0))]
            init_constraints.append(_le(_ws_size(0), KToken('1023', 'Int')))
            specs.append((opcode, init_subst, init_constraints, final_subst, [], ''))
        elif opcode_symbol == 'SWAP':
            init_constraints = [_le(addInt(KVariable('N', 'Int'), KToken('1', 'Int')), _ws_size(1))]
            init_constraints.append(_le(_ws_size(1), KToken('1023', 'Int')))
            specs.append((opcode, init_subst, init_constraints, final_subst, [], ''))
        elif opcode_symbol == 'LOG':
            init_constraints = [_le(addInt(KVariable('N', 'Int'), KToken('2', 'Int')), _ws_size(2))]
            init_constraints.append(_le(KVariable('N', 'Int'), _ws_size(0)))
            init_constraints.append(_le(_ws_size(2), addInt(KVariable('N', 'Int'), KToken('1026', 'Int'))))
            init_subst['STATIC_CELL'] = KToken('false', KSort('Bool'))
            specs.append((opcode, init_subst, init_constraints, final_subst, [], ''))
        else:
            specs.append((opcode, init_subst, [], final_subst, [], ''))

        return [self._build_spec(spec[0], need, spec[1], spec[2], spec[3], spec[4], spec[5]) for spec in specs]

    def explore(self, proof: APRProof) -> bool:
        """
        Execute the specification to explore the KCFG for all possible instructions.
        """

        # Construct the KCFGExplore
        # Copy from kevm-pyk/src/kevm_pyk/__main__.py/exec_prove
        # TODO: Make this process as an independent function to reuse； best to be in pyk.

        def _init_and_run_proof(proof: APRProof) -> tuple[bool, list[str]]:
            with legacy_explore(
                self.kevm,
                kcfg_semantics=KEVMSemantics(allow_symbolic_program=True),
                id=proof.id,
                llvm_definition_dir=self.kevm.definition_dir / 'llvm-library',
                bug_report=None,
                kore_rpc_command=('kore-rpc-booster',),
                smt_timeout=None,
                smt_retry_limit=None,
                log_succ_rewrites=True,
                log_fail_rewrites=True,
                fallback_on=None,
                interim_simplification=25,
                no_post_exec_simplify=False,
                port=None,
                haskell_threads=8,
            ) as kcfg_explore:

                def create_kcfg_explore() -> KCFGExplore:
                    client = KoreClient(
                        'localhost',
                        kcfg_explore.cterm_symbolic._kore_client.port,
                        bug_report=None,
                        bug_report_id=None,
                        dispatch=None,
                    )
                    cterm_symbolic = CTermSymbolic(
                        client,
                        self.kevm.definition,
                        log_succ_rewrites=True,
                        log_fail_rewrites=True,
                    )
                    return KCFGExplore(
                        cterm_symbolic,
                        kcfg_semantics=KEVMSemantics(allow_symbolic_program=True),
                        id=proof.id,
                    )

                initialize_apr_proof(kcfg_explore.cterm_symbolic, proof)
                proof.write_proof_data()

                start_time = time.time()
                passed = run_prover(
                    proof,
                    create_kcfg_explore=create_kcfg_explore,
                    max_depth=1,
                    max_iterations=300,
                    cut_point_rules=KEVMSemantics.cut_point_rules(
                        break_on_jumpi=False,
                        break_on_jump=False,
                        break_on_calls=False,
                        break_on_storage=False,
                        break_on_basic_blocks=False,
                        break_on_load_program=False,
                    ),
                    terminal_rules=KEVMSemantics.terminal_rules(True),
                    fail_fast=False,
                    fast_check_subsumption=False,
                    direct_subproof_rules=False,
                    max_frontier_parallel=8,
                    force_sequential=False,
                    assume_defined=False,
                    optimize_kcfg=False,
                )
            end_time = time.time()
            print(f'Proof timing {proof.id}: {end_time - start_time}s')

            res_lines = self.show_proof(
                proof,
                nodes=[node.id for node in proof.kcfg.nodes],
            )

            return passed, res_lines

        passed, res_lines = _init_and_run_proof(proof)

        ensure_dir_path(self.save_directory / proof.id)
        with open(self.save_directory / proof.id / 'proof-result.txt', 'w') as f:
            f.write(f'Proof {proof.id} Passed' if passed else f'Proof {proof.id} Failed')
            f.write('\n')
            for line in res_lines:
                f.write(line)
                f.write('\n')
        return passed

    def summarize(self, proof: APRProof, merge: bool = False) -> None:
        # TODO: may need customized way to generate summary rules, e.g., replacing infinite gas with finite gas.
        proof.minimize_kcfg(KEVMSemantics(allow_symbolic_program=True), merge)
        ensure_dir_path(self.save_directory / proof.id)
        with open(self.save_directory / proof.id / 'summary.md', 'w') as f:
            _LOGGER.info(f'Writing summary to {self.save_directory / proof.id / "summary.md"}')
            for res_line in self.show_proof(proof, to_module=True):
                f.write(res_line)
                f.write('\n')

    def print_node(self, proof: APRProof, nodes: Iterable[int]) -> None:
        with open(self.proof_dir / proof.id / 'node-print.md', 'w') as f:
            for res_line in self.show_proof(proof, nodes=nodes, to_module=False, minimize=False):
                f.write(res_line)
                f.write('\n')

    def analyze_proof(self, proof_id: str, node_id: int) -> None:
        proof = APRProof.read_proof_data(self.proof_dir, proof_id)
        self.summarize(proof)
        for successor in proof.kcfg.successors(node_id):
            print('Type: ', type(successor))
            print('Source: ', successor.source.id)
            if isinstance(successor, KCFG.Edge) or isinstance(successor, KCFG.NDBranch):
                print('Rules: ', successor.rules)
            print('Target: ', [target.id for target in successor.targets])


def _process_opcode(opcode: str) -> None:
    try:
        summarize(opcode)
        _LOGGER.info(f'Successfully processed opcode: {opcode}')
    except Exception as e:
        _LOGGER.error(f'Failed to process opcode {opcode}: {str(e)}')
        _LOGGER.debug(traceback.format_exc())


def batch_summarize(num_processes: int = 4) -> None:
    """
    Parallelize the summarization of opcodes using multiple processes.

    Args:
        num_processes: Number of parallel processes to use. Defaults to 4.
    """

    opcodes_to_process = OPCODES.keys()
    passed_opcodes = get_passed_opcodes()
    unpassed_opcodes = [opcode for opcode in opcodes_to_process if opcode not in passed_opcodes]
    has_call_opcodes = [opcode for opcode in unpassed_opcodes if 'Call' in OPCODES[opcode].label.name]
    no_call_opcodes = [opcode for opcode in unpassed_opcodes if 'Call' not in OPCODES[opcode].label.name]

    _LOGGER.info(f'Starting batch summarization of {len(unpassed_opcodes)} opcodes with {num_processes} processes')

    with Pool(processes=num_processes) as pool:
        _LOGGER.info(f'Summarizing {len(no_call_opcodes)} opcodes without CALL')
        pool.map(_process_opcode, no_call_opcodes)
        _LOGGER.info(f'Summarizing {len(has_call_opcodes)} opcodes with CALL')
        pool.map(_process_opcode, has_call_opcodes)

    _LOGGER.info('Batch summarization completed')


def summarize(opcode_symbol: str) -> tuple[KEVMSummarizer, list[APRProof]]:
    proof_dir = Path(__file__).parent / 'proofs'
    save_directory = Path(__file__).parent / 'summaries'
    summarizer = KEVMSummarizer(proof_dir, save_directory)
    proofs = summarizer.build_spec(opcode_symbol)
    for proof in proofs:
        summarizer.print_node(proof, [1])
        summarizer.explore(proof)
        summarizer.summarize(proof)
        proof.write_proof_data()
    return summarizer, proofs


def clear_proofs() -> None:
    proof_dir = Path(__file__).parent / 'proofs'
    if proof_dir.exists():
        shutil.rmtree(proof_dir)
