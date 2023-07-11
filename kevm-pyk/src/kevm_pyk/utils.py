from __future__ import annotations

import logging
from pathlib import Path
from typing import TYPE_CHECKING

from pyk.cterm import CTerm
from pyk.kast.inner import KApply, KRewrite, KVariable, Subst
from pyk.kast.manip import (
    abstract_term_safely,
    bottom_up,
    free_vars,
    is_anon_var,
    set_cell,
    split_config_and_constraints,
    split_config_from,
)
from pyk.kast.outer import KSequence
from pyk.proof import APRBMCProof, APRBMCProver, APRProof, APRProver
from pyk.proof.equality import EqualityProof, EqualityProver
from pyk.proof.proof import ProofStatus
from pyk.utils import single

if TYPE_CHECKING:
    from collections.abc import Callable, Collection, Iterable
    from typing import Final, TypeVar

    from pyk.kast import KInner
    from pyk.kast.outer import KDefinition
    from pyk.kcfg import KCFGExplore
    from pyk.ktool.kprove import KProve
    from pyk.proof.proof import Proof
    from pyk.utils import BugReport

    T1 = TypeVar('T1')
    T2 = TypeVar('T2')

_LOGGER: Final = logging.getLogger(__name__)


def get_apr_proof_for_spec(  # noqa: N802
    kprove: KProve,
    spec_file: Path,
    save_directory: Path | None,
    spec_module_name: str | None = None,
    include_dirs: Iterable[Path] = (),
    md_selector: str | None = None,
    claim_labels: Iterable[str] | None = None,
    exclude_claim_labels: Iterable[str] = (),
) -> APRProof:
    if save_directory is None:
        save_directory = Path('.')
        _LOGGER.info(f'Using default save_directory: {save_directory}')

    _LOGGER.info(f'Extracting claim from file: {spec_file}')
    claim = single(
        kprove.get_claims(
            spec_file,
            spec_module_name=spec_module_name,
            include_dirs=include_dirs,
            md_selector=md_selector,
            claim_labels=claim_labels,
            exclude_claim_labels=exclude_claim_labels,
        )
    )

    apr_proof = APRProof.read_proof(claim.label, save_directory)
    return apr_proof


def kevm_prove(
    kprove: KProve,
    proof: Proof,
    kcfg_explore: KCFGExplore,
    save_directory: Path | None = None,
    max_depth: int = 1000,
    max_iterations: int | None = None,
    workers: int = 1,
    break_every_step: bool = False,
    break_on_jumpi: bool = False,
    break_on_calls: bool = True,
    implication_every_block: bool = False,
    is_terminal: Callable[[CTerm], bool] | None = None,
    extract_branches: Callable[[CTerm], Iterable[KInner]] | None = None,
    same_loop: Callable[[CTerm, CTerm], bool] | None = None,
    bmc_depth: int | None = None,
    bug_report: BugReport | None = None,
    kore_rpc_command: str | Iterable[str] = ('kore-rpc',),
    smt_timeout: int | None = None,
    smt_retry_limit: int | None = None,
    trace_rewrites: bool = False,
    abstract_node: Callable[[CTerm], CTerm] | None = None,
) -> bool:
    proof = proof
    terminal_rules = ['EVM.halt']
    cut_point_rules = []
    if break_every_step:
        cut_point_rules.append('EVM.step')
    if break_on_jumpi:
        cut_point_rules.extend(['EVM.jumpi.true', 'EVM.jumpi.false'])
    if break_on_calls:
        cut_point_rules.extend(
            [
                'EVM.call',
                'EVM.callcode',
                'EVM.delegatecall',
                'EVM.staticcall',
                'EVM.create',
                'EVM.create2',
                'FOUNDRY.foundry.call',
                'EVM.end',
                'EVM.return.exception',
                'EVM.return.revert',
                'EVM.return.success',
            ]
        )
    prover: APRBMCProver | APRProver | EqualityProver
    if type(proof) is APRBMCProof:
        assert same_loop, f'BMC proof requires same_loop heuristic, but {same_loop} was supplied'
        prover = APRBMCProver(
            proof,
            kcfg_explore,
            is_terminal=is_terminal,
            extract_branches=extract_branches,
            same_loop=same_loop,
            abstract_node=abstract_node,
        )
    elif type(proof) is APRProof:
        prover = APRProver(
            proof, kcfg_explore, is_terminal=is_terminal, extract_branches=extract_branches, abstract_node=abstract_node
        )
    elif type(proof) is EqualityProof:
        prover = EqualityProver(kcfg_explore=kcfg_explore, proof=proof)
    else:
        raise ValueError(f'Do not know how to build prover for proof: {proof}')
    try:
        if type(prover) is APRBMCProver or type(prover) is APRProver:
            prover.advance_proof(
                max_iterations=max_iterations,
                execute_depth=max_depth,
                terminal_rules=terminal_rules,
                cut_point_rules=cut_point_rules,
                implication_every_block=implication_every_block,
            )
            assert isinstance(proof, APRProof)
            failure_nodes = proof.failing
            if len(failure_nodes) == 0:
                _LOGGER.info(f'Proof passed: {proof.id}')
                return True
            else:
                _LOGGER.error(f'Proof failed: {proof.id}')
                return False
        elif type(prover) is EqualityProver:
            prover.advance_proof()
            if prover.proof.status == ProofStatus.PASSED:
                _LOGGER.info(f'Proof passed: {prover.proof.id}')
                return True
            if prover.proof.status == ProofStatus.FAILED:
                _LOGGER.error(f'Proof failed: {prover.proof.id}')
                if type(proof) is EqualityProof:
                    _LOGGER.info(proof.pretty(kprove))
                return False
            if prover.proof.status == ProofStatus.PENDING:
                _LOGGER.info(f'Proof pending: {prover.proof.id}')
                return False
        return False

    except Exception as e:
        _LOGGER.error(f'Proof crashed: {proof.id}\n{e}', exc_info=True)
        return False
    failure_nodes = proof.pending + proof.failing
    if len(failure_nodes) == 0:
        _LOGGER.info(f'Proof passed: {proof.id}')
        return True
    else:
        _LOGGER.error(f'Proof failed: {proof.id}')
        return False


def print_failure_info(proof: Proof, kcfg_explore: KCFGExplore) -> list[str]:
    if type(proof) is APRProof or type(proof) is APRBMCProof:
        target = proof.kcfg.node(proof.target)

        res_lines: list[str] = []

        num_pending = len(proof.pending)
        num_failing = len(proof.failing)
        res_lines.append(
            f'{num_pending + num_failing} Failure nodes. ({num_pending} pending and {num_failing} failing)'
        )
        if num_pending > 0:
            res_lines.append('')
            res_lines.append('Pending nodes:')
            for node in proof.pending:
                res_lines.append('')
                res_lines.append(f'ID: {node.id}:')
        if num_failing > 0:
            res_lines.append('')
            res_lines.append('Failing nodes:')
            for node in proof.failing:
                res_lines.append('')
                res_lines.append(f'  Node id: {str(node.id)}')

                simplified_node, _ = kcfg_explore.cterm_simplify(node.cterm)
                simplified_target, _ = kcfg_explore.cterm_simplify(target.cterm)

                node_cterm = CTerm.from_kast(simplified_node)
                target_cterm = CTerm.from_kast(simplified_target)

                res_lines.append('  Failure reason:')
                _, reason = kcfg_explore.implication_failure_reason(node_cterm, target_cterm)
                res_lines += [f'    {line}' for line in reason.split('\n')]

                res_lines.append('  Path condition:')
                res_lines += [f'    {kcfg_explore.kprint.pretty_print(proof.path_constraints(node.id))}']

                res_lines.append('')
                res_lines.append(
                    'Join the Runtime Verification Discord server for support: https://discord.gg/GHvFbRDD'
                )

        return res_lines
    elif type(proof) is EqualityProof:
        return ['EqualityProof failed.']
    else:
        raise ValueError('Unknown proof type.')


def arg_pair_of(
    fst_type: Callable[[str], T1], snd_type: Callable[[str], T2], delim: str = ','
) -> Callable[[str], tuple[T1, T2]]:
    def parse(s: str) -> tuple[T1, T2]:
        elems = s.split(delim)
        length = len(elems)
        if length != 2:
            raise ValueError(f'Expected 2 elements, found {length}')
        return fst_type(elems[0]), snd_type(elems[1])

    return parse


def byte_offset_to_lines(lines: Iterable[str], byte_start: int, byte_width: int) -> tuple[list[str], int, int]:
    text_lines = []
    line_start = 0
    for line in lines:
        if len(line) < byte_start:
            byte_start -= len(line) + 1
            line_start += 1
        else:
            break
    line_end = line_start
    for line in list(lines)[line_start:]:
        if byte_start + byte_width < 0:
            break
        else:
            text_lines.append(line)
            byte_width -= len(line) + 1
            line_end += 1
    return (text_lines, line_start, line_end)


def KDefinition__expand_macros(defn: KDefinition, term: KInner) -> KInner:  # noqa: N802
    def _expand_macros(_term: KInner) -> KInner:
        if type(_term) is KApply:
            prod = defn.production_for_klabel(_term.label)
            if 'macro' in prod.att or 'alias' in prod.att or 'macro-rec' in prod.att or 'alias-rec' in prod.att:
                for r in defn.macro_rules:
                    assert type(r.body) is KRewrite
                    _new_term = r.body.apply_top(_term)
                    if _new_term != _term:
                        _term = _new_term
                        break
        return _term

    old_term = None
    while term != old_term:
        old_term = term
        term = bottom_up(_expand_macros, term)

    return term


def abstract_cell_vars(cterm: KInner, keep_vars: Collection[KVariable] = ()) -> KInner:
    state, _ = split_config_and_constraints(cterm)
    config, subst = split_config_from(state)
    for s in subst:
        if type(subst[s]) is KVariable and not is_anon_var(subst[s]) and subst[s] not in keep_vars:
            subst[s] = abstract_term_safely(KVariable('_'), base_name=s)
    return Subst(subst)(config)


def ensure_ksequence_on_k_cell(cterm: CTerm) -> CTerm:
    k_cell = cterm.cell('K_CELL')
    if type(k_cell) is not KSequence:
        _LOGGER.info('Introducing artificial KSequence on <k> cell.')
        return CTerm.from_kast(set_cell(cterm.kast, 'K_CELL', KSequence([k_cell])))
    return cterm


def constraints_for(vars: list[str], constraints: Iterable[KInner]) -> Iterable[KInner]:
    accounts_constraints = []
    constraints_changed = True
    while constraints_changed:
        constraints_changed = False
        for constraint in constraints:
            if constraint not in accounts_constraints and any(v in vars for v in free_vars(constraint)):
                accounts_constraints.append(constraint)
                vars.extend(free_vars(constraint))
                constraints_changed = True
    return accounts_constraints
