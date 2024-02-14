from __future__ import annotations

import logging
from contextlib import contextmanager
from pathlib import Path
from typing import TYPE_CHECKING

from pyk.cterm import CTerm
from pyk.kast.inner import KApply, KInner, KRewrite, KVariable, Subst
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
from pyk.kcfg import KCFGExplore
from pyk.kore.rpc import KoreClient, KoreExecLogFormat, TransportType, kore_server
from pyk.proof import APRProof, APRProver
from pyk.proof.equality import EqualityProof, ImpliesProver
from pyk.utils import single

if TYPE_CHECKING:
    from collections.abc import Callable, Collection, Iterable, Iterator
    from typing import Final, TypeVar

    from pyk.kast.outer import KClaim, KDefinition
    from pyk.kcfg import KCFG
    from pyk.kcfg.semantics import KCFGSemantics
    from pyk.kore.rpc import FallbackReason
    from pyk.ktool.kprint import KPrint
    from pyk.ktool.kprove import KProve
    from pyk.proof.proof import Proof
    from pyk.utils import BugReport

    T1 = TypeVar('T1')
    T2 = TypeVar('T2')

_LOGGER: Final = logging.getLogger(__name__)


def claim_dependency_dict(claims: Iterable[KClaim], spec_module_name: str | None = None) -> dict[str, list[str]]:
    claims_by_label = {claim.label: claim for claim in claims}
    graph: dict[str, list[str]] = {}
    for claim in claims:
        graph[claim.label] = []
        for dependency in claim.dependencies:
            if dependency not in claims_by_label:
                if spec_module_name is None:
                    raise ValueError(f'Could not find dependency and no spec_module provided: {dependency}')
                else:
                    spec_dependency = f'{spec_module_name}.{dependency}'
                    if spec_dependency not in claims_by_label:
                        raise ValueError(f'Could not find dependency: {dependency} or {spec_dependency}')
                    dependency = spec_dependency
            graph[claim.label].append(dependency)
    return graph


def get_apr_proof_for_spec(
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

    apr_proof = APRProof.read_proof_data(save_directory, claim.label)
    return apr_proof


def run_prover(
    proof: Proof,
    kcfg_explore: KCFGExplore,
    max_depth: int = 1000,
    max_iterations: int | None = None,
    cut_point_rules: Iterable[str] = (),
    terminal_rules: Iterable[str] = (),
    fail_fast: bool = False,
    counterexample_info: bool = False,
    always_check_subsumption: bool = False,
    fast_check_subsumption: bool = False,
) -> bool:
    prover: APRProver | ImpliesProver
    if type(proof) is APRProof:
        prover = APRProver(
            proof,
            kcfg_explore,
            counterexample_info=counterexample_info,
            always_check_subsumption=always_check_subsumption,
            fast_check_subsumption=fast_check_subsumption,
        )
    elif type(proof) is EqualityProof:
        prover = ImpliesProver(proof=proof, kcfg_explore=kcfg_explore)
    else:
        raise ValueError(f'Do not know how to build prover for proof: {proof}')

    try:
        if type(prover) is APRProver:
            prover.advance_proof(
                max_iterations=max_iterations,
                execute_depth=max_depth,
                terminal_rules=terminal_rules,
                cut_point_rules=cut_point_rules,
                fail_fast=fail_fast,
            )
        elif type(prover) is ImpliesProver:
            prover.advance_proof()

    except Exception as e:
        _LOGGER.error(f'Proof crashed: {proof.id}\n{e}', exc_info=True)
        return False

    _LOGGER.info(f'Proof status: {proof.status}')
    return proof.passed


def print_failure_info(proof: Proof, kcfg_explore: KCFGExplore, counterexample_info: bool = False) -> list[str]:
    if type(proof) is APRProof:
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

                node_cterm, _ = kcfg_explore.cterm_simplify(node.cterm)
                target_cterm, _ = kcfg_explore.cterm_simplify(target.cterm)

                res_lines.append('  Failure reason:')
                _, reason = kcfg_explore.implication_failure_reason(node_cterm, target_cterm)
                res_lines += [f'    {line}' for line in reason.split('\n')]

                res_lines.append('  Path condition:')
                res_lines += [f'    {kcfg_explore.kprint.pretty_print(proof.path_constraints(node.id))}']
                if counterexample_info:
                    res_lines.extend(print_model(node, kcfg_explore))

        res_lines.append('')
        res_lines.append(
            'Join the Runtime Verification Discord server for support: https://discord.com/invite/CurfmXNtbN'
        )

        return res_lines
    elif type(proof) is EqualityProof:
        return ['EqualityProof failed.']
    else:
        raise ValueError('Unknown proof type.')


def print_model(node: KCFG.Node, kcfg_explore: KCFGExplore) -> list[str]:
    res_lines: list[str] = []
    result_subst = kcfg_explore.cterm_get_model(node.cterm)
    if type(result_subst) is Subst:
        res_lines.append('  Model:')
        for var, term in result_subst.to_dict().items():
            term_kast = KInner.from_dict(term)
            res_lines.append(f'    {var} = {kcfg_explore.kprint.pretty_print(term_kast)}')
    else:
        res_lines.append('  Failed to generate a model.')

    return res_lines


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


@contextmanager
def legacy_explore(
    kprint: KPrint,
    *,
    kcfg_semantics: KCFGSemantics | None = None,
    id: str | None = None,
    port: int | None = None,
    kore_rpc_command: str | Iterable[str] | None = None,
    llvm_definition_dir: Path | None = None,
    smt_timeout: int | None = None,
    smt_retry_limit: int | None = None,
    smt_tactic: str | None = None,
    bug_report: BugReport | None = None,
    haskell_log_format: KoreExecLogFormat = KoreExecLogFormat.ONELINE,
    haskell_log_entries: Iterable[str] = (),
    log_axioms_file: Path | None = None,
    trace_rewrites: bool = False,
    start_server: bool = True,
    maude_port: int | None = None,
    fallback_on: Iterable[FallbackReason] | None = None,
    interim_simplification: int | None = None,
    no_post_exec_simplify: bool = False,
) -> Iterator[KCFGExplore]:
    if start_server:
        # Old way of handling KCFGExplore, to be removed
        with kore_server(
            definition_dir=kprint.definition_dir,
            llvm_definition_dir=llvm_definition_dir,
            module_name=kprint.main_module,
            port=port,
            command=kore_rpc_command,
            bug_report=bug_report,
            smt_timeout=smt_timeout,
            smt_retry_limit=smt_retry_limit,
            smt_tactic=smt_tactic,
            haskell_log_format=haskell_log_format,
            haskell_log_entries=haskell_log_entries,
            log_axioms_file=log_axioms_file,
            fallback_on=fallback_on,
            interim_simplification=interim_simplification,
            no_post_exec_simplify=no_post_exec_simplify,
        ) as server:
            with KoreClient('localhost', server.port, bug_report=bug_report, bug_report_id=id) as client:
                yield KCFGExplore(
                    kprint=kprint,
                    kore_client=client,
                    kcfg_semantics=kcfg_semantics,
                    id=id,
                    trace_rewrites=trace_rewrites,
                )
    else:
        if port is None:
            raise ValueError('Missing port with start_server=False')
        if maude_port is None:
            dispatch = None
        else:
            dispatch = {
                'execute': [('localhost', maude_port, TransportType.HTTP)],
                'simplify': [('localhost', maude_port, TransportType.HTTP)],
                'add-module': [
                    ('localhost', maude_port, TransportType.HTTP),
                    ('localhost', port, TransportType.SINGLE_SOCKET),
                ],
            }
        with KoreClient('localhost', port, bug_report=bug_report, bug_report_id=id, dispatch=dispatch) as client:
            yield KCFGExplore(
                kprint=kprint,
                kore_client=client,
                kcfg_semantics=kcfg_semantics,
                id=id,
                trace_rewrites=trace_rewrites,
            )
