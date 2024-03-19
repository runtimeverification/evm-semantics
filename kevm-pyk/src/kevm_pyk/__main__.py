from __future__ import annotations

import contextlib
import graphlib
import json
import logging
import os
import sys
import tempfile
import time
from argparse import ArgumentParser
from dataclasses import dataclass
from functools import cached_property
from pathlib import Path
from typing import TYPE_CHECKING

from pathos.pools import ProcessPool  # type: ignore
from pyk.cli.args import (
    BugReportOptions,
    KompileOptions,
    LoggingOptions,
    ParallelOptions,
    SaveDirOptions,
    SMTOptions,
    SpecOptions,
)
from pyk.cli.utils import file_path
from pyk.cterm import CTerm
from pyk.kast.outer import KApply, KRewrite, KSort, KToken
from pyk.kcfg import KCFG
from pyk.kdist import kdist
from pyk.kore.tools import PrintOutput, kore_print
from pyk.ktool.kompile import LLVMKompileType
from pyk.ktool.krun import KRunOutput
from pyk.prelude.ml import is_top, mlOr
from pyk.proof import APRProof
from pyk.proof.implies import EqualityProof
from pyk.proof.show import APRProofShow
from pyk.proof.tui import APRProofViewer
from pyk.utils import FrozenDict, hash_str, single

from . import VERSION, config
from .cli import (
    DisplayOptions,
    EVMChainOptions,
    ExploreOptions,
    KCFGShowOptions,
    KEVMCLIArgs,
    KOptions,
    KProveLegacyOptions,
    KProveOptions,
    RPCOptions,
    TargetOptions,
    node_id_like,
)
from .gst_to_kore import SORT_ETHEREUM_SIMULATION, gst_to_kore, kore_pgm_to_kore
from .kevm import KEVM, KEVMSemantics, kevm_node_printer
from .kompile import KompileTarget, kevm_kompile
from .utils import (
    arg_pair_of,
    claim_dependency_dict,
    ensure_ksequence_on_k_cell,
    get_apr_proof_for_spec,
    legacy_explore,
    print_failure_info,
    run_prover,
)

if TYPE_CHECKING:
    from argparse import Namespace
    from collections.abc import Callable, Iterator
    from typing import Any, Final, TypeVar

    from pyk.kast.outer import KClaim
    from pyk.kcfg.kcfg import NodeIdLike
    from pyk.kcfg.tui import KCFGElem
    from pyk.proof.proof import Proof

    T = TypeVar('T')

_LOGGER: Final = logging.getLogger(__name__)
_LOG_FORMAT: Final = '%(levelname)s %(asctime)s %(name)s - %(message)s'


def _ignore_arg(args: dict[str, Any], arg: str, cli_option: str) -> None:
    if arg in args:
        if args[arg] is not None:
            _LOGGER.warning(f'Ignoring command-line option: {cli_option}')
        args.pop(arg)


def main() -> None:
    sys.setrecursionlimit(15000000)
    parser = _create_argument_parser()
    args = parser.parse_args()
    logging.basicConfig(level=_loglevel(args), format=_LOG_FORMAT)

    executor_name = 'exec_' + args.command.lower().replace('-', '_')
    if executor_name not in globals():
        raise AssertionError(f'Unimplemented command: {args.command}')

    execute = globals()[executor_name]
    execute(**vars(args))


# Command implementation


class VersionOptions(LoggingOptions): ...


def exec_version(options: VersionOptions) -> None:
    print(f'KEVM Version: {VERSION}')


class KompileSpecOptions(LoggingOptions, KOptions, KompileOptions):
    main_file: Path
    target: KompileTarget
    output_dir: Path | None
    debug_build: bool

    @staticmethod
    def default() -> dict[str, Any]:
        return {
            'target': KompileTarget.HASKELL,
            'output_dir': None,
            'debug_build': False,
        }


def exec_kompile_spec(options: KompileSpecOptions) -> None:
    if options.target not in [KompileTarget.HASKELL, KompileTarget.MAUDE]:
        raise ValueError(f'Can only call kevm kompile-spec with --target [haskell,maude], got: {options.target.value}')

    output_dir = options.output_dir or Path()

    optimization = 0
    if options.o1:
        optimization = 1
    if options.o2:
        optimization = 2
    if options.o3:
        optimization = 3
    if options.debug_build:
        optimization = 0

    kevm_kompile(
        options.target,
        output_dir=output_dir,
        main_file=options.main_file,
        main_module=options.main_module,
        syntax_module=options.syntax_module,
        includes=options.includes,
        emit_json=options.emit_json,
        read_only=options.read_only,
        ccopts=options.ccopts,
        optimization=optimization,
        enable_llvm_debug=options.enable_llvm_debug,
        llvm_kompile_type=LLVMKompileType.C if options.llvm_library else LLVMKompileType.MAIN,
        debug_build=options.debug_build,
        debug=options.debug,
        verbose=options.verbose,
    )


class ProveLegacyOptions(LoggingOptions, KOptions, SpecOptions, KProveLegacyOptions):
    bug_report_legacy: bool

    @staticmethod
    def default() -> dict[str, Any]:
        return {
            'bug_report_legacy': False,
        }


def exec_prove_legacy(options: ProveLegacyOptions) -> None:
    definition_dir = options.definition_dir or kdist.get('evm-semantics.haskell')

    kevm = KEVM(definition_dir, use_directory=options.save_directory)

    include_dirs = [Path(include) for include in options.includes]
    include_dirs += config.INCLUDE_DIRS

    final_state = kevm.prove_legacy(
        spec_file=options.spec_file,
        includes=include_dirs,
        bug_report=options.bug_report_legacy,
        spec_module=options.spec_module,
        claim_labels=options.claim_labels,
        exclude_claim_labels=options.exclude_claim_labels,
        debug=options.debug,
        debugger=options.debugger,
        max_depth=options.max_depth,
        max_counterexamples=options.max_counterexamples,
        branching_allowed=options.branching_allowed,
        haskell_backend_args=options.haskell_backend_args,
    )
    final_kast = mlOr([state.kast for state in final_state])
    print(kevm.pretty_print(final_kast))
    if not is_top(final_kast):
        raise SystemExit(1)


class ZeroProcessPool:
    def map(self, f: Callable[[Any], Any], xs: list[Any]) -> list[Any]:
        return [f(x) for x in xs]


@contextlib.contextmanager
def wrap_process_pool(workers: int) -> Iterator[ZeroProcessPool | ProcessPool]:
    if workers <= 1:
        yield ZeroProcessPool()
    else:
        with ProcessPool(ncpus=workers) as pp:
            yield pp


class JSONEncoder(json.JSONEncoder):
    def default(self, obj: Any) -> Any:
        if isinstance(obj, FrozenDict):
            return json.JSONEncoder.encode(self, dict(obj))
        return json.JSONEncoder.default(self, obj)


@dataclass(frozen=True)
class KClaimJob:
    claim: KClaim
    dependencies: frozenset[KClaimJob]

    @cached_property
    def digest(self) -> str:
        deps_digest = ''.join([dep.digest for dep in self.dependencies])
        claim_hash = hash_str(json.dumps(self.claim.to_dict(), sort_keys=True, cls=JSONEncoder))
        return hash_str(f'{claim_hash}{deps_digest}')

    def up_to_date(self, digest_file: Path | None) -> bool:
        if not isinstance(digest_file, Path) or not digest_file.exists():
            return False
        digest_dict = json.loads(digest_file.read_text())
        if 'claims' not in digest_dict:
            digest_dict['claims'] = {}
            digest_file.write_text(json.dumps(digest_dict, indent=4))
        if self.claim.label not in digest_dict['claims']:
            return False
        return digest_dict['claims'][self.claim.label] == self.digest

    def update_digest(self, digest_file: Path | None) -> None:
        if digest_file is None:
            return
        digest_dict = {}
        if digest_file.exists():
            digest_dict = json.loads(digest_file.read_text())
        if 'claims' not in digest_dict:
            digest_dict['claims'] = {}
        digest_dict['claims'][self.claim.label] = self.digest
        digest_file.write_text(json.dumps(digest_dict, indent=4))

        _LOGGER.info(f'Updated claim {self.claim.label} in digest file: {digest_file}')


def init_claim_jobs(spec_module_name: str, claims: list[KClaim]) -> frozenset[KClaimJob]:
    labels_to_claims = {claim.label: claim for claim in claims}
    labels_to_claim_jobs: dict[str, KClaimJob] = {}

    def get_or_load_claim_job(claim_label: str) -> KClaimJob:
        if claim_label not in labels_to_claim_jobs:
            if claim_label in labels_to_claims:
                claim = labels_to_claims[claim_label]
            elif f'{spec_module_name}.{claim_label}' in labels_to_claims:
                claim = labels_to_claims[f'{spec_module_name}.{claim_label}']
            else:
                raise ValueError(f'Claim with label {claim_label} not found.')
            deps = frozenset({get_or_load_claim_job(dep_label) for dep_label in claim.dependencies})
            claim_job = KClaimJob(claim, deps)
            labels_to_claim_jobs[claim_label] = claim_job
        return labels_to_claim_jobs[claim_label]

    return frozenset({get_or_load_claim_job(claim.label) for claim in claims})


class ProveOptions(
    LoggingOptions,
    ParallelOptions,
    KOptions,
    RPCOptions,
    BugReportOptions,
    SMTOptions,
    ExploreOptions,
    SpecOptions,
    KProveOptions,
):
    reinit: bool

    @staticmethod
    def default() -> dict[str, Any]:
        return {
            'reinit': False,
        }


def exec_prove(options: ProveOptions) -> None:
    md_selector = 'k'

    save_directory = options.save_directory or Path(tempfile.mkdtemp())

    digest_file = save_directory / 'digest'

    definition_dir = options.definition_dir or kdist.get('evm-semantics.haskell')

    kevm = KEVM(definition_dir, use_directory=save_directory, bug_report=options.bug_report)

    include_dirs = [Path(include) for include in options.includes]
    include_dirs += config.INCLUDE_DIRS

    kore_rpc_command: tuple[str, ...]
    if options.kore_rpc_command is None:
        kore_rpc_command = ('kore-rpc-booster',) if options.use_booster else ('kore-rpc',)
    elif isinstance(options.kore_rpc_command, str):
        kore_rpc_command = tuple(options.kore_rpc_command.split())
    else:
        kore_rpc_command = options.kore_rpc_command

    def is_functional(claim: KClaim) -> bool:
        claim_lhs = claim.body
        if type(claim_lhs) is KRewrite:
            claim_lhs = claim_lhs.lhs
        return not (type(claim_lhs) is KApply and claim_lhs.label.name == '<generatedTop>')

    llvm_definition_dir = definition_dir / 'llvm-library' if options.use_booster else None

    _LOGGER.info(f'Extracting claims from file: {options.spec_file}')
    all_claims = kevm.get_claims(
        options.spec_file,
        spec_module_name=options.spec_module,
        include_dirs=include_dirs,
        md_selector=md_selector,
        claim_labels=options.claim_labels,
        exclude_claim_labels=options.exclude_claim_labels,
    )
    if all_claims is None:
        raise ValueError(f'No claims found in file: {options.spec_file}')
    spec_module_name = (
        options.spec_module if options.spec_module is not None else os.path.splitext(options.spec_file.name)[0].upper()
    )
    all_claim_jobs = init_claim_jobs(spec_module_name, all_claims)
    all_claim_jobs_by_label = {c.claim.label: c for c in all_claim_jobs}
    claims_graph = claim_dependency_dict(all_claims, spec_module_name=spec_module_name)

    def _init_and_run_proof(claim_job: KClaimJob) -> tuple[bool, list[str] | None]:
        claim = claim_job.claim
        up_to_date = claim_job.up_to_date(digest_file)
        if up_to_date:
            _LOGGER.info(f'Claim is up to date: {claim.label}')
        else:
            _LOGGER.info(f'Claim reinitialized because it is out of date: {claim.label}')
        claim_job.update_digest(digest_file)
        with legacy_explore(
            kevm,
            kcfg_semantics=KEVMSemantics(auto_abstract_gas=options.auto_abstract_gas),
            id=claim.label,
            llvm_definition_dir=llvm_definition_dir,
            bug_report=options.bug_report,
            kore_rpc_command=kore_rpc_command,
            smt_timeout=options.smt_timeout,
            smt_retry_limit=options.smt_retry_limit,
            trace_rewrites=options.trace_rewrites,
            fallback_on=options.fallback_on,
            interim_simplification=options.interim_simplification,
            no_post_exec_simplify=(not options.post_exec_simplify),
        ) as kcfg_explore:
            proof_problem: Proof
            if is_functional(claim):
                if not options.reinit and up_to_date and EqualityProof.proof_exists(claim.label, save_directory):
                    proof_problem = EqualityProof.read_proof_data(save_directory, claim.label)
                else:
                    proof_problem = EqualityProof.from_claim(claim, kevm.definition, proof_dir=save_directory)
            else:
                if not options.reinit and up_to_date and APRProof.proof_data_exists(claim.label, save_directory):
                    proof_problem = APRProof.read_proof_data(save_directory, claim.label)

                else:
                    _LOGGER.info(f'Converting claim to KCFG: {claim.label}')
                    kcfg, init_node_id, target_node_id = KCFG.from_claim(kevm.definition, claim)

                    new_init = ensure_ksequence_on_k_cell(kcfg.node(init_node_id).cterm)
                    new_target = ensure_ksequence_on_k_cell(kcfg.node(target_node_id).cterm)

                    _LOGGER.info(f'Computing definedness constraint for initial node: {claim.label}')
                    new_init = kcfg_explore.cterm_symbolic.assume_defined(new_init)

                    _LOGGER.info(f'Simplifying initial and target node: {claim.label}')
                    new_init, _ = kcfg_explore.cterm_symbolic.simplify(new_init)
                    new_target, _ = kcfg_explore.cterm_symbolic.simplify(new_target)
                    if CTerm._is_bottom(new_init.kast):
                        raise ValueError('Simplifying initial node led to #Bottom, are you sure your LHS is defined?')
                    if CTerm._is_top(new_target.kast):
                        raise ValueError('Simplifying target node led to #Bottom, are you sure your RHS is defined?')

                    kcfg.replace_node(init_node_id, new_init)
                    kcfg.replace_node(target_node_id, new_target)

                    proof_problem = APRProof(
                        claim.label,
                        kcfg,
                        [],
                        init_node_id,
                        target_node_id,
                        {},
                        proof_dir=save_directory,
                        subproof_ids=claims_graph[claim.label],
                        admitted=claim.is_trusted,
                    )

            if proof_problem.admitted:
                proof_problem.write_proof_data()
                _LOGGER.info(f'Skipping execution of proof because it is marked as admitted: {proof_problem.id}')
                return True, None

            start_time = time.time()
            passed = run_prover(
                proof_problem,
                kcfg_explore,
                max_depth=options.max_depth,
                max_iterations=options.max_iterations,
                cut_point_rules=KEVMSemantics.cut_point_rules(
                    options.break_on_jumpi,
                    options.break_on_calls,
                    options.break_on_storage,
                    options.break_on_basic_blocks,
                ),
                terminal_rules=KEVMSemantics.terminal_rules(options.break_every_step),
                fail_fast=options.fail_fast,
                always_check_subsumption=options.always_check_subsumption,
                fast_check_subsumption=options.fast_check_subsumption,
            )
            end_time = time.time()
            _LOGGER.info(f'Proof timing {proof_problem.id}: {end_time - start_time}s')
            failure_log = None
            if not passed:
                failure_log = print_failure_info(proof_problem, kcfg_explore)

            return passed, failure_log

    topological_sorter = graphlib.TopologicalSorter(claims_graph)
    topological_sorter.prepare()
    with wrap_process_pool(workers=options.workers) as process_pool:
        selected_results: list[tuple[bool, list[str] | None]] = []
        selected_claims = []
        while topological_sorter.is_active():
            ready = topological_sorter.get_ready()
            _LOGGER.info(f'Discharging proof obligations: {ready}')
            curr_claim_list = [all_claim_jobs_by_label[label] for label in ready]
            results: list[tuple[bool, list[str] | None]] = process_pool.map(_init_and_run_proof, curr_claim_list)
            for label in ready:
                topological_sorter.done(label)
            selected_results.extend(results)
            selected_claims.extend(curr_claim_list)

    failed = 0
    for job, r in zip(selected_claims, selected_results, strict=True):
        passed, failure_log = r
        if passed:
            print(f'PROOF PASSED: {job.claim.label}')
        else:
            failed += 1
            print(f'PROOF FAILED: {job.claim.label}')
            if options.failure_info and failure_log is not None:
                for line in failure_log:
                    print(line)

    if failed:
        sys.exit(failed)


class PruneOptions(LoggingOptions, KOptions, SpecOptions):
    node: NodeIdLike


def exec_prune(options: PruneOptions) -> None:
    md_selector = 'k'

    if options.save_directory is None:
        raise ValueError('Must pass --save-directory to prune!')

    if options.definition_dir is None:
        raise ValueError('Must pass --definition to prune!')

    kevm = KEVM(options.definition_dir, use_directory=options.save_directory)

    include_dirs = [Path(include) for include in options.includes]
    include_dirs += config.INCLUDE_DIRS

    _LOGGER.info(f'Extracting claims from file: {options.spec_file}')
    claim = single(
        kevm.get_claims(
            options.spec_file,
            spec_module_name=options.spec_module,
            include_dirs=include_dirs,
            md_selector=md_selector,
            claim_labels=options.claim_labels,
            exclude_claim_labels=options.exclude_claim_labels,
        )
    )

    apr_proof = APRProof.read_proof_data(options.save_directory, claim.label)
    node_ids = apr_proof.prune(options.node)
    _LOGGER.info(f'Pruned nodes: {node_ids}')
    apr_proof.write_proof_data()


class SectionEdgeOptions(
    LoggingOptions,
    KOptions,
    RPCOptions,
    SMTOptions,
    SpecOptions,
    BugReportOptions,
):
    edge: tuple[str, str]
    sections: int

    @staticmethod
    def default() -> dict[str, Any]:
        return {
            'sections': 2,
            'use_booster': False,
        }


def exec_section_edge(options: SectionEdgeOptions) -> None:
    md_selector = 'k'

    if options.save_directory is None:
        raise ValueError('Must pass --save-directory to section-edge!')

    if options.definition_dir is None:
        raise ValueError('Must pass --definition to section-edge!')

    kore_rpc_command: tuple[str, ...]
    if options.kore_rpc_command is None:
        kore_rpc_command = ('kore-rpc-booster',) if options.use_booster else ('kore-rpc',)
    elif isinstance(options.kore_rpc_command, str):
        kore_rpc_command = tuple(options.kore_rpc_command.split())
    else:
        kore_rpc_command = options.kore_rpc_command

    kevm = KEVM(options.definition_dir, use_directory=options.save_directory)
    llvm_definition_dir = options.definition_dir / 'llvm-library' if options.use_booster else None

    include_dirs = [Path(include) for include in options.includes]
    include_dirs += config.INCLUDE_DIRS

    claim = single(
        kevm.get_claims(
            options.spec_file,
            spec_module_name=options.spec_module,
            include_dirs=include_dirs,
            md_selector=md_selector,
            claim_labels=options.claim_labels,
            exclude_claim_labels=options.exclude_claim_labels,
        )
    )

    proof = APRProof.read_proof_data(options.save_directory, claim.label)
    source_id, target_id = options.edge
    with legacy_explore(
        kevm,
        kcfg_semantics=KEVMSemantics(),
        id=proof.id,
        bug_report=options.bug_report,
        kore_rpc_command=kore_rpc_command,
        smt_timeout=options.smt_timeout,
        smt_retry_limit=options.smt_retry_limit,
        trace_rewrites=options.trace_rewrites,
        llvm_definition_dir=llvm_definition_dir,
    ) as kcfg_explore:
        kcfg, _ = kcfg_explore.section_edge(
            proof.kcfg, source_id=int(source_id), target_id=int(target_id), logs=proof.logs, sections=options.sections
        )
    proof.write_proof_data()


class ShowKCFGOptions(
    LoggingOptions,
    KCFGShowOptions,
    KOptions,
    SpecOptions,
    DisplayOptions,
): ...


def exec_show_kcfg(options: ShowKCFGOptions) -> None:

    if options.definition_dir is None:
        raise ValueError('Must pass --definition to show-kcfg!')

    kevm = KEVM(options.definition_dir)
    include_dirs = [Path(include) for include in options.includes]
    include_dirs += config.INCLUDE_DIRS
    proof = get_apr_proof_for_spec(
        kevm,
        options.spec_file,
        save_directory=options.save_directory,
        spec_module_name=options.spec_module,
        include_dirs=include_dirs,
        md_selector=options.md_selector,
        claim_labels=options.claim_labels,
        exclude_claim_labels=options.exclude_claim_labels,
    )

    nodes = options.nodes

    if options.pending:
        nodes = list(nodes) + [node.id for node in proof.pending]
    if options.failing:
        nodes = list(nodes) + [node.id for node in proof.failing]

    node_printer = kevm_node_printer(kevm, proof)
    proof_show = APRProofShow(kevm, node_printer=node_printer)

    res_lines = proof_show.show(
        proof,
        nodes=nodes,
        node_deltas=options.node_deltas,
        to_module=options.to_module,
        minimize=options.minimize,
        sort_collections=options.sort_collections,
    )

    if options.failure_info:
        with legacy_explore(kevm, kcfg_semantics=KEVMSemantics(), id=proof.id) as kcfg_explore:
            res_lines += print_failure_info(proof, kcfg_explore)

    print('\n'.join(res_lines))


class ViewKCFGOptions(
    LoggingOptions,
    KOptions,
    SpecOptions,
): ...


def exec_view_kcfg(options: ViewKCFGOptions) -> None:

    if options.definition_dir is None:
        raise ValueError('Must pass --definition to view-kcfg!')

    kevm = KEVM(options.definition_dir)
    include_dirs = [Path(include) for include in options.includes]
    include_dirs += config.INCLUDE_DIRS
    proof = get_apr_proof_for_spec(
        kevm,
        options.spec_file,
        save_directory=options.save_directory,
        spec_module_name=options.spec_module,
        include_dirs=include_dirs,
        md_selector=options.md_selector,
        claim_labels=options.claim_labels,
        exclude_claim_labels=options.exclude_claim_labels,
    )

    node_printer = kevm_node_printer(kevm, proof)

    def custom_view(element: KCFGElem) -> list[str]:
        if type(element) is KCFG.Edge:
            return list(element.rules)
        if type(element) is KCFG.NDBranch:
            return list(element.rules)
        return []

    proof_view = APRProofViewer(proof, kevm, node_printer=node_printer, custom_view=custom_view)

    proof_view.run()


class RunOptions(
    LoggingOptions,
    KOptions,
    EVMChainOptions,
    TargetOptions,
    SaveDirOptions,
):
    input_file: Path
    output: KRunOutput
    expand_macros: bool
    debugger: bool

    @staticmethod
    def default() -> dict[str, Any]:
        return {
            'output': KRunOutput.PRETTY,
            'expand_macros': True,
            'debugger': False,
        }


def exec_run(options: RunOptions) -> None:
    target = options.target or 'llvm'

    target_fqn = f'evm-semantics.{target}'

    kevm = KEVM(kdist.get(target_fqn), use_directory=options.save_directory)

    try:
        json_read = json.loads(options.input_file.read_text())
        kore_pattern = gst_to_kore(json_read, options.schedule, options.mode, options.chainid, options.usegas)
    except json.JSONDecodeError:
        pgm_token = KToken(options.input_file.read_text(), KSort('EthereumSimulation'))
        kast_pgm = kevm.parse_token(pgm_token)
        kore_pgm = kevm.kast_to_kore(kast_pgm, sort=KSort('EthereumSimulation'))
        kore_pattern = kore_pgm_to_kore(
            kore_pgm, SORT_ETHEREUM_SIMULATION, options.schedule, options.mode, options.chainid, options.usegas
        )

    kevm.run(
        kore_pattern,
        depth=options.depth,
        term=True,
        expand_macros=options.expand_macros,
        output=options.output,
        check=True,
        debugger=options.debugger,
    )


class KastOptions(
    LoggingOptions,
    TargetOptions,
    EVMChainOptions,
    KOptions,
    SaveDirOptions,
):
    input_file: Path
    output: PrintOutput

    @staticmethod
    def default() -> dict[str, Any]:
        return {
            'output': PrintOutput.KORE,
        }


def exec_kast(options: KastOptions) -> None:
    target = options.target or 'llvm'

    target_fqn = f'evm-semantics.{target}'

    kevm = KEVM(kdist.get(target_fqn), use_directory=options.save_directory)

    try:
        json_read = json.loads(options.input_file.read_text())
        kore_pattern = gst_to_kore(json_read, options.schedule, options.mode, options.chainid, options.usegas)
    except json.JSONDecodeError:
        pgm_token = KToken(options.input_file.read_text(), KSort('EthereumSimulation'))
        kast_pgm = kevm.parse_token(pgm_token)
        kore_pgm = kevm.kast_to_kore(kast_pgm)
        kore_pattern = kore_pgm_to_kore(
            kore_pgm, SORT_ETHEREUM_SIMULATION, options.schedule, options.mode, options.chainid, options.usegas
        )

    output_text = kore_print(kore_pattern, definition_dir=kevm.definition_dir, output=options.output)
    print(output_text)


# Helpers


def _create_argument_parser() -> ArgumentParser:
    def list_of(elem_type: Callable[[str], T], delim: str = ';') -> Callable[[str], list[T]]:
        def parse(s: str) -> list[T]:
            return [elem_type(elem) for elem in s.split(delim)]

        return parse

    kevm_cli_args = KEVMCLIArgs()
    parser = ArgumentParser(prog='kevm-pyk')

    command_parser = parser.add_subparsers(dest='command', required=True)

    command_parser.add_parser('version', help='Print KEVM version and exit.', parents=[kevm_cli_args.logging_args])

    kevm_kompile_spec_args = command_parser.add_parser(
        'kompile-spec',
        help='Kompile KEVM specification.',
        parents=[kevm_cli_args.logging_args, kevm_cli_args.k_args, kevm_cli_args.kompile_args],
    )
    kevm_kompile_spec_args.add_argument('main_file', type=file_path, help='Path to file with main module.')
    kevm_kompile_spec_args.add_argument('--target', type=KompileTarget, help='[haskell|maude]')
    kevm_kompile_spec_args.add_argument(
        '-o', '--output-definition', type=Path, dest='output_dir', help='Path to write kompiled definition to.'
    )
    kevm_kompile_spec_args.add_argument(
        '--debug-build', dest='debug_build', default=None, help='Enable debug symbols in LLVM builds.'
    )

    prove_args = command_parser.add_parser(
        'prove',
        help='Run KEVM proof.',
        parents=[
            kevm_cli_args.logging_args,
            kevm_cli_args.parallel_args,
            kevm_cli_args.k_args,
            kevm_cli_args.kprove_args,
            kevm_cli_args.rpc_args,
            kevm_cli_args.bug_report_args,
            kevm_cli_args.smt_args,
            kevm_cli_args.explore_args,
            kevm_cli_args.spec_args,
        ],
    )
    prove_args.add_argument(
        '--reinit',
        dest='reinit',
        default=None,
        action='store_true',
        help='Reinitialize CFGs even if they already exist.',
    )

    prune_args = command_parser.add_parser(
        'prune',
        help='Remove a node and its successors from the proof state.',
        parents=[
            kevm_cli_args.logging_args,
            kevm_cli_args.k_args,
            kevm_cli_args.spec_args,
        ],
    )
    prune_args.add_argument('node', type=node_id_like, help='Node to remove CFG subgraph from.')

    section_edge_args = command_parser.add_parser(
        'section-edge',
        help='Break an edge into sections.',
        parents=[
            kevm_cli_args.logging_args,
            kevm_cli_args.k_args,
            kevm_cli_args.spec_args,
        ],
    )
    section_edge_args.add_argument('edge', type=arg_pair_of(str, str), help='Edge to section in CFG.')
    section_edge_args.add_argument(
        '--sections', type=int, help='Number of sections to make from edge (>= 2).'
    )
    section_edge_args.add_argument(
        '--use-booster',
        dest='use_booster',
        default=None,
        action='store_true',
        help="Use the booster RPC server instead of kore-rpc. Requires calling kompile with '--target haskell-booster' flag",
    )

    prove_legacy_args = command_parser.add_parser(
        'prove-legacy',
        help='Run KEVM proof using the legacy kprove binary.',
        parents=[
            kevm_cli_args.logging_args,
            kevm_cli_args.k_args,
            kevm_cli_args.spec_args,
            kevm_cli_args.kprove_legacy_args,
        ],
    )
    prove_legacy_args.add_argument(
        '--bug-report-legacy', default=None, action='store_true', help='Generate a legacy bug report.'
    )

    command_parser.add_parser(
        'view-kcfg',
        help='Explore a given proof in the KCFG visualizer.',
        parents=[kevm_cli_args.logging_args, kevm_cli_args.k_args, kevm_cli_args.spec_args],
    )

    command_parser.add_parser(
        'show-kcfg',
        help='Print the CFG for a given proof.',
        parents=[
            kevm_cli_args.logging_args,
            kevm_cli_args.k_args,
            kevm_cli_args.kcfg_show_args,
            kevm_cli_args.spec_args,
            kevm_cli_args.display_args,
        ],
    )

    run_args = command_parser.add_parser(
        'run',
        help='Run KEVM test/simulation.',
        parents=[
            kevm_cli_args.logging_args,
            kevm_cli_args.target_args,
            kevm_cli_args.evm_chain_args,
            kevm_cli_args.k_args,
        ],
    )
    run_args.add_argument('input_file', type=file_path, help='Path to input file.')
    run_args.add_argument(
        '--output',
        type=KRunOutput,
        choices=list(KRunOutput),
    )
    run_args.add_argument(
        '--expand-macros',
        dest='expand_macros',
        default=None,
        action='store_true',
        help='Expand macros on the input term before execution.',
    )
    run_args.add_argument(
        '--no-expand-macros',
        dest='expand_macros',
        action='store_false',
        help='Do not expand macros on the input term before execution.',
    )
    run_args.add_argument(
        '--debugger',
        dest='debugger',
        action='store_true',
        help='Run GDB debugger for execution.',
    )

    kast_args = command_parser.add_parser(
        'kast',
        help='Run KEVM program.',
        parents=[
            kevm_cli_args.logging_args,
            kevm_cli_args.target_args,
            kevm_cli_args.evm_chain_args,
            kevm_cli_args.k_args,
        ],
    )
    kast_args.add_argument('input_file', type=file_path, help='Path to input file.')
    kast_args.add_argument(
        '--output',
        type=PrintOutput,
        choices=list(PrintOutput),
    )

    return parser


def _loglevel(args: Namespace) -> int:
    if args.debug:
        return logging.DEBUG

    if args.verbose:
        return logging.INFO

    return logging.WARNING


if __name__ == '__main__':
    main()
