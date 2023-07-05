from __future__ import annotations

import json
import logging
import sys
from argparse import ArgumentParser
from pathlib import Path
from typing import TYPE_CHECKING

from pathos.pools import ProcessPool  # type: ignore
from pyk.cli.utils import file_path
from pyk.cterm import CTerm
from pyk.kast.outer import KApply, KRewrite
from pyk.kcfg import KCFG, KCFGExplore
from pyk.kore.prelude import int_dv
from pyk.ktool.krun import KRunOutput, _krun
from pyk.prelude.ml import is_bottom, is_top
from pyk.proof import APRProof
from pyk.proof.equality import EqualityProof
from pyk.proof.show import APRProofShow
from pyk.proof.tui import APRProofViewer
from pyk.utils import BugReport, single

from .cli import KEVMCLIArgs, node_id_like
from .foundry import (
    Foundry,
    foundry_kompile,
    foundry_list,
    foundry_node_printer,
    foundry_prove,
    foundry_remove_node,
    foundry_section_edge,
    foundry_show,
    foundry_simplify_node,
    foundry_step_node,
    foundry_to_dot,
)
from .gst_to_kore import _mode_to_kore, _schedule_to_kore
from .kevm import KEVM, kevm_node_printer
from .kompile import KompileTarget, kevm_kompile
from .solc_to_k import solc_compile, solc_to_k
from .utils import arg_pair_of, ensure_ksequence_on_k_cell, get_apr_proof_for_spec, kevm_prove, print_failure_info

if TYPE_CHECKING:
    from argparse import Namespace
    from collections.abc import Callable, Iterable
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


def exec_compile(contract_file: Path, **kwargs: Any) -> None:
    res = solc_compile(contract_file)
    print(json.dumps(res))


def exec_kompile(
    target: KompileTarget,
    output_dir: Path | None,
    main_file: Path,
    emit_json: bool,
    includes: list[str],
    main_module: str | None,
    syntax_module: str | None,
    read_only: bool = False,
    ccopts: Iterable[str] = (),
    o0: bool = False,
    o1: bool = False,
    o2: bool = False,
    o3: bool = False,
    debug: bool = False,
    enable_llvm_debug: bool = False,
    **kwargs: Any,
) -> None:
    optimization = 0
    if o1:
        optimization = 1
    if o2:
        optimization = 2
    if o3:
        optimization = 3

    kevm_kompile(
        target,
        output_dir=output_dir,
        main_file=main_file,
        main_module=main_module,
        syntax_module=syntax_module,
        includes=includes,
        emit_json=emit_json,
        read_only=read_only,
        ccopts=ccopts,
        optimization=optimization,
        enable_llvm_debug=enable_llvm_debug,
        debug=debug,
    )


def exec_solc_to_k(
    definition_dir: Path,
    contract_file: Path,
    contract_name: str,
    main_module: str | None,
    requires: list[str],
    imports: list[str],
    **kwargs: Any,
) -> None:
    k_text = solc_to_k(
        definition_dir=definition_dir,
        contract_file=contract_file,
        contract_name=contract_name,
        main_module=main_module,
        requires=requires,
        imports=imports,
    )
    print(k_text)


def exec_foundry_kompile(
    definition_dir: Path,
    foundry_root: Path,
    includes: Iterable[str] = (),
    regen: bool = False,
    rekompile: bool = False,
    requires: Iterable[str] = (),
    imports: Iterable[str] = (),
    ccopts: Iterable[str] = (),
    llvm_kompile: bool = True,
    debug: bool = False,
    llvm_library: bool = False,
    **kwargs: Any,
) -> None:
    _ignore_arg(kwargs, 'main_module', f'--main-module {kwargs["main_module"]}')
    _ignore_arg(kwargs, 'syntax_module', f'--syntax-module {kwargs["syntax_module"]}')
    _ignore_arg(kwargs, 'spec_module', f'--spec-module {kwargs["spec_module"]}')
    _ignore_arg(kwargs, 'o0', '-O0')
    _ignore_arg(kwargs, 'o1', '-O1')
    _ignore_arg(kwargs, 'o2', '-O2')
    _ignore_arg(kwargs, 'o3', '-O3')
    foundry_kompile(
        definition_dir=definition_dir,
        foundry_root=foundry_root,
        includes=includes,
        regen=regen,
        rekompile=rekompile,
        requires=requires,
        imports=imports,
        ccopts=ccopts,
        llvm_kompile=llvm_kompile,
        debug=debug,
        llvm_library=llvm_library,
    )


def exec_prove_legacy(
    definition_dir: Path,
    spec_file: Path,
    includes: Iterable[str] = (),
    bug_report: bool = False,
    save_directory: Path | None = None,
    spec_module: str | None = None,
    claim_labels: Iterable[str] | None = None,
    exclude_claim_labels: Iterable[str] = (),
    debug: bool = False,
    debugger: bool = False,
    max_depth: int | None = None,
    max_counterexamples: int | None = None,
    branching_allowed: int | None = None,
    haskell_backend_args: Iterable[str] = (),
    **kwargs: Any,
) -> None:
    _ignore_arg(kwargs, 'md_selector', f'--md-selector: {kwargs["md_selector"]}')
    kevm = KEVM(definition_dir, use_directory=save_directory)
    final_state = kevm.prove_legacy(
        spec_file=spec_file,
        includes=includes,
        bug_report=bug_report,
        spec_module=spec_module,
        claim_labels=claim_labels,
        exclude_claim_labels=exclude_claim_labels,
        debug=debug,
        debugger=debugger,
        max_depth=max_depth,
        max_counterexamples=max_counterexamples,
        branching_allowed=branching_allowed,
        haskell_backend_args=haskell_backend_args,
    )
    print(kevm.pretty_print(final_state))
    if not is_top(final_state):
        raise SystemExit(1)


def exec_prove(
    definition_dir: Path,
    spec_file: Path,
    includes: Iterable[str],
    bug_report: bool = False,
    save_directory: Path | None = None,
    spec_module: str | None = None,
    claim_labels: Iterable[str] | None = None,
    exclude_claim_labels: Iterable[str] = (),
    reinit: bool = False,
    max_depth: int = 1000,
    max_iterations: int | None = None,
    workers: int = 1,
    simplify_init: bool = True,
    break_every_step: bool = False,
    break_on_jumpi: bool = False,
    break_on_calls: bool = True,
    implication_every_block: bool = True,
    kore_rpc_command: str | Iterable[str] = ('kore-rpc',),
    smt_timeout: int | None = None,
    smt_retry_limit: int | None = None,
    trace_rewrites: bool = False,
    failure_info: bool = True,
    auto_abstract_gas: bool = False,
    **kwargs: Any,
) -> None:
    _ignore_arg(kwargs, 'md_selector', f'--md-selector: {kwargs["md_selector"]}')
    md_selector = 'k & ! node'

    br = BugReport(spec_file.with_suffix('.bug_report')) if bug_report else None
    kevm = KEVM(definition_dir, use_directory=save_directory, bug_report=br)

    _LOGGER.info(f'Extracting claims from file: {spec_file}')
    claims = kevm.get_claims(
        spec_file,
        spec_module_name=spec_module,
        include_dirs=[Path(i) for i in includes],
        md_selector=md_selector,
        claim_labels=claim_labels,
        exclude_claim_labels=exclude_claim_labels,
    )

    if not claims:
        raise ValueError(f'No claims found in file: {spec_file}')

    if isinstance(kore_rpc_command, str):
        kore_rpc_command = kore_rpc_command.split()

    def is_functional(claim: KClaim) -> bool:
        claim_lhs = claim.body
        if type(claim_lhs) is KRewrite:
            claim_lhs = claim_lhs.lhs
        return not (type(claim_lhs) is KApply and claim_lhs.label.name == '<generatedTop>')

    def _init_and_run_proof(claim: KClaim) -> tuple[bool, list[str] | None]:
        with KCFGExplore(
            kevm,
            id=claim.label,
            bug_report=br,
            kore_rpc_command=kore_rpc_command,
            smt_timeout=smt_timeout,
            smt_retry_limit=smt_retry_limit,
            trace_rewrites=trace_rewrites,
        ) as kcfg_explore:
            proof_problem: Proof
            if is_functional(claim):
                if (
                    save_directory is not None
                    and not reinit
                    and EqualityProof.proof_exists(claim.label, save_directory)
                ):
                    proof_problem = EqualityProof.read_proof(claim.label, save_directory)
                else:
                    proof_problem = EqualityProof.from_claim(claim, kevm.definition, proof_dir=save_directory)
            else:
                if save_directory is not None and not reinit and APRProof.proof_exists(claim.label, save_directory):
                    proof_problem = APRProof.read_proof(claim.label, save_directory)

                else:
                    _LOGGER.info(f'Converting claim to KCFG: {claim.label}')
                    kcfg, init_node_id, target_node_id = KCFG.from_claim(kevm.definition, claim)

                    new_init = ensure_ksequence_on_k_cell(kcfg.node(init_node_id).cterm)
                    new_target = ensure_ksequence_on_k_cell(kcfg.node(target_node_id).cterm)

                    _LOGGER.info(f'Computing definedness constraint for initial node: {claim.label}')
                    new_init = kcfg_explore.cterm_assume_defined(new_init)

                    if simplify_init:
                        _LOGGER.info(f'Simplifying initial and target node: {claim.label}')
                        _new_init, _ = kcfg_explore.cterm_simplify(new_init)
                        _new_target, _ = kcfg_explore.cterm_simplify(new_target)
                        if is_bottom(_new_init):
                            raise ValueError(
                                'Simplifying initial node led to #Bottom, are you sure your LHS is defined?'
                            )
                        if is_bottom(_new_target):
                            raise ValueError(
                                'Simplifying target node led to #Bottom, are you sure your RHS is defined?'
                            )
                        new_init = CTerm.from_kast(_new_init)
                        new_target = CTerm.from_kast(_new_target)

                    kcfg.replace_node(init_node_id, new_init)
                    kcfg.replace_node(target_node_id, new_target)

                    proof_problem = APRProof(
                        claim.label, kcfg, init_node_id, target_node_id, {}, proof_dir=save_directory
                    )

            passed = kevm_prove(
                kevm,
                proof_problem,
                kcfg_explore,
                save_directory=save_directory,
                max_depth=max_depth,
                max_iterations=max_iterations,
                workers=workers,
                break_every_step=break_every_step,
                break_on_jumpi=break_on_jumpi,
                break_on_calls=break_on_calls,
                implication_every_block=implication_every_block,
                is_terminal=KEVM.is_terminal,
                extract_branches=KEVM.extract_branches,
                bug_report=br,
                kore_rpc_command=kore_rpc_command,
                smt_timeout=smt_timeout,
                smt_retry_limit=smt_retry_limit,
                trace_rewrites=trace_rewrites,
                abstract_node=(KEVM.abstract_gas_cell if auto_abstract_gas else None),
            )
            failure_log = None
            if not passed:
                failure_log = print_failure_info(proof_problem, kcfg_explore)

            return passed, failure_log

    results: list[tuple[bool, list[str] | None]]
    if workers > 1:
        with ProcessPool(ncpus=workers) as process_pool:
            results = process_pool.map(_init_and_run_proof, claims)
    else:
        results = []
        for claim in claims:
            results.append(_init_and_run_proof(claim))

    failed = 0
    for claim, r in zip(claims, results, strict=True):
        passed, failure_log = r
        if passed:
            print(f'PROOF PASSED: {claim.label}')
        else:
            failed += 1
            print(f'PROOF FAILED: {claim.label}')
            if failure_info and failure_log is not None:
                for line in failure_log:
                    print(line)

    if failed:
        sys.exit(failed)


def exec_prune_proof(
    definition_dir: Path,
    spec_file: Path,
    node: NodeIdLike,
    includes: Iterable[str] = (),
    save_directory: Path | None = None,
    spec_module: str | None = None,
    claim_labels: Iterable[str] | None = None,
    exclude_claim_labels: Iterable[str] = (),
    **kwargs: Any,
) -> None:
    _ignore_arg(kwargs, 'md_selector', f'--md-selector: {kwargs["md_selector"]}')
    md_selector = 'k & ! node'

    if save_directory is None:
        raise ValueError('Must pass --save-directory to prune-proof!')

    _LOGGER.warning(f'definition_dir: {definition_dir}')
    kevm = KEVM(definition_dir, use_directory=save_directory)

    _LOGGER.info(f'Extracting claims from file: {spec_file}')
    claim = single(
        kevm.get_claims(
            spec_file,
            spec_module_name=spec_module,
            include_dirs=[Path(i) for i in includes],
            md_selector=md_selector,
            claim_labels=claim_labels,
            exclude_claim_labels=exclude_claim_labels,
        )
    )

    apr_proof = APRProof.read_proof(claim.label, save_directory)
    node_ids = apr_proof.kcfg.prune(node)
    _LOGGER.info(f'Pruned nodes: {node_ids}')
    apr_proof.write_proof()


def exec_show_kcfg(
    definition_dir: Path,
    spec_file: Path,
    save_directory: Path | None = None,
    includes: Iterable[str] = (),
    claim_labels: Iterable[str] | None = None,
    exclude_claim_labels: Iterable[str] = (),
    spec_module: str | None = None,
    md_selector: str | None = None,
    nodes: Iterable[NodeIdLike] = (),
    node_deltas: Iterable[tuple[NodeIdLike, NodeIdLike]] = (),
    to_module: bool = False,
    minimize: bool = True,
    failure_info: bool = False,
    sort_collections: bool = False,
    pending: bool = False,
    failing: bool = False,
    **kwargs: Any,
) -> None:
    kevm = KEVM(definition_dir)
    proof = get_apr_proof_for_spec(
        kevm,
        spec_file,
        save_directory=save_directory,
        spec_module_name=spec_module,
        include_dirs=[Path(i) for i in includes],
        md_selector=md_selector,
        claim_labels=claim_labels,
        exclude_claim_labels=exclude_claim_labels,
    )

    if pending:
        nodes = list(nodes) + [node.id for node in proof.pending]
    if failing:
        nodes = list(nodes) + [node.id for node in proof.failing]

    node_printer = kevm_node_printer(kevm, proof)
    proof_show = APRProofShow(kevm, node_printer=node_printer)

    res_lines = proof_show.show(
        proof,
        nodes=nodes,
        node_deltas=node_deltas,
        to_module=to_module,
        minimize=minimize,
        sort_collections=sort_collections,
    )

    if failure_info:
        with KCFGExplore(kevm, id=proof.id) as kcfg_explore:
            res_lines += print_failure_info(proof, kcfg_explore)

    print('\n'.join(res_lines))


def exec_view_kcfg(
    definition_dir: Path,
    spec_file: Path,
    save_directory: Path | None = None,
    includes: Iterable[str] = (),
    claim_labels: Iterable[str] | None = None,
    exclude_claim_labels: Iterable[str] = (),
    spec_module: str | None = None,
    md_selector: str | None = None,
    **kwargs: Any,
) -> None:
    kevm = KEVM(definition_dir)
    proof = get_apr_proof_for_spec(
        kevm,
        spec_file,
        save_directory=save_directory,
        spec_module_name=spec_module,
        include_dirs=[Path(i) for i in includes],
        md_selector=md_selector,
        claim_labels=claim_labels,
        exclude_claim_labels=exclude_claim_labels,
    )

    node_printer = kevm_node_printer(kevm, proof)
    proof_view = APRProofViewer(proof, kevm, node_printer=node_printer)

    proof_view.run()


def exec_foundry_prove(
    foundry_root: Path,
    max_depth: int = 1000,
    max_iterations: int | None = None,
    reinit: bool = False,
    tests: Iterable[str] = (),
    exclude_tests: Iterable[str] = (),
    workers: int = 1,
    simplify_init: bool = True,
    break_every_step: bool = False,
    break_on_jumpi: bool = False,
    break_on_calls: bool = True,
    implication_every_block: bool = True,
    bmc_depth: int | None = None,
    bug_report: bool = False,
    kore_rpc_command: str | Iterable[str] = ('kore-rpc',),
    use_booster: bool = False,
    smt_timeout: int | None = None,
    smt_retry_limit: int | None = None,
    failure_info: bool = True,
    trace_rewrites: bool = False,
    auto_abstract_gas: bool = False,
    **kwargs: Any,
) -> None:
    _ignore_arg(kwargs, 'main_module', f'--main-module: {kwargs["main_module"]}')
    _ignore_arg(kwargs, 'syntax_module', f'--syntax-module: {kwargs["syntax_module"]}')
    _ignore_arg(kwargs, 'definition_dir', f'--definition: {kwargs["definition_dir"]}')
    _ignore_arg(kwargs, 'spec_module', f'--spec-module: {kwargs["spec_module"]}')

    if isinstance(kore_rpc_command, str):
        kore_rpc_command = kore_rpc_command.split()

    results = foundry_prove(
        foundry_root=foundry_root,
        max_depth=max_depth,
        max_iterations=max_iterations,
        reinit=reinit,
        tests=tests,
        exclude_tests=exclude_tests,
        workers=workers,
        simplify_init=simplify_init,
        break_every_step=break_every_step,
        break_on_jumpi=break_on_jumpi,
        break_on_calls=break_on_calls,
        implication_every_block=implication_every_block,
        bmc_depth=bmc_depth,
        bug_report=bug_report,
        kore_rpc_command=kore_rpc_command,
        use_booster=use_booster,
        smt_timeout=smt_timeout,
        smt_retry_limit=smt_retry_limit,
        trace_rewrites=trace_rewrites,
        auto_abstract_gas=auto_abstract_gas,
    )
    failed = 0
    for pid, r in results.items():
        passed, failure_log = r
        if passed:
            print(f'PROOF PASSED: {pid}')
        else:
            failed += 1
            print(f'PROOF FAILED: {pid}')
            if failure_info and failure_log is not None:
                failure_log += Foundry.help_info()
                for line in failure_log:
                    print(line)

    sys.exit(failed)


def exec_foundry_show(
    foundry_root: Path,
    test: str,
    nodes: Iterable[NodeIdLike] = (),
    node_deltas: Iterable[tuple[NodeIdLike, NodeIdLike]] = (),
    to_module: bool = False,
    minimize: bool = True,
    sort_collections: bool = False,
    omit_unstable_output: bool = False,
    pending: bool = False,
    failing: bool = False,
    failure_info: bool = False,
    **kwargs: Any,
) -> None:
    output = foundry_show(
        foundry_root=foundry_root,
        test=test,
        nodes=nodes,
        node_deltas=node_deltas,
        to_module=to_module,
        minimize=minimize,
        omit_unstable_output=omit_unstable_output,
        sort_collections=sort_collections,
        pending=pending,
        failing=failing,
        failure_info=failure_info,
    )
    print(output)


def exec_foundry_to_dot(foundry_root: Path, test: str, **kwargs: Any) -> None:
    foundry_to_dot(foundry_root=foundry_root, test=test)


def exec_foundry_list(foundry_root: Path, **kwargs: Any) -> None:
    stats = foundry_list(foundry_root=foundry_root)
    print('\n'.join(stats))


def exec_run(
    definition_dir: Path,
    input_file: Path,
    term: bool,
    parser: str | None,
    expand_macros: str,
    depth: int | None,
    output: str,
    schedule: str,
    mode: str,
    chainid: int,
    **kwargs: Any,
) -> None:
    cmap = {
        'MODE': _mode_to_kore(mode).text,
        'SCHEDULE': _schedule_to_kore(schedule).text,
        'CHAINID': int_dv(chainid).text,
    }
    pmap = {'MODE': 'cat', 'SCHEDULE': 'cat', 'CHAINID': 'cat'}
    krun_result = _krun(
        definition_dir=definition_dir,
        input_file=input_file,
        depth=depth,
        term=term,
        no_expand_macros=not expand_macros,
        parser=parser,
        cmap=cmap,
        pmap=pmap,
        output=KRunOutput[output.upper()],
    )
    print(krun_result.stdout)
    sys.exit(krun_result.returncode)


def exec_foundry_view_kcfg(foundry_root: Path, test: str, **kwargs: Any) -> None:
    foundry = Foundry(foundry_root)
    proofs_dir = foundry.out / 'apr_proofs'
    contract_name, test_name = test.split('.')
    proof_digest = foundry.proof_digest(contract_name, test_name)

    proof = APRProof.read_proof(proof_digest, proofs_dir)

    def _short_info(cterm: CTerm) -> Iterable[str]:
        return foundry.short_info_for_contract(contract_name, cterm)

    def _custom_view(elem: KCFGElem) -> Iterable[str]:
        return foundry.custom_view(contract_name, elem)

    node_printer = foundry_node_printer(foundry, contract_name, proof)
    viewer = APRProofViewer(proof, foundry.kevm, node_printer=node_printer, custom_view=_custom_view)
    viewer.run()


def exec_foundry_remove_node(foundry_root: Path, test: str, node: NodeIdLike, **kwargs: Any) -> None:
    foundry_remove_node(foundry_root=foundry_root, test=test, node=node)


def exec_foundry_simplify_node(
    foundry_root: Path,
    test: str,
    node: NodeIdLike,
    replace: bool = False,
    minimize: bool = True,
    sort_collections: bool = False,
    bug_report: bool = False,
    smt_timeout: int | None = None,
    smt_retry_limit: int | None = None,
    trace_rewrites: bool = False,
    **kwargs: Any,
) -> None:
    pretty_term = foundry_simplify_node(
        foundry_root=foundry_root,
        test=test,
        node=node,
        replace=replace,
        minimize=minimize,
        sort_collections=sort_collections,
        bug_report=bug_report,
        smt_timeout=smt_timeout,
        smt_retry_limit=smt_retry_limit,
        trace_rewrites=trace_rewrites,
    )
    print(f'Simplified:\n{pretty_term}')


def exec_foundry_step_node(
    foundry_root: Path,
    test: str,
    node: NodeIdLike,
    repeat: int = 1,
    depth: int = 1,
    bug_report: bool = False,
    smt_timeout: int | None = None,
    smt_retry_limit: int | None = None,
    trace_rewrites: bool = False,
    **kwargs: Any,
) -> None:
    foundry_step_node(
        foundry_root=foundry_root,
        test=test,
        node=node,
        repeat=repeat,
        depth=depth,
        bug_report=bug_report,
        smt_timeout=smt_timeout,
        smt_retry_limit=smt_retry_limit,
        trace_rewrites=trace_rewrites,
    )


def exec_foundry_section_edge(
    foundry_root: Path,
    test: str,
    edge: tuple[str, str],
    sections: int = 2,
    replace: bool = False,
    bug_report: bool = False,
    smt_timeout: int | None = None,
    smt_retry_limit: int | None = None,
    trace_rewrites: bool = False,
    **kwargs: Any,
) -> None:
    foundry_section_edge(
        foundry_root=foundry_root,
        test=test,
        edge=edge,
        sections=sections,
        replace=replace,
        bug_report=bug_report,
        smt_timeout=smt_timeout,
        smt_retry_limit=smt_retry_limit,
        trace_rewrites=trace_rewrites,
    )


# Helpers


def _create_argument_parser() -> ArgumentParser:
    def list_of(elem_type: Callable[[str], T], delim: str = ';') -> Callable[[str], list[T]]:
        def parse(s: str) -> list[T]:
            return [elem_type(elem) for elem in s.split(delim)]

        return parse

    kevm_cli_args = KEVMCLIArgs()
    parser = ArgumentParser(prog='python3 -m kevm_pyk')

    command_parser = parser.add_subparsers(dest='command', required=True)

    kevm_kompile_args = command_parser.add_parser(
        'kompile',
        help='Kompile KEVM specification.',
        parents=[kevm_cli_args.logging_args, kevm_cli_args.k_args, kevm_cli_args.kompile_args],
    )
    kevm_kompile_args.add_argument('main_file', type=file_path, help='Path to file with main module.')
    kevm_kompile_args.add_argument(
        '--target', type=KompileTarget, help='[llvm|haskell|haskell-standalone|node|foundry]'
    )
    kevm_kompile_args.add_argument(
        '-o', '--output-definition', type=Path, dest='output_dir', help='Path to write kompiled definition to.'
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
            kevm_cli_args.smt_args,
            kevm_cli_args.explore_args,
            kevm_cli_args.spec_args,
        ],
    )
    prove_args.add_argument(
        '--reinit',
        dest='reinit',
        default=False,
        action='store_true',
        help='Reinitialize CFGs even if they already exist.',
    )

    prune_proof_args = command_parser.add_parser(
        'prune-proof',
        help='Remove a node and its successors from the proof state.',
        parents=[
            kevm_cli_args.logging_args,
            kevm_cli_args.k_args,
            kevm_cli_args.spec_args,
        ],
    )
    prune_proof_args.add_argument('node', type=node_id_like, help='Node to remove CFG subgraph from.')

    _ = command_parser.add_parser(
        'prove-legacy',
        help='Run KEVM proof using the legacy kprove binary.',
        parents=[
            kevm_cli_args.logging_args,
            kevm_cli_args.k_args,
            kevm_cli_args.spec_args,
            kevm_cli_args.kprove_legacy_args,
        ],
    )

    _ = command_parser.add_parser(
        'view-kcfg',
        help='Display tree view of CFG',
        parents=[kevm_cli_args.logging_args, kevm_cli_args.k_args, kevm_cli_args.spec_args],
    )

    _ = command_parser.add_parser(
        'show-kcfg',
        help='Display tree show of CFG',
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
        parents=[kevm_cli_args.logging_args, kevm_cli_args.evm_chain_args, kevm_cli_args.k_args],
    )
    run_args.add_argument('input_file', type=file_path, help='Path to input file.')
    run_args.add_argument(
        '--term', default=False, action='store_true', help='<input_file> is the entire term to execute.'
    )
    run_args.add_argument('--parser', default=None, type=str, help='Parser to use for $PGM.')
    run_args.add_argument(
        '--output',
        default='pretty',
        type=str,
        help='Output format to use, one of [pretty|program|kast|binary|json|latex|kore|none].',
    )
    run_args.add_argument(
        '--expand-macros',
        dest='expand_macros',
        default=True,
        action='store_true',
        help='Expand macros on the input term before execution.',
    )
    run_args.add_argument(
        '--no-expand-macros',
        dest='expand_macros',
        action='store_false',
        help='Do not expand macros on the input term before execution.',
    )

    solc_args = command_parser.add_parser('compile', help='Generate combined JSON with solc compilation results.')
    solc_args.add_argument('contract_file', type=file_path, help='Path to contract file.')

    solc_to_k_args = command_parser.add_parser(
        'solc-to-k',
        help='Output helper K definition for given JSON output from solc compiler.',
        parents=[kevm_cli_args.logging_args, kevm_cli_args.k_args, kevm_cli_args.k_gen_args],
    )
    solc_to_k_args.add_argument('contract_file', type=file_path, help='Path to contract file.')
    solc_to_k_args.add_argument('contract_name', type=str, help='Name of contract to generate K helpers for.')

    foundry_kompile = command_parser.add_parser(
        'foundry-kompile',
        help='Kompile K definition corresponding to given output directory.',
        parents=[
            kevm_cli_args.logging_args,
            kevm_cli_args.k_args,
            kevm_cli_args.k_gen_args,
            kevm_cli_args.kompile_args,
            kevm_cli_args.foundry_args,
        ],
    )
    foundry_kompile.add_argument(
        '--regen',
        dest='regen',
        default=False,
        action='store_true',
        help='Regenerate foundry.k even if it already exists.',
    )
    foundry_kompile.add_argument(
        '--rekompile',
        dest='rekompile',
        default=False,
        action='store_true',
        help='Rekompile foundry.k even if kompiled definition already exists.',
    )

    foundry_prove_args = command_parser.add_parser(
        'foundry-prove',
        help='Run Foundry Proof.',
        parents=[
            kevm_cli_args.logging_args,
            kevm_cli_args.parallel_args,
            kevm_cli_args.k_args,
            kevm_cli_args.kprove_args,
            kevm_cli_args.smt_args,
            kevm_cli_args.rpc_args,
            kevm_cli_args.explore_args,
            kevm_cli_args.foundry_args,
        ],
    )
    foundry_prove_args.add_argument(
        '--test',
        type=str,
        dest='tests',
        default=[],
        action='append',
        help='Limit to only listed tests, ContractName.TestName',
    )
    foundry_prove_args.add_argument(
        '--exclude-test',
        type=str,
        dest='exclude_tests',
        default=[],
        action='append',
        help='Skip listed tests, ContractName.TestName',
    )
    foundry_prove_args.add_argument(
        '--reinit',
        dest='reinit',
        default=False,
        action='store_true',
        help='Reinitialize CFGs even if they already exist.',
    )
    foundry_prove_args.add_argument(
        '--bmc-depth',
        dest='bmc_depth',
        default=None,
        type=int,
        help='Max depth of loop unrolling during bounded model checking',
    )
    foundry_prove_args.add_argument(
        '--use-booster',
        dest='use_booster',
        default=False,
        action='store_true',
        help="Use the booster RPC server instead of kore-rpc. Requires calling foundry-kompile with the '--with-llvm-library' flag",
    )

    foundry_show_args = command_parser.add_parser(
        'foundry-show',
        help='Display a given Foundry CFG.',
        parents=[
            kevm_cli_args.logging_args,
            kevm_cli_args.k_args,
            kevm_cli_args.kcfg_show_args,
            kevm_cli_args.display_args,
            kevm_cli_args.foundry_args,
        ],
    )
    foundry_show_args.add_argument('test', type=str, help='Display the CFG for this test.')
    foundry_show_args.add_argument(
        '--omit-unstable-output',
        dest='omit_unstable_output',
        default=False,
        action='store_true',
        help='Strip output that is likely to change without the contract logic changing',
    )
    foundry_to_dot = command_parser.add_parser(
        'foundry-to-dot',
        help='Dump the given CFG for the test as DOT for visualization.',
        parents=[kevm_cli_args.logging_args, kevm_cli_args.foundry_args],
    )
    foundry_to_dot.add_argument('test', type=str, help='Display the CFG for this test.')

    command_parser.add_parser(
        'foundry-list',
        help='List information about CFGs on disk',
        parents=[kevm_cli_args.logging_args, kevm_cli_args.k_args, kevm_cli_args.foundry_args],
    )

    foundry_view_kcfg_args = command_parser.add_parser(
        'foundry-view-kcfg',
        help='Display tree view of CFG',
        parents=[kevm_cli_args.logging_args, kevm_cli_args.foundry_args],
    )
    foundry_view_kcfg_args.add_argument('test', type=str, help='View the CFG for this test.')

    foundry_remove_node = command_parser.add_parser(
        'foundry-remove-node',
        help='Remove a node and its successors.',
        parents=[kevm_cli_args.logging_args, kevm_cli_args.foundry_args],
    )
    foundry_remove_node.add_argument('test', type=str, help='View the CFG for this test.')
    foundry_remove_node.add_argument('node', type=node_id_like, help='Node to remove CFG subgraph from.')

    foundry_simplify_node = command_parser.add_parser(
        'foundry-simplify-node',
        help='Simplify a given node, and potentially replace it.',
        parents=[
            kevm_cli_args.logging_args,
            kevm_cli_args.smt_args,
            kevm_cli_args.rpc_args,
            kevm_cli_args.display_args,
            kevm_cli_args.foundry_args,
        ],
    )
    foundry_simplify_node.add_argument('test', type=str, help='Simplify node in this CFG.')
    foundry_simplify_node.add_argument('node', type=node_id_like, help='Node to simplify in CFG.')
    foundry_simplify_node.add_argument(
        '--replace', default=False, help='Replace the original node with the simplified variant in the graph.'
    )

    foundry_step_node = command_parser.add_parser(
        'foundry-step-node',
        help='Step from a given node, adding it to the CFG.',
        parents=[
            kevm_cli_args.logging_args,
            kevm_cli_args.rpc_args,
            kevm_cli_args.smt_args,
            kevm_cli_args.foundry_args,
        ],
    )
    foundry_step_node.add_argument('test', type=str, help='Step from node in this CFG.')
    foundry_step_node.add_argument('node', type=node_id_like, help='Node to step from in CFG.')
    foundry_step_node.add_argument(
        '--repeat', type=int, default=1, help='How many node expansions to do from the given start node (>= 1).'
    )
    foundry_step_node.add_argument(
        '--depth', type=int, default=1, help='How many steps to take from initial node on edge.'
    )

    foundry_section_edge = command_parser.add_parser(
        'foundry-section-edge',
        help='Given an edge in the graph, cut it into sections to get intermediate nodes.',
        parents=[
            kevm_cli_args.logging_args,
            kevm_cli_args.rpc_args,
            kevm_cli_args.smt_args,
            kevm_cli_args.foundry_args,
        ],
    )
    foundry_section_edge.add_argument('test', type=str, help='Section edge in this CFG.')
    foundry_section_edge.add_argument('edge', type=arg_pair_of(str, str), help='Edge to section in CFG.')
    foundry_section_edge.add_argument(
        '--sections', type=int, default=2, help='Number of sections to make from edge (>= 2).'
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
