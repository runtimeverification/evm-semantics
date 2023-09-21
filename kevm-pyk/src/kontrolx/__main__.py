from __future__ import annotations

import json
import logging
import sys
from argparse import ArgumentParser
from typing import TYPE_CHECKING

from pyk.cli.utils import file_path
from pyk.proof.tui import APRProofViewer

from kevm_pyk.cli import KEVMCLIArgs, node_id_like
from kevm_pyk.dist import DistTarget
from kevm_pyk.utils import arg_pair_of

from .foundry import (
    Foundry,
    foundry_get_model,
    foundry_kompile,
    foundry_list,
    foundry_merge_nodes,
    foundry_node_printer,
    foundry_prove,
    foundry_remove_node,
    foundry_section_edge,
    foundry_show,
    foundry_simplify_node,
    foundry_step_node,
    foundry_to_dot,
)
from .solc_to_k import solc_compile, solc_to_k

if TYPE_CHECKING:
    from argparse import Namespace
    from collections.abc import Callable, Iterable
    from pathlib import Path
    from typing import Any, Final, TypeVar

    from pyk.cterm import CTerm
    from pyk.kcfg.kcfg import NodeIdLike
    from pyk.kcfg.tui import KCFGElem
    from pyk.utils import BugReport

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


def exec_version(**kwargs: Any) -> None:
    raise NotImplementedError()


def exec_compile(contract_file: Path, **kwargs: Any) -> None:
    res = solc_compile(contract_file)
    print(json.dumps(res))


def exec_solc_to_k(
    contract_file: Path,
    contract_name: str,
    main_module: str | None,
    requires: list[str],
    imports: list[str],
    target: DistTarget | None = None,
    **kwargs: Any,
) -> None:
    if target is None:
        target = DistTarget.HASKELL

    k_text = solc_to_k(
        definition_dir=target.get(),
        contract_file=contract_file,
        contract_name=contract_name,
        main_module=main_module,
        requires=requires,
        imports=imports,
    )
    print(k_text)


def exec_foundry_kompile(
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
    verbose: bool = False,
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
        foundry_root=foundry_root,
        includes=includes,
        regen=regen,
        rekompile=rekompile,
        requires=requires,
        imports=imports,
        ccopts=ccopts,
        llvm_kompile=llvm_kompile,
        debug=debug,
        verbose=verbose,
    )


def exec_foundry_prove(
    foundry_root: Path,
    max_depth: int = 1000,
    max_iterations: int | None = None,
    reinit: bool = False,
    tests: Iterable[tuple[str, int | None]] = (),
    exclude_tests: Iterable[str] = (),
    workers: int = 1,
    simplify_init: bool = True,
    break_every_step: bool = False,
    break_on_jumpi: bool = False,
    break_on_calls: bool = True,
    bmc_depth: int | None = None,
    bug_report: BugReport | None = None,
    kore_rpc_command: str | Iterable[str] | None = None,
    use_booster: bool = False,
    smt_timeout: int | None = None,
    smt_retry_limit: int | None = None,
    failure_info: bool = True,
    counterexample_info: bool = False,
    trace_rewrites: bool = False,
    auto_abstract_gas: bool = False,
    max_branches: int | None = None,
    **kwargs: Any,
) -> None:
    _ignore_arg(kwargs, 'main_module', f'--main-module: {kwargs["main_module"]}')
    _ignore_arg(kwargs, 'syntax_module', f'--syntax-module: {kwargs["syntax_module"]}')
    _ignore_arg(kwargs, 'definition_dir', f'--definition: {kwargs["definition_dir"]}')
    _ignore_arg(kwargs, 'spec_module', f'--spec-module: {kwargs["spec_module"]}')

    if smt_timeout is None:
        smt_timeout = 300
    if smt_retry_limit is None:
        smt_retry_limit = 10

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
        bmc_depth=bmc_depth,
        bug_report=bug_report,
        kore_rpc_command=kore_rpc_command,
        use_booster=use_booster,
        counterexample_info=counterexample_info,
        smt_timeout=smt_timeout,
        smt_retry_limit=smt_retry_limit,
        trace_rewrites=trace_rewrites,
        auto_abstract_gas=auto_abstract_gas,
        max_branches=max_branches,
    )
    failed = 0
    for proof in results:
        if proof.passed:
            print(f'PROOF PASSED: {proof.id}')
        elif proof.is_proof_pending:
            print(f'PROOF PENDING: {proof.id}')
        elif proof.failed:
            print(f'PROOF FAILED: {proof.id}')
            if failure_info and proof.failure_info is not None:
                failure_log = proof.failure_info.print()
                failure_log += Foundry.help_info()
                for line in failure_log:
                    print(line)

    sys.exit(failed)


def exec_foundry_show(
    foundry_root: Path,
    test: str,
    version: int | None,
    nodes: Iterable[NodeIdLike] = (),
    node_deltas: Iterable[tuple[NodeIdLike, NodeIdLike]] = (),
    to_module: bool = False,
    minimize: bool = True,
    sort_collections: bool = False,
    omit_unstable_output: bool = False,
    pending: bool = False,
    failing: bool = False,
    failure_info: bool = False,
    counterexample_info: bool = False,
    subproof_path: list[int] | None = None,
    **kwargs: Any,
) -> None:
    output = foundry_show(
        foundry_root=foundry_root,
        test=test,
        version=version,
        nodes=nodes,
        node_deltas=node_deltas,
        to_module=to_module,
        minimize=minimize,
        omit_unstable_output=omit_unstable_output,
        sort_collections=sort_collections,
        pending=pending,
        failing=failing,
        failure_info=failure_info,
        counterexample_info=counterexample_info,
        subproof_path=subproof_path,
    )
    print(output)


def exec_foundry_to_dot(
    foundry_root: Path, test: str, version: int | None, subproof_path: list[int] | None = None, **kwargs: Any
) -> None:
    foundry_to_dot(foundry_root=foundry_root, test=test, version=version, subproof_path=subproof_path)


def exec_foundry_list(foundry_root: Path, **kwargs: Any) -> None:
    stats = foundry_list(foundry_root=foundry_root)
    print('\n'.join(stats))


def exec_foundry_view_kcfg(
    foundry_root: Path, test: str, version: int | None, subproof_path: list[int] | None = None, **kwargs: Any
) -> None:
    foundry = Foundry(foundry_root)
    test_id = foundry.get_test_id(test, version, subproof_path=subproof_path)
    contract_name, _ = test_id.split('.')
    proof = foundry.get_apr_proof(test_id)

    def _short_info(cterm: CTerm) -> Iterable[str]:
        return foundry.short_info_for_contract(contract_name, cterm)

    def _custom_view(elem: KCFGElem) -> Iterable[str]:
        return foundry.custom_view(contract_name, elem)

    node_printer = foundry_node_printer(foundry, contract_name, proof)
    viewer = APRProofViewer(proof, foundry.kevm, node_printer=node_printer, custom_view=_custom_view)
    viewer.run()


def exec_foundry_remove_node(
    foundry_root: Path,
    test: str,
    node: NodeIdLike,
    version: int | None,
    subproof_path: list[int] | None = None,
    **kwargs: Any,
) -> None:
    foundry_remove_node(foundry_root=foundry_root, test=test, version=version, node=node, subproof_path=subproof_path)


def exec_foundry_simplify_node(
    foundry_root: Path,
    test: str,
    version: int | None,
    node: NodeIdLike,
    replace: bool = False,
    minimize: bool = True,
    sort_collections: bool = False,
    bug_report: BugReport | None = None,
    smt_timeout: int | None = None,
    smt_retry_limit: int | None = None,
    trace_rewrites: bool = False,
    subproof_path: list[int] | None = None,
    **kwargs: Any,
) -> None:
    if smt_timeout is None:
        smt_timeout = 300
    if smt_retry_limit is None:
        smt_retry_limit = 10

    pretty_term = foundry_simplify_node(
        foundry_root=foundry_root,
        test=test,
        version=version,
        node=node,
        replace=replace,
        minimize=minimize,
        sort_collections=sort_collections,
        bug_report=bug_report,
        smt_timeout=smt_timeout,
        smt_retry_limit=smt_retry_limit,
        trace_rewrites=trace_rewrites,
        subproof_path=subproof_path,
    )
    print(f'Simplified:\n{pretty_term}')


def exec_foundry_step_node(
    foundry_root: Path,
    test: str,
    version: int | None,
    node: NodeIdLike,
    repeat: int = 1,
    depth: int = 1,
    bug_report: BugReport | None = None,
    smt_timeout: int | None = None,
    smt_retry_limit: int | None = None,
    trace_rewrites: bool = False,
    subproof_path: list[int] | None = None,
    **kwargs: Any,
) -> None:
    if smt_timeout is None:
        smt_timeout = 300
    if smt_retry_limit is None:
        smt_retry_limit = 10

    foundry_step_node(
        foundry_root=foundry_root,
        test=test,
        version=version,
        node=node,
        repeat=repeat,
        depth=depth,
        bug_report=bug_report,
        smt_timeout=smt_timeout,
        smt_retry_limit=smt_retry_limit,
        trace_rewrites=trace_rewrites,
        subproof_path=subproof_path,
    )


def exec_foundry_merge_nodes(
    foundry_root: Path,
    test: str,
    version: int | None,
    nodes: Iterable[NodeIdLike],
    subproof_path: list[int] | None = None,
    **kwargs: Any,
) -> None:
    foundry_merge_nodes(
        foundry_root=foundry_root, node_ids=nodes, test=test, version=version, subproof_path=subproof_path
    )


def exec_foundry_section_edge(
    foundry_root: Path,
    test: str,
    version: int | None,
    edge: tuple[str, str],
    sections: int = 2,
    replace: bool = False,
    bug_report: BugReport | None = None,
    smt_timeout: int | None = None,
    smt_retry_limit: int | None = None,
    trace_rewrites: bool = False,
    subproof_path: list[int] | None = None,
    **kwargs: Any,
) -> None:
    if smt_timeout is None:
        smt_timeout = 300
    if smt_retry_limit is None:
        smt_retry_limit = 10

    foundry_section_edge(
        foundry_root=foundry_root,
        test=test,
        version=version,
        edge=edge,
        sections=sections,
        replace=replace,
        bug_report=bug_report,
        smt_timeout=smt_timeout,
        smt_retry_limit=smt_retry_limit,
        trace_rewrites=trace_rewrites,
        subproof_path=subproof_path,
    )


def exec_foundry_get_model(
    foundry_root: Path,
    test: str,
    version: int | None,
    nodes: Iterable[NodeIdLike] = (),
    pending: bool = False,
    failing: bool = False,
    subproof_path: list[int] | None = None,
    **kwargs: Any,
) -> None:
    output = foundry_get_model(
        foundry_root=foundry_root,
        test=test,
        version=version,
        nodes=nodes,
        pending=pending,
        failing=failing,
        subproof_path=subproof_path,
    )
    print(output)


# Helpers


def _create_argument_parser() -> ArgumentParser:
    def list_of(elem_type: Callable[[str], T], delim: str = ';') -> Callable[[str], list[T]]:
        def parse(s: str) -> list[T]:
            return [elem_type(elem) for elem in s.split(delim)]

        return parse

    kevm_cli_args = KEVMCLIArgs()
    parser = ArgumentParser(prog='kontrolx')

    command_parser = parser.add_subparsers(dest='command', required=True)

    command_parser.add_parser('version', help='Print out version of Kontrol command.')

    solc_args = command_parser.add_parser('compile', help='Generate combined JSON with solc compilation results.')
    solc_args.add_argument('contract_file', type=file_path, help='Path to contract file.')

    solc_to_k_args = command_parser.add_parser(
        'solc-to-k',
        help='Output helper K definition for given JSON output from solc compiler.',
        parents=[kevm_cli_args.logging_args, kevm_cli_args.target_args, kevm_cli_args.k_args, kevm_cli_args.k_gen_args],
    )
    solc_to_k_args.add_argument('contract_file', type=file_path, help='Path to contract file.')
    solc_to_k_args.add_argument('contract_name', type=str, help='Name of contract to generate K helpers for.')

    def _parse_test_version_tuple(value: str) -> tuple[str, int | None]:
        if ':' in value:
            test, version = value.split(':')
            return (test, int(version))
        else:
            return (value, None)

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
            kevm_cli_args.bug_report_args,
            kevm_cli_args.explore_args,
            kevm_cli_args.foundry_args,
        ],
    )
    foundry_prove_args.add_argument(
        '--test',
        type=_parse_test_version_tuple,
        dest='tests',
        default=[],
        action='append',
        help='Limit to only listed tests, ContractName.TestName',
    )
    foundry_prove_args.add_argument(
        '--exclude-test',
        type=_parse_test_version_tuple,
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
        help='Enables bounded model checking. Specifies the maximum depth to unroll all loops to.',
    )
    foundry_prove_args.add_argument(
        '--max-branches',
        dest='max_branches',
        default=None,
        type=int,
        help='Enables subproof splitting when the number of pending nodes exceeds max_branches',
    )
    foundry_prove_args.add_argument(
        '--use-booster',
        dest='use_booster',
        default=False,
        action='store_true',
        help='Use the booster RPC server instead of kore-rpc.',
    )

    foundry_show_args = command_parser.add_parser(
        'foundry-show',
        help='Display a given Foundry CFG.',
        parents=[
            kevm_cli_args.foundry_test_args,
            kevm_cli_args.logging_args,
            kevm_cli_args.k_args,
            kevm_cli_args.kcfg_show_args,
            kevm_cli_args.display_args,
            kevm_cli_args.foundry_args,
        ],
    )
    foundry_show_args.add_argument(
        '--omit-unstable-output',
        dest='omit_unstable_output',
        default=False,
        action='store_true',
        help='Strip output that is likely to change without the contract logic changing',
    )
    command_parser.add_parser(
        'foundry-to-dot',
        help='Dump the given CFG for the test as DOT for visualization.',
        parents=[kevm_cli_args.foundry_test_args, kevm_cli_args.logging_args, kevm_cli_args.foundry_args],
    )

    command_parser.add_parser(
        'foundry-list',
        help='List information about CFGs on disk',
        parents=[kevm_cli_args.logging_args, kevm_cli_args.k_args, kevm_cli_args.foundry_args],
    )

    command_parser.add_parser(
        'foundry-view-kcfg',
        help='Display tree view of CFG',
        parents=[kevm_cli_args.foundry_test_args, kevm_cli_args.logging_args, kevm_cli_args.foundry_args],
    )

    foundry_remove_node = command_parser.add_parser(
        'foundry-remove-node',
        help='Remove a node and its successors.',
        parents=[kevm_cli_args.foundry_test_args, kevm_cli_args.logging_args, kevm_cli_args.foundry_args],
    )
    foundry_remove_node.add_argument('node', type=node_id_like, help='Node to remove CFG subgraph from.')

    foundry_simplify_node = command_parser.add_parser(
        'foundry-simplify-node',
        help='Simplify a given node, and potentially replace it.',
        parents=[
            kevm_cli_args.foundry_test_args,
            kevm_cli_args.logging_args,
            kevm_cli_args.smt_args,
            kevm_cli_args.rpc_args,
            kevm_cli_args.bug_report_args,
            kevm_cli_args.display_args,
            kevm_cli_args.foundry_args,
        ],
    )
    foundry_simplify_node.add_argument('node', type=node_id_like, help='Node to simplify in CFG.')
    foundry_simplify_node.add_argument(
        '--replace', default=False, help='Replace the original node with the simplified variant in the graph.'
    )

    foundry_step_node = command_parser.add_parser(
        'foundry-step-node',
        help='Step from a given node, adding it to the CFG.',
        parents=[
            kevm_cli_args.foundry_test_args,
            kevm_cli_args.logging_args,
            kevm_cli_args.rpc_args,
            kevm_cli_args.bug_report_args,
            kevm_cli_args.smt_args,
            kevm_cli_args.foundry_args,
        ],
    )
    foundry_step_node.add_argument('node', type=node_id_like, help='Node to step from in CFG.')
    foundry_step_node.add_argument(
        '--repeat', type=int, default=1, help='How many node expansions to do from the given start node (>= 1).'
    )
    foundry_step_node.add_argument(
        '--depth', type=int, default=1, help='How many steps to take from initial node on edge.'
    )
    foundry_merge_node = command_parser.add_parser(
        'foundry-merge-nodes',
        help='Merge multiple nodes into one branch.',
        parents=[
            kevm_cli_args.foundry_test_args,
            kevm_cli_args.logging_args,
            kevm_cli_args.foundry_args,
        ],
    )
    foundry_merge_node.add_argument(
        '--node',
        type=node_id_like,
        dest='nodes',
        default=[],
        action='append',
        help='One node to be merged.',
    )

    foundry_section_edge = command_parser.add_parser(
        'foundry-section-edge',
        help='Given an edge in the graph, cut it into sections to get intermediate nodes.',
        parents=[
            kevm_cli_args.foundry_test_args,
            kevm_cli_args.logging_args,
            kevm_cli_args.rpc_args,
            kevm_cli_args.bug_report_args,
            kevm_cli_args.smt_args,
            kevm_cli_args.foundry_args,
        ],
    )
    foundry_section_edge.add_argument('edge', type=arg_pair_of(str, str), help='Edge to section in CFG.')
    foundry_section_edge.add_argument(
        '--sections', type=int, default=2, help='Number of sections to make from edge (>= 2).'
    )

    foundry_get_model = command_parser.add_parser(
        'foundry-get-model',
        help='Display a model for a given node.',
        parents=[
            kevm_cli_args.foundry_test_args,
            kevm_cli_args.logging_args,
            kevm_cli_args.rpc_args,
            kevm_cli_args.smt_args,
            kevm_cli_args.foundry_args,
        ],
    )
    foundry_get_model.add_argument(
        '--node',
        type=node_id_like,
        dest='nodes',
        default=[],
        action='append',
        help='List of nodes to display the models of.',
    )
    foundry_get_model.add_argument(
        '--pending', dest='pending', default=False, action='store_true', help='Also display models of pending nodes'
    )
    foundry_get_model.add_argument(
        '--failing', dest='failing', default=False, action='store_true', help='Also display models of failing nodes'
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
