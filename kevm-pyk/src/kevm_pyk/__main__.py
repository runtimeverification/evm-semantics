from __future__ import annotations

import json
import logging
import sys
from argparse import ArgumentParser
from enum import Enum
from pathlib import Path
from typing import TYPE_CHECKING

from pyk.cli_utils import BugReport, dir_path, ensure_dir_path, file_path
from pyk.kast.outer import KDefinition, KFlatModule, KImport, KRequire
from pyk.kcfg import KCFG, KCFGExplore, KCFGShow, KCFGViewer
from pyk.ktool.kompile import KompileBackend
from pyk.ktool.krun import KRunOutput, _krun
from pyk.proof import AGProof

from .foundry import (
    Foundry,
    foundry_kompile,
    foundry_list,
    foundry_prove,
    foundry_remove_node,
    foundry_section_edge,
    foundry_show,
    foundry_simplify_node,
    foundry_step_node,
    foundry_to_dot,
)
from .kevm import KEVM, KEVMKompileMode
from .solc_to_k import Contract, contract_to_main_module, solc_compile
from .utils import arg_pair_of, get_ag_proof_for_spec, parallel_kcfg_explore

if TYPE_CHECKING:
    from argparse import Namespace
    from typing import Any, Callable, Dict, Final, Iterable, List, Optional, Tuple, TypeVar, Union

    from pyk.cterm import CTerm
    from pyk.kcfg.tui import KCFGElem

    T = TypeVar('T')

_LOGGER: Final = logging.getLogger(__name__)
_LOG_FORMAT: Final = '%(levelname)s %(asctime)s %(name)s - %(message)s'


class KompileTarget(Enum):
    LINUX = 'linux'
    DARWIN = 'darwin'


def _ignore_arg(args: Dict[str, Any], arg: str, cli_option: str) -> None:
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
    definition_dir: Path,
    backend: KompileBackend,
    main_file: Path,
    emit_json: bool,
    kompile_mode: KEVMKompileMode,
    includes: List[str],
    main_module: Optional[str],
    syntax_module: Optional[str],
    ccopts: Iterable[str] = (),
    llvm_kompile: bool = True,
    target: Optional[KompileTarget] = None,
    o0: bool = False,
    o1: bool = False,
    o2: bool = False,
    o3: bool = False,
    debug: bool = False,
    plugin_include: Optional[Path] = None,
    libff_dir: Optional[Path] = None,
    brew_root: Optional[Path] = None,
    libcryptopp_dir: Optional[Path] = None,
    openssl_root: Optional[Path] = None,
    **kwargs: Any,
) -> None:
    _ignore_arg(kwargs, 'md_selector', f'--md-selector {kwargs["md_selector"]}')

    optimization = 0
    if o1:
        optimization = 1
    if o2:
        optimization = 2
    if o3:
        optimization = 3

    md_selector = 'k & ! node'
    if kompile_mode == KEVMKompileMode.NODE:
        md_selector = 'k & ! standalone'

    if backend == KompileBackend.LLVM:
        ccopts = list(ccopts)
        if libff_dir is not None:
            ccopts += [f'-L{libff_dir}/lib', f'-I{libff_dir}/include']
        if plugin_include is not None:
            ccopts += [
                f'{plugin_include}/c/plugin_util.cpp',
                f'{plugin_include}/c/crypto.cpp',
                f'{plugin_include}/c/blake2.cpp',
            ]
        ccopts += ['-g', '-std=c++14', '-lff', '-lcryptopp', '-lsecp256k1', '-lssl', '-lcrypto']
        if target == KompileTarget.DARWIN:
            if brew_root is not None:
                ccopts += [
                    f'-I{brew_root}/include',
                    f'-L{brew_root}/lib',
                ]
            if openssl_root is not None:
                ccopts += [
                    f'-I{openssl_root}/include',
                    f'-L{openssl_root}/lib',
                ]
            if libcryptopp_dir is not None:
                ccopts += [
                    f'-I{libcryptopp_dir}/include',
                    f'-L{libcryptopp_dir}/lib',
                ]
        elif target == KompileTarget.LINUX:
            ccopts += ['-lprocps']

    KEVM.kompile(
        definition_dir,
        backend,
        main_file,
        emit_json=emit_json,
        includes=includes,
        main_module_name=main_module,
        syntax_module_name=syntax_module,
        md_selector=md_selector,
        debug=debug,
        ccopts=ccopts,
        llvm_kompile=llvm_kompile,
        optimization=optimization,
    )


def exec_solc_to_k(
    definition_dir: Path,
    contract_file: Path,
    contract_name: str,
    main_module: Optional[str],
    requires: List[str],
    imports: List[str],
    **kwargs: Any,
) -> None:
    kevm = KEVM(definition_dir)
    empty_config = kevm.definition.empty_config(KEVM.Sorts.KEVM_CELL)
    solc_json = solc_compile(contract_file)
    contract_json = solc_json['contracts'][contract_file.name][contract_name]
    if 'sources' in solc_json and contract_file.name in solc_json['sources']:
        contract_source = solc_json['sources'][contract_file.name]
        for key in ['id', 'ast']:
            if key not in contract_json and key in contract_source:
                contract_json[key] = contract_source[key]
    contract = Contract(contract_name, contract_json, foundry=False)
    contract_module = contract_to_main_module(contract, empty_config, imports=['EDSL'] + imports)
    _main_module = KFlatModule(
        main_module if main_module else 'MAIN', [], [KImport(mname) for mname in [contract_module.name] + imports]
    )
    modules = (contract_module, _main_module)
    bin_runtime_definition = KDefinition(
        _main_module.name, modules, requires=[KRequire(req) for req in ['edsl.md'] + requires]
    )
    _kprint = KEVM(definition_dir, extra_unparsing_modules=modules)
    print(_kprint.pretty_print(bin_runtime_definition) + '\n')


def exec_foundry_kompile(
    definition_dir: Path,
    foundry_root: Path,
    md_selector: Optional[str] = None,
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
    _ignore_arg(kwargs, 'backend', f'--backend {kwargs["backend"]}')
    _ignore_arg(kwargs, 'o0', '-O0')
    _ignore_arg(kwargs, 'o1', '-O1')
    _ignore_arg(kwargs, 'o2', '-O2')
    _ignore_arg(kwargs, 'o3', '-O3')
    foundry_kompile(
        definition_dir=definition_dir,
        foundry_root=foundry_root,
        includes=includes,
        md_selector=md_selector,
        regen=regen,
        rekompile=rekompile,
        requires=requires,
        imports=imports,
        ccopts=ccopts,
        llvm_kompile=llvm_kompile,
        debug=debug,
        llvm_library=llvm_library,
    )


def exec_prove(
    definition_dir: Path,
    spec_file: Path,
    includes: List[str],
    bug_report: bool = False,
    save_directory: Optional[Path] = None,
    spec_module: Optional[str] = None,
    md_selector: Optional[str] = None,
    claim_labels: Iterable[str] = (),
    exclude_claim_labels: Iterable[str] = (),
    max_depth: int = 1000,
    max_iterations: Optional[int] = None,
    workers: int = 1,
    simplify_init: bool = True,
    break_every_step: bool = False,
    break_on_jumpi: bool = False,
    break_on_calls: bool = True,
    implication_every_block: bool = True,
    kore_rpc_command: Union[str, Iterable[str]] = ('kore-rpc',),
    smt_timeout: Optional[int] = None,
    smt_retry_limit: Optional[int] = None,
    **kwargs: Any,
) -> None:
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

    if isinstance(kore_rpc_command, str):
        kore_rpc_command = kore_rpc_command.split()

    _LOGGER.info(f'Converting {len(claims)} KClaims to KCFGs')
    proof_problems = {c.label: AGProof(c.label, KCFG.from_claim(kevm.definition, c)) for c in claims}
    if simplify_init:
        with KCFGExplore(
            kevm,
            bug_report=br,
            kore_rpc_command=kore_rpc_command,
            smt_timeout=smt_timeout,
            smt_retry_limit=smt_retry_limit,
        ) as kcfg_explore:
            proof_problems = {
                claim: AGProof(claim, kcfg_explore.simplify(claim, ag_proof.kcfg))
                for claim, ag_proof in proof_problems.items()
            }

    results = parallel_kcfg_explore(
        kevm,
        proof_problems,
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
    )
    failed = 0
    for pid, r in results.items():
        if r:
            print(f'PROOF PASSED: {pid}')
        else:
            failed += 1
            print(f'PROOF FAILED: {pid}')
    sys.exit(failed)


def exec_show_kcfg(
    definition_dir: Path,
    spec_file: Path,
    save_directory: Optional[Path] = None,
    includes: Iterable[str] = (),
    claim_labels: Iterable[str] = (),
    exclude_claim_labels: Iterable[str] = (),
    spec_module: Optional[str] = None,
    md_selector: Optional[str] = None,
    nodes: Iterable[str] = (),
    node_deltas: Iterable[Tuple[str, str]] = (),
    to_module: bool = False,
    minimize: bool = True,
    **kwargs: Any,
) -> None:
    kevm = KEVM(definition_dir)
    ag_proof = get_ag_proof_for_spec(
        kevm,
        spec_file,
        save_directory=save_directory,
        spec_module_name=spec_module,
        include_dirs=[Path(i) for i in includes],
        md_selector=md_selector,
        claim_labels=claim_labels,
        exclude_claim_labels=exclude_claim_labels,
    )

    kcfg_show = KCFGShow(kevm)
    res_lines = kcfg_show.show(
        ag_proof.id,
        ag_proof.kcfg,
        nodes=nodes,
        node_deltas=node_deltas,
        to_module=to_module,
        minimize=minimize,
        node_printer=kevm.short_info,
    )
    print('\n'.join(res_lines))


def exec_view_kcfg(
    definition_dir: Path,
    spec_file: Path,
    save_directory: Optional[Path] = None,
    includes: Iterable[str] = (),
    claim_labels: Iterable[str] = (),
    exclude_claim_labels: Iterable[str] = (),
    spec_module: Optional[str] = None,
    md_selector: Optional[str] = None,
    **kwargs: Any,
) -> None:
    kevm = KEVM(definition_dir)
    ag_proof = get_ag_proof_for_spec(
        kevm,
        spec_file,
        save_directory=save_directory,
        spec_module_name=spec_module,
        include_dirs=[Path(i) for i in includes],
        md_selector=md_selector,
        claim_labels=claim_labels,
        exclude_claim_labels=exclude_claim_labels,
    )

    viewer = KCFGViewer(ag_proof.kcfg, kevm, node_printer=kevm.short_info)
    viewer.run()


def exec_foundry_prove(
    foundry_root: Path,
    max_depth: int = 1000,
    max_iterations: Optional[int] = None,
    reinit: bool = False,
    tests: Iterable[str] = (),
    exclude_tests: Iterable[str] = (),
    workers: int = 1,
    simplify_init: bool = True,
    break_every_step: bool = False,
    break_on_jumpi: bool = False,
    break_on_calls: bool = True,
    implication_every_block: bool = True,
    bug_report: bool = False,
    kore_rpc_command: Union[str, Iterable[str]] = ('kore-rpc',),
    smt_timeout: Optional[int] = None,
    smt_retry_limit: Optional[int] = None,
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
        bug_report=bug_report,
        kore_rpc_command=kore_rpc_command,
        smt_timeout=smt_timeout,
        smt_retry_limit=smt_retry_limit,
    )
    failed = 0
    for pid, r in results.items():
        if r:
            print(f'PROOF PASSED: {pid}')
        else:
            failed += 1
            print(f'PROOF FAILED: {pid}')
    sys.exit(failed)


def exec_foundry_show(
    foundry_root: Path,
    test: str,
    nodes: Iterable[str] = (),
    node_deltas: Iterable[Tuple[str, str]] = (),
    to_module: bool = False,
    minimize: bool = True,
    **kwargs: Any,
) -> None:
    output = foundry_show(
        foundry_root=foundry_root,
        test=test,
        nodes=nodes,
        node_deltas=node_deltas,
        to_module=to_module,
        minimize=minimize,
    )
    print(output)


def exec_foundry_to_dot(foundry_root: Path, test: str, **kwargs: Any) -> None:
    foundry_to_dot(foundry_root=foundry_root, test=test)


def exec_foundry_list(foundry_root: Path, details: bool = True, **kwargs: Any) -> None:
    stats = foundry_list(foundry_root=foundry_root)
    delim = '\n\n' if details else '\n'
    output = delim.join(stat.pretty(details=details) for stat in stats)
    print(output)


def exec_run(
    definition_dir: Path,
    input_file: Path,
    term: bool,
    parser: Optional[str],
    expand_macros: str,
    depth: Optional[int],
    output: str,
    **kwargs: Any,
) -> None:
    krun_result = _krun(
        definition_dir=Path(definition_dir),
        input_file=Path(input_file),
        depth=depth,
        term=term,
        no_expand_macros=not expand_macros,
        parser=parser,
        output=KRunOutput[output.upper()],
    )
    print(krun_result.stdout)
    sys.exit(krun_result.returncode)


def exec_foundry_view_kcfg(foundry_root: Path, test: str, **kwargs: Any) -> None:
    foundry = Foundry(foundry_root)
    ag_proofs_dir = foundry.out / 'ag_proofs'
    contract_name = test.split('.')[0]

    ag_proof = AGProof.read_proof(test, ag_proofs_dir)
    assert type(ag_proof) is AGProof

    def _short_info(cterm: CTerm) -> Iterable[str]:
        return foundry.short_info_for_contract(contract_name, cterm)

    def _custom_view(elem: KCFGElem) -> Iterable[str]:
        return foundry.custom_view(contract_name, elem)

    viewer = KCFGViewer(ag_proof.kcfg, foundry.kevm, node_printer=_short_info, custom_view=_custom_view)
    viewer.run()


def exec_foundry_remove_node(foundry_root: Path, test: str, node: str, **kwargs: Any) -> None:
    foundry_remove_node(foundry_root=foundry_root, test=test, node=node)


def exec_foundry_simplify_node(
    foundry_root: Path,
    test: str,
    node: str,
    replace: bool = False,
    minimize: bool = True,
    bug_report: bool = False,
    smt_timeout: Optional[int] = None,
    smt_retry_limit: Optional[int] = None,
    **kwargs: Any,
) -> None:
    pretty_term = foundry_simplify_node(
        foundry_root=foundry_root,
        test=test,
        node=node,
        replace=replace,
        minimize=minimize,
        bug_report=bug_report,
        smt_timeout=smt_timeout,
        smt_retry_limit=smt_retry_limit,
    )
    print(f'Simplified:\n{pretty_term}')


def exec_foundry_step_node(
    foundry_root: Path,
    test: str,
    node: str,
    repeat: int = 1,
    depth: int = 1,
    bug_report: bool = False,
    smt_timeout: Optional[int] = None,
    smt_retry_limit: Optional[int] = None,
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
    )


def exec_foundry_section_edge(
    foundry_root: Path,
    test: str,
    edge: Tuple[str, str],
    sections: int = 2,
    replace: bool = False,
    bug_report: bool = False,
    smt_timeout: Optional[int] = None,
    smt_retry_limit: Optional[int] = None,
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
    )


# Helpers


def _create_argument_parser() -> ArgumentParser:
    def list_of(elem_type: Callable[[str], T], delim: str = ';') -> Callable[[str], List[T]]:
        def parse(s: str) -> List[T]:
            return [elem_type(elem) for elem in s.split(delim)]

        return parse

    shared_args = ArgumentParser(add_help=False)
    shared_args.add_argument('--verbose', '-v', default=False, action='store_true', help='Verbose output.')
    shared_args.add_argument('--debug', default=False, action='store_true', help='Debug output.')
    shared_args.add_argument('--workers', '-j', default=1, type=int, help='Number of processes to run in parallel.')

    display_args = ArgumentParser(add_help=False)
    display_args.add_argument('--minimize', dest='minimize', default=True, action='store_true', help='Minimize output.')
    display_args.add_argument('--no-minimize', dest='minimize', action='store_false', help='Do not minimize output.')

    foundry_root_arg = ArgumentParser(add_help=False)
    foundry_root_arg.add_argument(
        '--foundry-project-root',
        dest='foundry_root',
        type=dir_path,
        default=Path('.'),
        help='Path to Foundry project root directory.',
    )

    rpc_args = ArgumentParser(add_help=False)
    rpc_args.add_argument(
        '--bug-report',
        default=False,
        action='store_true',
        help='Generate a haskell-backend bug report for the execution.',
    )

    smt_args = ArgumentParser(add_help=False)
    smt_args.add_argument(
        '--smt-timeout', dest='smt_timeout', type=int, default=125, help='Timeout in ms to use for SMT queries.'
    )
    smt_args.add_argument(
        '--smt-retry-limit',
        dest='smt_retry_limit',
        type=int,
        default=4,
        help='Number of times to retry SMT queries with scaling timeouts.',
    )

    explore_args = ArgumentParser(add_help=False)
    explore_args.add_argument(
        '--break-every-step',
        dest='break_every_step',
        default=False,
        action='store_true',
        help='Store a node for every EVM opcode step (expensive).',
    )
    explore_args.add_argument(
        '--break-on-jumpi',
        dest='break_on_jumpi',
        default=False,
        action='store_true',
        help='Store a node for every EVM jump opcode.',
    )
    explore_args.add_argument(
        '--break-on-calls',
        dest='break_on_calls',
        default=True,
        action='store_true',
        help='Store a node for every EVM call made.',
    )
    explore_args.add_argument(
        '--no-break-on-calls',
        dest='break_on_calls',
        action='store_false',
        help='Do not store a node for every EVM call made.',
    )
    explore_args.add_argument(
        '--implication-every-block',
        dest='implication_every_block',
        default=True,
        action='store_true',
        help='Check subsumption into target state every basic block, not just at terminal nodes.',
    )
    explore_args.add_argument(
        '--no-implication-every-block',
        dest='implication_every_block',
        action='store_false',
        help='Do not check subsumption into target state every basic block, not just at terminal nodes.',
    )
    explore_args.add_argument(
        '--simplify-init',
        dest='simplify_init',
        default=True,
        action='store_true',
        help='Simplify the initial and target states at startup.',
    )
    explore_args.add_argument(
        '--no-simplify-init',
        dest='simplify_init',
        action='store_false',
        help='Do not simplify the initial and target states at startup.',
    )
    explore_args.add_argument(
        '--max-depth',
        dest='max_depth',
        default=1000,
        type=int,
        help='Store every Nth state in the CFG for inspection.',
    )
    explore_args.add_argument(
        '--max-iterations',
        dest='max_iterations',
        default=None,
        type=int,
        help='Store every Nth state in the CFG for inspection.',
    )
    explore_args.add_argument(
        '--kore-rpc-command',
        dest='kore_rpc_command',
        type=str,
        default='kore-rpc',
        help='Custom command to start RPC server',
    )

    k_args = ArgumentParser(add_help=False)
    k_args.add_argument('--depth', default=None, type=int, help='Maximum depth to execute to.')
    k_args.add_argument(
        '-I', type=str, dest='includes', default=[], action='append', help='Directories to lookup K definitions in.'
    )
    k_args.add_argument('--main-module', default=None, type=str, help='Name of the main module.')
    k_args.add_argument('--syntax-module', default=None, type=str, help='Name of the syntax module.')
    k_args.add_argument('--spec-module', default=None, type=str, help='Name of the spec module.')
    k_args.add_argument('--definition', type=str, dest='definition_dir', help='Path to definition to use.')
    k_args.add_argument(
        '--md-selector',
        type=str,
        help='Code selector expression to use when reading markdown.',
    )

    kprove_args = ArgumentParser(add_help=False)
    kprove_args.add_argument(
        '--debug-equations', type=list_of(str, delim=','), default=[], help='Comma-separate list of equations to debug.'
    )

    k_kompile_args = ArgumentParser(add_help=False)
    k_kompile_args.add_argument('--backend', type=KompileBackend, help='[llvm|haskell]')
    k_kompile_args.add_argument(
        '--emit-json',
        dest='emit_json',
        default=True,
        action='store_true',
        help='Emit JSON definition after compilation.',
    )
    k_kompile_args.add_argument(
        '--no-emit-json', dest='emit_json', action='store_false', help='Do not JSON definition after compilation.'
    )
    k_kompile_args.add_argument(
        '-ccopt',
        dest='ccopts',
        default=[],
        action='append',
        help='Additional arguments to pass to llvm-kompile.',
    )
    k_kompile_args.add_argument(
        '--no-llvm-kompile',
        dest='llvm_kompile',
        default=True,
        action='store_false',
        help='Do not run llvm-kompile process.',
    )
    k_kompile_args.add_argument(
        '--with-llvm-library',
        dest='llvm_library',
        default=False,
        action='store_true',
        help='Make kompile generate a dynamic llvm library.',
    )
    k_kompile_args.add_argument('-O0', dest='o0', default=False, action='store_true', help='Optimization level 0.')
    k_kompile_args.add_argument('-O1', dest='o1', default=False, action='store_true', help='Optimization level 1.')
    k_kompile_args.add_argument('-O2', dest='o2', default=False, action='store_true', help='Optimization level 2.')
    k_kompile_args.add_argument('-O3', dest='o3', default=False, action='store_true', help='Optimization level 3.')

    evm_chain_args = ArgumentParser(add_help=False)
    evm_chain_args.add_argument(
        '--schedule',
        type=str,
        default='LONDON',
        help='KEVM Schedule to use for execution. One of [DEFAULT|FRONTIER|HOMESTEAD|TANGERINE_WHISTLE|SPURIOUS_DRAGON|BYZANTIUM|CONSTANTINOPLE|PETERSBURG|ISTANBUL|BERLIN|LONDON].',
    )
    evm_chain_args.add_argument('--chainid', type=int, default=1, help='Chain ID to use for execution.')
    evm_chain_args.add_argument(
        '--mode', type=str, default='NORMAL', help='Execution mode to use. One of [NORMAL|VMTESTS].'
    )

    k_gen_args = ArgumentParser(add_help=False)
    k_gen_args.add_argument(
        '--require',
        dest='requires',
        default=[],
        action='append',
        help='Extra K requires to include in generated output.',
    )
    k_gen_args.add_argument(
        '--module-import',
        dest='imports',
        default=[],
        action='append',
        help='Extra modules to import into generated main module.',
    )

    spec_args = ArgumentParser(add_help=False)
    spec_args.add_argument('spec_file', type=file_path, help='Path to spec file.')
    spec_args.add_argument('--save-directory', type=ensure_dir_path, help='Path to where CFGs are stored.')
    spec_args.add_argument(
        '--claim', type=str, dest='claim_labels', action='append', help='Only prove listed claims, MODULE_NAME.claim-id'
    )
    spec_args.add_argument(
        '--exclude-claim',
        type=str,
        dest='exclude_claim_labels',
        action='append',
        help='Skip listed claims, MODULE_NAME.claim-id',
    )

    kcfg_show_args = ArgumentParser(add_help=False)
    kcfg_show_args.add_argument(
        '--node',
        type=str,
        dest='nodes',
        default=[],
        action='append',
        help='List of nodes to display as well.',
    )
    kcfg_show_args.add_argument(
        '--node-delta',
        type=arg_pair_of(str, str),
        dest='node_deltas',
        default=[],
        action='append',
        help='List of nodes to display delta for.',
    )
    kcfg_show_args.add_argument(
        '--to-module', dest='to_module', default=False, action='store_true', help='Output edges as a K module.'
    )

    parser = ArgumentParser(prog='python3 -m kevm_pyk')

    command_parser = parser.add_subparsers(dest='command', required=True)

    kompile_args = command_parser.add_parser(
        'kompile', help='Kompile KEVM specification.', parents=[shared_args, k_args, k_kompile_args]
    )
    kompile_args.add_argument('main_file', type=file_path, help='Path to file with main module.')
    kompile_args.add_argument(
        '--kompile-mode',
        type=KEVMKompileMode,
        default=KEVMKompileMode.STANDALONE,
        help='KEVM kompile mode, [standalone|node].',
    )
    kompile_args.add_argument('--plugin-include', type=dir_path, help='Path to plugin include directory.')
    kompile_args.add_argument('--libff-dir', type=dir_path, help='Path to libff include directory.')
    kompile_args.add_argument(
        '--target', type=KompileTarget, default=KompileTarget.LINUX, help='Compilation target, [linux|darwin].'
    )
    kompile_args.add_argument('--libcryptopp-dir', type=dir_path, help='Path to libcryptopp include directory.')
    kompile_args.add_argument(
        '--brew-root', type=dir_path, help='Path to homebrew root directory (only for --target-darwin).'
    )
    kompile_args.add_argument(
        '--openssl-root', type=dir_path, help='Path to openssl root directory (only for --target-darwin).'
    )

    _ = command_parser.add_parser(
        'prove',
        help='Run KEVM proof.',
        parents=[shared_args, k_args, kprove_args, rpc_args, smt_args, explore_args, spec_args],
    )

    _ = command_parser.add_parser(
        'view-kcfg',
        help='Display tree view of CFG',
        parents=[shared_args, k_args, spec_args],
    )

    _ = command_parser.add_parser(
        'show-kcfg',
        help='Display tree show of CFG',
        parents=[shared_args, k_args, kcfg_show_args, spec_args, display_args],
    )

    run_args = command_parser.add_parser(
        'run', help='Run KEVM test/simulation.', parents=[shared_args, evm_chain_args, k_args]
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
        parents=[shared_args, k_args, k_gen_args],
    )
    solc_to_k_args.add_argument('contract_file', type=file_path, help='Path to contract file.')
    solc_to_k_args.add_argument('contract_name', type=str, help='Name of contract to generate K helpers for.')

    foundry_kompile = command_parser.add_parser(
        'foundry-kompile',
        help='Kompile K definition corresponding to given output directory.',
        parents=[shared_args, k_args, k_gen_args, k_kompile_args, foundry_root_arg],
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
        parents=[shared_args, k_args, kprove_args, smt_args, rpc_args, explore_args, foundry_root_arg],
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

    foundry_show_args = command_parser.add_parser(
        'foundry-show',
        help='Display a given Foundry CFG.',
        parents=[shared_args, k_args, kcfg_show_args, display_args, foundry_root_arg],
    )
    foundry_show_args.add_argument('test', type=str, help='Display the CFG for this test.')

    foundry_to_dot = command_parser.add_parser(
        'foundry-to-dot',
        help='Dump the given CFG for the test as DOT for visualization.',
        parents=[shared_args, foundry_root_arg],
    )
    foundry_to_dot.add_argument('test', type=str, help='Display the CFG for this test.')

    foundry_list_args = command_parser.add_parser(
        'foundry-list',
        help='List information about CFGs on disk',
        parents=[shared_args, k_args, foundry_root_arg],
    )
    foundry_list_args.add_argument(
        '--details', dest='details', default=True, action='store_true', help='Information about progress on each CFG.'
    )
    foundry_list_args.add_argument('--no-details', dest='details', action='store_false', help='Just list the CFGs.')

    foundry_view_kcfg_args = command_parser.add_parser(
        'foundry-view-kcfg',
        help='Display tree view of CFG',
        parents=[shared_args, foundry_root_arg],
    )
    foundry_view_kcfg_args.add_argument('test', type=str, help='View the CFG for this test.')

    foundry_remove_node = command_parser.add_parser(
        'foundry-remove-node',
        help='Remove a node and its successors.',
        parents=[shared_args, foundry_root_arg],
    )
    foundry_remove_node.add_argument('test', type=str, help='View the CFG for this test.')
    foundry_remove_node.add_argument('node', type=str, help='Node to remove CFG subgraph from.')

    foundry_simplify_node = command_parser.add_parser(
        'foundry-simplify-node',
        help='Simplify a given node, and potentially replace it.',
        parents=[shared_args, smt_args, rpc_args, display_args, foundry_root_arg],
    )
    foundry_simplify_node.add_argument('test', type=str, help='Simplify node in this CFG.')
    foundry_simplify_node.add_argument('node', type=str, help='Node to simplify in CFG.')
    foundry_simplify_node.add_argument(
        '--replace', default=False, help='Replace the original node with the simplified variant in the graph.'
    )

    foundry_step_node = command_parser.add_parser(
        'foundry-step-node',
        help='Step from a given node, adding it to the CFG.',
        parents=[shared_args, rpc_args, smt_args, foundry_root_arg],
    )
    foundry_step_node.add_argument('test', type=str, help='Step from node in this CFG.')
    foundry_step_node.add_argument('node', type=str, help='Node to step from in CFG.')
    foundry_step_node.add_argument(
        '--repeat', type=int, default=1, help='How many node expansions to do from the given start node (>= 1).'
    )
    foundry_step_node.add_argument(
        '--depth', type=int, default=1, help='How many steps to take from initial node on edge.'
    )

    foundry_section_edge = command_parser.add_parser(
        'foundry-section-edge',
        help='Given an edge in the graph, cut it into sections to get intermediate nodes.',
        parents=[shared_args, rpc_args, smt_args, foundry_root_arg],
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
