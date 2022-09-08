import glob
import json
import logging
import sys
from argparse import ArgumentParser, Namespace
from pathlib import Path
from typing import Any, Dict, Final, Iterable, List, Optional, TextIO

from pyk.cli_utils import dir_path, file_path
from pyk.kast import KDefinition, KFlatModule, KImport, KRequire, KSort
from pyk.ktool.krun import _krun

from .gst_to_kore import gst_to_kore
from .kevm import KEVM
from .solc_to_k import Contract, contract_to_k, solc_compile
from .utils import KPrint_make_unparsing, add_include_arg

_LOGGER: Final = logging.getLogger(__name__)
_LOG_FORMAT: Final = '%(levelname)s %(asctime)s %(name)s - %(message)s'


def _ignore_arg(args: Dict[str, Any], arg: str, cli_option: str) -> None:
    if arg in args:
        if args[arg] is not None:
            _LOGGER.warning(f'Ignoring command-line option: {cli_option}')
        args.pop(arg)


def main():
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


def exec_compile(contract_file: Path, profile: bool, **kwargs) -> None:
    res = solc_compile(contract_file, profile=profile)
    print(json.dumps(res))


def exec_gst_to_kore(input_file: Path, schedule: str, mode: str, chainid: int, **kwargs) -> None:
    gst_to_kore(input_file, sys.stdout, schedule, mode, chainid)


def exec_kompile(
    definition_dir: Path,
    profile: bool,
    main_file: Path,
    emit_json: bool,
    includes: List[str],
    main_module: Optional[str],
    syntax_module: Optional[str],
    md_selector: Optional[str],
    hook_namespaces: Optional[str],
    **kwargs,
) -> None:
    KEVM.kompile(
        definition_dir,
        main_file,
        emit_json=emit_json,
        includes=includes,
        main_module_name=main_module,
        syntax_module_name=syntax_module,
        md_selector=md_selector,
        hook_namespaces=hook_namespaces.split(' ') if hook_namespaces is not None else None,
        profile=profile,
    )


def exec_solc_to_k(
    definition_dir: Path,
    profile: bool,
    contract_file: Path,
    contract_name: str,
    main_module: Optional[str],
    spec_module: Optional[str],
    requires: List[str],
    imports: List[str],
    exclude_tests: Optional[Path],
    **kwargs,
) -> None:
    kevm = KEVM(definition_dir, profile=profile)
    empty_config = kevm.definition.empty_config(KSort('KevmCell'))
    solc_json = solc_compile(contract_file, profile=profile)
    contract_json = solc_json['contracts'][contract_file.name][contract_name]
    _exclude_tests = []
    if exclude_tests and exclude_tests.exists():
        with open(exclude_tests, 'r') as el:
            _exclude_tests = el.read().strip().split('\n')
    contract = Contract(contract_name, contract_json, foundry=False)
    contract_module, contract_claims_module = contract_to_k(
        contract, empty_config, foundry=False, exclude_tests=_exclude_tests, imports=imports
    )
    modules = [contract_module]
    claims_modules = [contract_claims_module] if contract_claims_module else []
    _main_module = KFlatModule(
        main_module if main_module else 'MAIN', [], [KImport(mname) for mname in [_m.name for _m in modules] + imports]
    )
    _spec_module = KFlatModule(
        spec_module if spec_module else 'SPEC', [], [KImport(mname) for mname in [_m.name for _m in claims_modules]]
    )
    modules.append(_main_module)
    modules.append(_spec_module)
    bin_runtime_definition = KDefinition(
        _main_module.name, modules + claims_modules, requires=[KRequire(req) for req in ['edsl.md'] + requires]
    )
    _kprint = KPrint_make_unparsing(kevm, extra_modules=modules)
    KEVM._patch_symbol_table(_kprint.symbol_table)
    print(_kprint.pretty_print(bin_runtime_definition) + '\n')


def exec_foundry_to_k(
    definition_dir: Path,
    profile: bool,
    foundry_out: Path,
    main_module: Optional[str],
    spec_module: Optional[str],
    requires: List[str],
    imports: List[str],
    exclude_tests: Optional[Path],
    output: Optional[TextIO],
    **kwargs,
) -> None:
    kevm = KEVM(definition_dir, profile=profile)
    empty_config = kevm.definition.empty_config(KSort('KevmCell'))
    path_glob = str(foundry_out) + '/*.t.sol/*.json'
    modules: List[KFlatModule] = []
    claims_modules: List[KFlatModule] = []
    _exclude_tests = []
    if exclude_tests and exclude_tests.exists():
        with open(exclude_tests, 'r') as el:
            _exclude_tests = el.read().strip().split('\n')
    # Must sort to get consistent output order on different platforms.
    for json_file in sorted(glob.glob(path_glob)):
        if json_file.endswith('.metadata.json'):
            continue
        _LOGGER.info(f'Processing contract file: {json_file}')
        contract_name = json_file.split('/')[-1]
        contract_name = contract_name[0:-5] if contract_name.endswith('.json') else contract_name
        with open(json_file, 'r') as cjson:
            contract_json = json.loads(cjson.read())
            contract = Contract(contract_name, contract_json, foundry=True)
            module, claims_module = contract_to_k(
                contract,
                empty_config,
                foundry=True,
                exclude_tests=_exclude_tests,
                imports=imports,
                main_module=main_module,
            )
            _LOGGER.info(f'Produced contract module: {module.name}')
            modules.append(module)
            if claims_module:
                _LOGGER.info(f'Produced claim module: {claims_module.name}')
                claims_modules.append(claims_module)
    _main_module = KFlatModule(
        main_module if main_module else 'MAIN', [], [KImport(mname) for mname in [_m.name for _m in modules] + imports]
    )
    _spec_module = KFlatModule(
        spec_module if spec_module else 'SPEC', [], [KImport(mname) for mname in [_m.name for _m in claims_modules]]
    )
    modules.append(_main_module)
    modules.append(_spec_module)
    bin_runtime_definition = KDefinition(
        _main_module.name,
        modules + claims_modules,
        requires=[KRequire(req) for req in ['edsl.md'] + requires],
    )
    _kprint = KPrint_make_unparsing(kevm, extra_modules=modules)
    KEVM._patch_symbol_table(_kprint.symbol_table)
    if not output:
        output = sys.stdout
    output.write(_kprint.pretty_print(bin_runtime_definition) + '\n')
    output.flush()


def exec_foundry_kompile(
    definition_dir: Path,
    profile: bool,
    foundry_out: Path,
    exclude_tests: Optional[Path],
    includes: List[str],
    md_selector: Optional[str],
    hook_namespaces: Optional[str],
    regen: bool = False,
    rekompile: bool = False,
    requires: Iterable[str] = (),
    imports: Iterable[str] = (),
    **kwargs,
) -> None:
    _ignore_arg(kwargs, 'main_module', f'--main-module {kwargs["main_module"]}')
    _ignore_arg(kwargs, 'syntax_module', f'--syntax-module {kwargs["syntax_module"]}')
    _ignore_arg(kwargs, 'spec_module', f'--spec-module {kwargs["spec_module"]}')
    main_module = 'FOUNDRY-MAIN'
    syntax_module = 'FOUNDRY-MAIN'
    spec_module = 'FOUNDRY-SPEC'
    foundry_definition_dir = foundry_out / 'kompiled'
    foundry_main_file = foundry_definition_dir / 'foundry.k'
    if not foundry_definition_dir.exists():
        foundry_definition_dir.mkdir()
    if regen or not foundry_main_file.exists():
        with open(foundry_main_file, 'w') as fmf:
            exec_foundry_to_k(
                definition_dir=definition_dir,
                profile=profile,
                foundry_out=foundry_out,
                main_module=main_module,
                spec_module=spec_module,
                requires=list(requires),
                imports=list(imports),
                exclude_tests=exclude_tests,
                output=fmf,
            )
    if regen or rekompile or not (foundry_definition_dir / 'timestamp').exists():
        KEVM.kompile(
            foundry_definition_dir,
            foundry_main_file,
            emit_json=True,
            includes=includes,
            main_module_name=main_module,
            syntax_module_name=syntax_module,
            md_selector=md_selector,
            hook_namespaces=hook_namespaces.split(' ') if hook_namespaces is not None else None,
            profile=profile,
        )


def exec_prove(
    definition_dir: Path,
    profile: bool,
    spec_file: Path,
    includes: List[str],
    debug_equations: List[str],
    bug_report: bool,
    spec_module: Optional[str],
    depth: Optional[int],
    **kwargs,
) -> None:
    kevm = KEVM(definition_dir, profile=profile)
    prove_args = add_include_arg(includes)
    haskell_args = []
    for de in debug_equations:
        haskell_args += ['--debug-equation', de]
    if bug_report:
        haskell_args += ['--bug-report', str(spec_file.with_suffix(''))]
    if depth is not None:
        prove_args += ['--depth', str(depth)]
    final_state = kevm.prove(spec_file, spec_module_name=spec_module, args=prove_args, haskell_args=haskell_args)
    print(kevm.pretty_print(final_state) + '\n')


def exec_foundry_prove(
    profile: bool,
    foundry_out: Path,
    contract: Optional[str],
    includes: List[str],
    debug_equations: List[str],
    bug_report: bool,
    spec_module: Optional[str],
    depth: Optional[int],
    **kwargs,
) -> None:
    _ignore_arg(kwargs, 'main_module', f'--main-module: {kwargs["main_module"]}')
    _ignore_arg(kwargs, 'syntax_module', f'--syntax-module: {kwargs["syntax_module"]}')
    _ignore_arg(kwargs, 'definition_dir', f'--definition: {kwargs["definition_dir"]}')
    definition_dir = foundry_out / 'kompiled'
    spec_file = definition_dir / 'foundry.k'
    spec_module = contract.upper() + '-BIN-RUNTIME-SPEC' if contract else 'FOUNDRY-SPEC'
    exec_prove(
        definition_dir,
        profile,
        spec_file,
        includes=includes,
        debug_equations=debug_equations,
        bug_report=bug_report,
        depth=depth,
        spec_module=spec_module,
        **kwargs,
    )


def exec_run(
    definition_dir: Path,
    profile: bool,
    input_file: Path,
    term: bool,
    parser: Optional[str],
    expand_macros: str,
    depth: Optional[int],
    output: str,
    **kwargs,
) -> None:
    kevm = KEVM(definition_dir, profile=profile)
    krun_args = []
    if term:
        krun_args += ['--term']
    if parser is not None:
        krun_args += ['--parser', parser]
    if not expand_macros:
        krun_args += ['--no-expand-macros']
    # TODO: These are inlined into _krun
    krun_args += ['--output', output]
    krun_result = _krun(kevm.definition_dir, Path(input_file), depth=depth, args=krun_args, profile=profile)
    print(krun_result.stdout)
    sys.exit(krun_result.returncode)


# Helpers


def _create_argument_parser() -> ArgumentParser:
    def list_of(elem_type, delim=';'):
        def parse(s):
            return [elem_type(elem) for elem in s.split(delim)]

        return parse

    shared_args = ArgumentParser(add_help=False)
    shared_args.add_argument('--verbose', '-v', default=False, action='store_true', help='Verbose output.')
    shared_args.add_argument('--debug', default=False, action='store_true', help='Debug output.')
    shared_args.add_argument('--profile', default=False, action='store_true', help='Coarse process-level profiling.')

    k_args = ArgumentParser(add_help=False)
    k_args.add_argument('--depth', default=None, type=int, help='Maximum depth to execute to.')
    k_args.add_argument(
        '-I', type=str, dest='includes', default=[], action='append', help='Directories to lookup K definitions in.'
    )
    k_args.add_argument('--main-module', default=None, type=str, help='Name of the main module.')
    k_args.add_argument('--syntax-module', default=None, type=str, help='Name of the syntax module.')
    k_args.add_argument('--spec-module', default=None, type=str, help='Name of the spec module.')
    k_args.add_argument('--definition', type=str, dest='definition_dir', help='Path to definition to use.')

    kprove_args = ArgumentParser(add_help=False)
    kprove_args.add_argument(
        '--debug-equations', type=list_of(str, delim=','), default=[], help='Comma-separate list of equations to debug.'
    )
    kprove_args.add_argument(
        '--bug-report',
        default=False,
        action='store_true',
        help='Generate a haskell-backend bug report for the execution.',
    )

    k_kompile_args = ArgumentParser(add_help=False)
    k_kompile_args.add_argument(
        '--md-selector',
        type=str,
        default='k & ! nobytes & ! node',
        help='Code selector expression to use when reading markdown.',
    )
    k_kompile_args.add_argument('--hook-namespaces', type=str, help='Hook namespaces. What more can I say?')
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
    k_gen_args.add_argument(
        '--exclude-tests',
        type=file_path,
        help='File containing, one per line, tests to exclude as CONTRACT_NAME.TEST_NAME.',
    )

    parser = ArgumentParser(prog='python3 -m kevm_pyk')

    command_parser = parser.add_subparsers(dest='command', required=True)

    kompile_args = command_parser.add_parser(
        'kompile', help='Kompile KEVM specification.', parents=[shared_args, k_args, k_kompile_args]
    )
    kompile_args.add_argument('main_file', type=file_path, help='Path to file with main module.')

    prove_args = command_parser.add_parser('prove', help='Run KEVM proof.', parents=[shared_args, k_args, kprove_args])
    prove_args.add_argument('spec_file', type=file_path, help='Path to spec file.')

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

    gst_to_kore_args = command_parser.add_parser(
        'gst-to-kore',
        help='Convert a GeneralStateTest to Kore for compsumption by KEVM.',
        parents=[shared_args, evm_chain_args],
    )
    gst_to_kore_args.add_argument('input_file', type=file_path, help='Path to GST.')

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
        parents=[shared_args, k_args, k_gen_args, k_kompile_args],
    )
    foundry_kompile.add_argument('foundry_out', type=dir_path, help='Path to Foundry output directory.')
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
        parents=[shared_args, k_args, kprove_args],
    )
    foundry_prove_args.add_argument('foundry_out', type=dir_path, help='Path to Foundry output directory.')
    foundry_prove_args.add_argument(
        '--contract', default=None, type=str, help='Limit to only proofs for the named contract.'
    )

    return parser


def _loglevel(args: Namespace) -> int:
    if args.verbose or args.profile:
        return logging.INFO

    if args.debug:
        return logging.DEBUG

    return logging.WARNING


if __name__ == "__main__":
    main()
