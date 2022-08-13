import argparse
import glob
import json
import logging
import sys
from pathlib import Path
from typing import Final, List

from pyk.cli_utils import dir_path, file_path
from pyk.kast import KDefinition, KFlatModule, KImport, KRequire, KSort
from pyk.ktool.krun import _krun

from .gst_to_kore import gst_to_kore
from .kevm import KEVM
from .solc_to_k import Contract, contract_to_k, solc_compile
from .utils import KPrint_make_unparsing, add_include_arg

_LOGGER: Final = logging.getLogger(__name__)
_LOG_FORMAT: Final = '%(levelname)s %(asctime)s %(name)s - %(message)s'


def main():

    sys.setrecursionlimit(15000000)
    parser = create_argument_parser()
    args = parser.parse_args()

    if not (args.verbose or args.profile or args.debug):
        logging.basicConfig(level=logging.WARNING, format=_LOG_FORMAT)
    if args.verbose or args.profile:
        logging.basicConfig(level=logging.INFO, format=_LOG_FORMAT)
    if args.debug:
        logging.basicConfig(level=logging.DEBUG, format=_LOG_FORMAT)

    if args.command == 'compile':
        res = solc_compile(args.contract_file, profile=args.profile)
        print(json.dumps(res))

    elif args.command == 'gst-to-kore':
        gst_to_kore(args.input_file, sys.stdout, args.schedule, args.mode, args.chainid)

    elif args.command in {'solc-to-k', 'foundry-to-k', 'kompile', 'prove', 'run'}:

        if 'definition_dir' not in args:
            raise ValueError(f'Must provide --definition argument to {args.command}!')

        if args.command == 'kompile':
            kevm = KEVM.kompile(
                args.definition_dir,
                args.main_file,
                emit_json=args.emit_json,
                includes=args.includes,
                main_module_name=args.main_module,
                syntax_module_name=args.syntax_module,
                md_selector=args.md_selector,
                hook_namespaces=args.hook_namespaces.split(' '),
                concrete_rules_file=args.concrete_rules_file,
                profile=args.profile,
            )

        else:
            kevm = KEVM(args.definition_dir, profile=args.profile)
            empty_config = kevm.definition.empty_config(KSort('KevmCell'))

            if args.command == 'solc-to-k':
                solc_json = solc_compile(args.contract_file, profile=args.profile)
                contract_json = solc_json['contracts'][args.contract_file.name][args.contract_name]
                exclude_tests = []
                if args.exclude_tests and args.exclude_tests.exists():
                    with open(args.exclude_tests, 'r') as el:
                        exclude_tests = el.read().strip().split('\n')
                contract = Contract(args.contract_name, contract_json, foundry=False, exclude_tests=exclude_tests)
                contract_module, contract_claims_module = contract_to_k(contract, empty_config)
                modules = [contract_module]
                claims_modules = [contract_claims_module] if contract_claims_module else []
                main_module = KFlatModule(args.main_module, [], [KImport(mname) for mname in [_m.name for _m in modules] + args.imports])
                spec_module = KFlatModule(args.spec_module, [], [KImport(mname) for mname in [_m.name for _m in claims_modules]])
                modules.append(main_module)
                modules.append(spec_module)
                bin_runtime_definition = KDefinition(args.main_module, modules + claims_modules, requires=[KRequire(req) for req in ['edsl.md'] + args.requires])
                _kprint = KPrint_make_unparsing(kevm, extra_modules=modules)
                KEVM._patch_symbol_table(_kprint.symbol_table)
                print(_kprint.pretty_print(bin_runtime_definition) + '\n')

            elif args.command == 'foundry-to-k':
                path_glob = str(args.out) + '/*.t.sol/*.json'
                modules: List[KFlatModule] = []
                claims_modules: List[KFlatModule] = []
                exclude_tests = []
                if args.exclude_tests and args.exclude_tests.exists():
                    with open(args.exclude_tests, 'r') as el:
                        exclude_tests = el.read().strip().split('\n')
                # Must sort to get consistent output order on different platforms.
                for json_file in sorted(glob.glob(path_glob)):
                    _LOGGER.info(f'Processing contract file: {json_file}')
                    contract_name = json_file.split('/')[-1]
                    contract_name = contract_name[0:-5] if contract_name.endswith('.json') else contract_name
                    with open(json_file, 'r') as cjson:
                        contract_json = json.loads(cjson.read())
                        contract = Contract(contract_name, contract_json, foundry=True, exclude_tests=exclude_tests)
                        module, claims_module = contract_to_k(contract, empty_config, foundry=True)
                        _LOGGER.info(f'Produced contract module: {module.name}')
                        modules.append(module)
                        if claims_module:
                            claims_modules.append(claims_module)
                main_module = KFlatModule(args.main_module, [], [KImport(mname) for mname in [_m.name for _m in modules] + args.imports])
                spec_module = KFlatModule(args.spec_module, [], [KImport(mname) for mname in [_m.name for _m in claims_modules]])
                modules.append(main_module)
                modules.append(spec_module)
                bin_runtime_definition = KDefinition(main_module.name, modules + claims_modules, requires=[KRequire(req) for req in ['edsl.md', 'lemmas/int-simplification.k', 'lemmas/lemmas.k'] + args.requires])
                _kprint = KPrint_make_unparsing(kevm, extra_modules=modules)
                KEVM._patch_symbol_table(_kprint.symbol_table)
                print(_kprint.pretty_print(bin_runtime_definition) + '\n')

            elif args.command == 'prove':
                spec_file = args.spec_file
                spec_module = args.spec_module
                prove_args = add_include_arg(args.includes)
                haskell_args = []
                for de in args.debug_equations:
                    haskell_args += ['--debug-equation', de]
                if args.bug_report:
                    haskell_args += ['--bug-report', str(spec_file.with_suffix(''))]
                final_state = kevm.prove(spec_file, spec_module_name=spec_module, args=prove_args, haskell_args=haskell_args)
                print(kevm.pretty_print(final_state) + '\n')

            elif args.command == 'run':
                input_file = args.input_file
                krun_args = []
                if args.term:
                    krun_args += ['--term']
                if args.parser is not None:
                    krun_args += ['--parser', args.parser]
                if not args.expand_macros:
                    krun_args += ['--no-expand-macros']
                # TODO: These are inlined into _krun
                krun_args += ['--output', args.output]
                krun_result = _krun(kevm.definition_dir, Path(input_file), depth=args.depth, args=krun_args, profile=args.profile)
                print(krun_result.stdout)
                sys.exit(krun_result.returncode)

    else:
        assert False


def create_argument_parser():

    def list_of(elem_type, delim=';'):
        def parse(s):
            return [elem_type(elem) for elem in s.split(delim)]
        return parse

    shared_args = argparse.ArgumentParser(add_help=False)
    shared_args.add_argument('--verbose', '-v', default=False, action='store_true', help='Verbose output.')
    shared_args.add_argument('--debug', default=False, action='store_true', help='Debug output.')
    shared_args.add_argument('--profile', default=False, action='store_true', help='Coarse process-level profiling.')
    shared_args.add_argument('--definition', type=str, dest='definition_dir', help='Path to definition to use.')
    shared_args.add_argument('-I', type=str, dest='includes', default=[], action='append', help='Directories to lookup K definitions in.')

    evm_chain_args = argparse.ArgumentParser(add_help=False)
    evm_chain_args.add_argument('--schedule', type=str, default='LONDON', help='KEVM Schedule to use for execution. One of [DEFAULT|FRONTIER|HOMESTEAD|TANGERINE_WHISTLE|SPURIOUS_DRAGON|BYZANTIUM|CONSTANTINOPLE|PETERSBURG|ISTANBUL|BERLIN|LONDON].')
    evm_chain_args.add_argument('--chainid', type=int, default=1, help='Chain ID to use for execution.')
    evm_chain_args.add_argument('--mode', type=str, default='NORMAL', help='Execution mode to use. One of [NORMAL|VMTESTS].')

    parser = argparse.ArgumentParser(prog='python3 -m kevm_pyk')

    command_parser = parser.add_subparsers(dest='command', required=True)

    kompile_args = command_parser.add_parser('kompile', help='Kompile KEVM specification.', parents=[shared_args])
    kompile_args.add_argument('main_file', type=file_path, help='Path to file with main module.')
    kompile_args.add_argument('--main-module', type=str, help='Name of the main module.')
    kompile_args.add_argument('--syntax-module', type=str, help='Name of the syntax module.')
    kompile_args.add_argument('--md-selector', type=str, help='Code selector expression to use when reading markdown.')
    kompile_args.add_argument('--hook-namespaces', type=str, help='Hook namespaces. What more can I say?')
    kompile_args.add_argument('--concrete-rules-file', type=str, help='List of rules to only evaluate if arguments are fully concrete.')
    kompile_args.add_argument('--emit-json', dest='emit_json', default=True, action='store_true', help='Emit JSON definition after compilation.')
    kompile_args.add_argument('--no-emit-json', dest='emit_json', action='store_false', help='Do not JSON definition after compilation.')

    prove_args = command_parser.add_parser('prove', help='Run KEVM proof.', parents=[shared_args])
    prove_args.add_argument('spec_file', type=file_path, help='Path to spec file.')
    prove_args.add_argument('--spec-module', type=str, help='Name of the specification module.')
    prove_args.add_argument('--debug-equations', type=list_of(str, delim=','), default=[], help='Comma-separate list of equations to debug.')
    prove_args.add_argument('--bug-report', default=False, action='store_true', help='Generate a haskell-backend bug report for the execution.')

    run_args = command_parser.add_parser('run', help='Run KEVM test/simulation.', parents=[shared_args, evm_chain_args])
    run_args.add_argument('input_file', type=file_path, help='Path to input file.')
    run_args.add_argument('--depth', default=None, type=int, help='Maximum depth to execute to.')
    run_args.add_argument('--term', default=False, action='store_true', help='<input_file> is the entire term to execute.')
    run_args.add_argument('--parser', default=None, type=str, help='Parser to use for $PGM.')
    run_args.add_argument('--output', default='pretty', type=str, help='Output format to use, one of [pretty|program|kast|binary|json|latex|kore|none].')
    run_args.add_argument('--expand-macros', dest='expand_macros', default=True, action='store_true', help='Expand macros on the input term before execution.')
    run_args.add_argument('--no-expand-macros', dest='expand_macros', action='store_false', help='Do not expand macros on the input term before execution.')

    solc_args = command_parser.add_parser('compile', help='Generate combined JSON with solc compilation results.')
    solc_args.add_argument('contract_file', type=file_path, help='Path to contract file.')

    gst_to_kore_args = command_parser.add_parser('gst-to-kore', help='Convert a GeneralStateTest to Kore for compsumption by KEVM.', parents=[shared_args, evm_chain_args])
    gst_to_kore_args.add_argument('input_file', type=file_path, help='Path to GST.')

    k_gen_args = argparse.ArgumentParser(add_help=False)
    k_gen_args.add_argument('--main-module', default='VERIFICATION', type=str, help='Name of the main module.')
    k_gen_args.add_argument('--spec-module', default='SPEC', type=str, help='Name of the spec module.')
    k_gen_args.add_argument('--require', dest='requires', default=[], action='append', help='Extra K requires to include in generated output.')
    k_gen_args.add_argument('--module-import', dest='imports', default=[], action='append', help='Extra modules to import into generated main module.')
    k_gen_args.add_argument('--exclude-tests', type=file_path, help='File containing, one per line, tests to exclude as CONTRACT_NAME.TEST_NAME.')

    solc_to_k_args = command_parser.add_parser('solc-to-k', help='Output helper K definition for given JSON output from solc compiler.', parents=[shared_args, k_gen_args])
    solc_to_k_args.add_argument('contract_file', type=file_path, help='Path to contract file.')
    solc_to_k_args.add_argument('contract_name', type=str, help='Name of contract to generate K helpers for.')

    foundry_to_k_args = command_parser.add_parser('foundry-to-k', help='Output helper K definition for given JSON output from solc compiler that Foundry produces.', parents=[shared_args, k_gen_args])
    foundry_to_k_args.add_argument('out', type=dir_path, help='Path to Foundry output directory.')

    return parser


if __name__ == "__main__":
    main()
