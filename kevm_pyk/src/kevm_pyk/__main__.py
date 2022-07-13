import argparse
import glob
import json
import logging
import sys
from pathlib import Path
from typing import Final

from pyk.cli_utils import dir_path, file_path

from .kevm import KEVM
from .solc_to_k import gen_spec_modules, solc_compile, solc_to_k
from .utils import add_include_arg

_LOGGER: Final = logging.getLogger(__name__)
_LOG_FORMAT: Final = '%(levelname)s %(asctime)s %(name)s - %(message)s'


def main():
    sys.setrecursionlimit(15000000)
    parser = create_argument_parser()
    args = parser.parse_args()

    if args.verbose:
        logging.basicConfig(level=logging.DEBUG, format=_LOG_FORMAT)
    else:
        logging.basicConfig(level=logging.WARNING, format=_LOG_FORMAT)

    if args.command == 'compile':
        res = solc_compile(args.contract_file)
        print(json.dumps(res))

    elif args.command in ['solc-to-k', 'foundry-to-k', 'gen-spec-modules', 'kompile', 'prove']:

        if 'definition_dir' not in args:
            raise ValueError(f'Must provide --definition argument to {args.command}!')

        if args.command == 'kompile':
            kevm = KEVM.kompile(
                args.definition_dir,
                args.main_file,
                includes=args.includes,
                main_module_name=args.main_module,
                syntax_module_name=args.syntax_module,
                md_selector=args.md_selector,
                hook_namespaces=args.hook_namespaces.split(' '),
                concrete_rules_file=args.concrete_rules_file,
            )

        else:
            kevm = KEVM(args.definition_dir)

            if args.command == 'solc-to-k':
                solc_json = solc_compile(args.contract_file)
                contract_json = solc_json['contracts'][args.contract_file.name][args.contract_name]
                res = solc_to_k(kevm, contract_json, args.contract_file.name, args.contract_name, args.generate_storage)
                print(res)

            elif args.command == 'foundry-to-k':
                # forge build --extra-output storageLayout --extra-output abi --extra-output evm.methodIdentifiers --extra-output evm.deployedBytecode.object
                path_glob = str(args.out) + '/**/*.json'
                for f in map(Path, glob.glob(path_glob)):
                    _LOGGER.info(f'Processing contract file: {f}')
                    with open(f, 'r') as cjson:
                        contract_json = json.loads(cjson.read())
                        res = solc_to_k(kevm, contract_json, 'NONAME', 'NONAME', args.generate_storage, foundry=True)
                        print(res)

            elif args.command == 'gen-spec-modules':
                res = gen_spec_modules(kevm, args.spec_module_name)
                print(res)

            elif args.command == 'prove':
                spec_file = args.spec_file
                spec_module = args.spec_module
                prove_args = add_include_arg(args.includes)
                haskell_args = []
                for de in args.debug_equations:
                    haskell_args += ['--debug-equation', de]
                if args.bug_report:
                    haskell_args += ['--bug-report', str(spec_file.with_suffix(''))]
                final_state = kevm.prove(spec_file, spec_module_name=spec_module, args=prove_args, haskell_args=haskell_args, rule_profile=spec_file.with_suffix('.rule-profile'))
                print(kevm.pretty_print(final_state) + '\n')

    else:
        assert False


def create_argument_parser():

    def list_of(elem_type, delim=';'):
        def parse(s):
            return [elem_type(elem) for elem in s.split(delim)]
        return parse

    shared_options = argparse.ArgumentParser(add_help=False)
    shared_options.add_argument('--verbose', '-v', default=False, action='store_true', help='Verbose debugging information.')
    shared_options.add_argument('--definition', type=str, dest='definition_dir', help='Path to definition to use.')
    shared_options.add_argument('-I', type=str, dest='includes', default=[], action='append', help='Directories to lookup K definitions in.')

    parser = argparse.ArgumentParser(prog='python3 -m kevm_pyk')

    command_parser = parser.add_subparsers(dest='command', required=True)

    kompile_subparser = command_parser.add_parser('kompile', help='Kompile KEVM specification.', parents=[shared_options])
    kompile_subparser.add_argument('main_file', type=file_path, help='Path to file with main module.')
    kompile_subparser.add_argument('--main-module', type=str, help='Name of the main module.')
    kompile_subparser.add_argument('--syntax-module', type=str, help='Name of the syntax module.')
    kompile_subparser.add_argument('--md-selector', type=str, help='Code selector expression to use when reading markdown.')
    kompile_subparser.add_argument('--hook-namespaces', type=str, help='Hook namespaces. What more can I say?')
    kompile_subparser.add_argument('--concrete-rules-file', type=str, help='List of rules to only evaluate if arguments are fully concrete.')

    prove_subparser = command_parser.add_parser('prove', help='Run KEVM proof.', parents=[shared_options])
    prove_subparser.add_argument('spec_file', type=file_path, help='Path to spec file.')
    prove_subparser.add_argument('--spec-module', type=str, help='Name of the specification module.')
    prove_subparser.add_argument('--debug-equations', type=list_of(str, delim=','), default=[], help='Comma-separate list of equations to debug.')
    prove_subparser.add_argument('--bug-report', default=False, action='store_true', help='Generate a haskell-backend bug report for the execution.')

    solc_subparser = command_parser.add_parser('compile', help='Generate combined JSON with solc compilation results.')
    solc_subparser.add_argument('contract_file', type=file_path, help='Path to contract file.')

    solc_to_k_subparser = command_parser.add_parser('solc-to-k', help='Output helper K definition for given JSON output from solc compiler.', parents=[shared_options])
    solc_to_k_subparser.add_argument('contract_file', type=file_path, help='Path to contract file.')
    solc_to_k_subparser.add_argument('contract_name', type=str, help='Name of contract to generate K helpers for.')
    solc_to_k_subparser.add_argument('--no-storage-slots', dest='generate_storage', default=True, action='store_false', help='Do not generate productions and rules for accessing storage slots')

    foundry_to_k_subparser = command_parser.add_parser('foundry-to-k', help='Output helper K definition for given JSON output from solc compiler that Foundry produces.', parents=[shared_options])
    foundry_to_k_subparser.add_argument('out', type=dir_path, help='Path to Foundry output directory.')
    foundry_to_k_subparser.add_argument('--no-storage-slots', dest='generate_storage', default=True, action='store_false', help='Do not generate productions and rules for accessing storage slots')

    gen_spec_modules_subparser = command_parser.add_parser('gen-spec-modules', help='Output helper K definition for given JSON output from solc compiler.', parents=[shared_options])
    gen_spec_modules_subparser.add_argument('spec_module_name', type=str, help='Name of module containing all the generated specs.')

    return parser


if __name__ == "__main__":
    main()
