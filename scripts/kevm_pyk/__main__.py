import argparse
import json
import sys

from pyk.cli_utils import file_path

from .solc_to_k import solc_to_k, solc_compile


def main():
    sys.setrecursionlimit(15000000)
    parser = create_argument_parser()
    args = parser.parse_args()

    if args.command == 'compile':
        res = solc_compile(args.contract_file)
        print(json.dumps(res))

    elif args.command == 'solc-to-k':
        res = solc_to_k(**vars(args))
        print(res)

    else:
        assert False


def create_argument_parser():
    parser = argparse.ArgumentParser(prog='python3 -m kevm_pyk')
    command_parser = parser.add_subparsers(dest='command', required=True)

    solc_subparser = command_parser.add_parser('compile', help='Generate combined JSON with solc compilation results.')
    solc_subparser.add_argument('contract_file', type=file_path, help='Path to contract file.')

    solc_to_k_subparser = command_parser.add_parser('solc-to-k', help='Output helper K definition for given JSON output from solc compiler.')
    solc_to_k_subparser.add_argument('kompiled_directory', type=str, help='Path to *-kompiled directory to use.')
    solc_to_k_subparser.add_argument('contract_file', type=file_path, help='Path to contract file.')
    solc_to_k_subparser.add_argument('contract_name', type=str, help='Name of contract to generate K helpers for.')
    solc_to_k_subparser.add_argument('--no-storage-slots', dest='generate_storage', default=True, action='store_false', help='Do not generate productions and rules for accessing storage slots')

    return parser


if __name__ == "__main__":
    main()
