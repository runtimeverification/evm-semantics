import argparse
import sys

from .solc_to_k import solc_to_k


def main(args):
    if args.command == 'solc-to-k':
        res = solc_to_k(**vars(args))
        sys.stdout.write(res)
        sys.stdout.flush()


def create_argument_parser():
    parser = argparse.ArgumentParser(prog='python3 -m kevm_pyk')
    command_parser = parser.add_subparsers(dest='command')
    solc_command_parser = command_parser.add_parser('solc-to-k', help='Output helper K definition for given JSON output from solc compiler.')
    solc_command_parser.add_argument('kompiled_directory', type=str, help='Path to *-kompiled directory to use.')
    solc_command_parser.add_argument('contract_file', type=str, help='Combined JSON output from solc compiler.')
    solc_command_parser.add_argument('solc_output', type=argparse.FileType('r'), default='-', help='Combined JSON output from solc compiler.')
    solc_command_parser.add_argument('contract_name', type=str, help='Name of contract to generate K helpers for.')
    solc_command_parser.add_argument('--no-storage-slots', dest='generate_storage', default=True, action='store_false', help='Do not generate productions and rules for accessing storage slots')
    return parser


sys.setrecursionlimit(15000000)
parser = create_argument_parser()
args = parser.parse_args()
main(args)
