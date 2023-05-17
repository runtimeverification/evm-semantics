from __future__ import annotations

from argparse import ArgumentParser
from functools import cached_property
from typing import TYPE_CHECKING

from pyk.cli_utils import dir_path

if TYPE_CHECKING:
    from collections.abc import Callable
    from typing import TypeVar

    T = TypeVar('T')


def list_of(elem_type: Callable[[str], T], delim: str = ';') -> Callable[[str], list[T]]:
    def parse(s: str) -> list[T]:
        return [elem_type(elem) for elem in s.split(delim)]

    return parse


class KEVMCLIArgs:
    @cached_property
    def shared_args(self) -> ArgumentParser:
        args = ArgumentParser(add_help=False)
        args.add_argument('--verbose', '-v', default=False, action='store_true', help='Verbose output.')
        args.add_argument('--debug', default=False, action='store_true', help='Debug output.')
        args.add_argument('--workers', '-j', default=1, type=int, help='Number of processes to run in parallel.')
        return args

    @cached_property
    def k_args(self) -> ArgumentParser:
        args = ArgumentParser(add_help=False)
        args.add_argument('--depth', default=None, type=int, help='Maximum depth to execute to.')
        args.add_argument(
            '-I', type=str, dest='includes', default=[], action='append', help='Directories to lookup K definitions in.'
        )
        args.add_argument('--main-module', default=None, type=str, help='Name of the main module.')
        args.add_argument('--syntax-module', default=None, type=str, help='Name of the syntax module.')
        args.add_argument('--spec-module', default=None, type=str, help='Name of the spec module.')
        args.add_argument('--definition', type=dir_path, dest='definition_dir', help='Path to definition to use.')
        args.add_argument(
            '--md-selector',
            type=str,
            help='Code selector expression to use when reading markdown.',
        )
        return args

    @cached_property
    def kprove_args(self) -> ArgumentParser:
        args = ArgumentParser(add_help=False)
        args.add_argument(
            '--debug-equations',
            type=list_of(str, delim=','),
            default=[],
            help='Comma-separate list of equations to debug.',
        )
        return args

    @cached_property
    def kompile_args(self) -> ArgumentParser:
        args = ArgumentParser(add_help=False)
        args.add_argument(
            '--emit-json',
            dest='emit_json',
            default=True,
            action='store_true',
            help='Emit JSON definition after compilation.',
        )
        args.add_argument(
            '--no-emit-json', dest='emit_json', action='store_false', help='Do not JSON definition after compilation.'
        )
        args.add_argument(
            '-ccopt',
            dest='ccopts',
            default=[],
            action='append',
            help='Additional arguments to pass to llvm-kompile.',
        )
        args.add_argument(
            '--no-llvm-kompile',
            dest='llvm_kompile',
            default=True,
            action='store_false',
            help='Do not run llvm-kompile process.',
        )
        args.add_argument(
            '--with-llvm-library',
            dest='llvm_library',
            default=False,
            action='store_true',
            help='Make kompile generate a dynamic llvm library.',
        )
        args.add_argument(
            '--enable-llvm-debug',
            dest='enable_llvm_debug',
            default=False,
            action='store_true',
            help='Make kompile generate debug symbols for llvm.',
        )
        args.add_argument(
            '--read-only-kompiled-directory',
            dest='read_only',
            default=False,
            action='store_true',
            help='Generated a kompiled directory that K will not attempt to write to afterwards.',
        )
        args.add_argument('-O0', dest='o0', default=False, action='store_true', help='Optimization level 0.')
        args.add_argument('-O1', dest='o1', default=False, action='store_true', help='Optimization level 1.')
        args.add_argument('-O2', dest='o2', default=False, action='store_true', help='Optimization level 2.')
        args.add_argument('-O3', dest='o3', default=False, action='store_true', help='Optimization level 3.')
        return args

    @cached_property
    def evm_chain_args(self) -> ArgumentParser:
        schedules = (
            'DEFAULT',
            'FRONTIER',
            'HOMESTEAD',
            'TANGERINE_WHISTLE',
            'SPURIOUS_DRAGON',
            'BYZANTIUM',
            'CONSTANTINOPLE',
            'PETERSBURG',
            'ISTANBUL',
            'BERLIN',
            'LONDON',
            'MERGE',
        )
        modes = ('NORMAL', 'VMTESTS')

        args = ArgumentParser(add_help=False)
        args.add_argument(
            '--schedule',
            choices=schedules,
            default='LONDON',
            help=f"schedule to use for execution [{'|'.join(schedules)}]",
        )
        args.add_argument('--chainid', type=int, default=1, help='chain ID to use for execution')
        args.add_argument(
            '--mode',
            choices=modes,
            default='NORMAL',
            help="execution mode to use [{'|'.join(modes)}]",
        )
        return args
