from __future__ import annotations

from argparse import ArgumentParser
from functools import cached_property
from pathlib import Path
from typing import TYPE_CHECKING

from pyk.cli.args import KCLIArgs
from pyk.cli.utils import dir_path

from .utils import arg_pair_of

if TYPE_CHECKING:
    from collections.abc import Callable
    from typing import TypeVar

    from pyk.kcfg.kcfg import NodeIdLike

    T = TypeVar('T')


def list_of(elem_type: Callable[[str], T], delim: str = ';') -> Callable[[str], list[T]]:
    def parse(s: str) -> list[T]:
        return [elem_type(elem) for elem in s.split(delim)]

    return parse


def node_id_like(s: str) -> NodeIdLike:
    try:
        return int(s)
    except ValueError:
        return s


class KEVMCLIArgs(KCLIArgs):
    @cached_property
    def k_args(self) -> ArgumentParser:
        args = super().definition_args
        args.add_argument('--depth', default=None, type=int, help='Maximum depth to execute to.')
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
    def kprove_legacy_args(self) -> ArgumentParser:
        args = ArgumentParser(add_help=False)
        args.add_argument(
            '--bug-report',
            default=False,
            action='store_true',
            help='Generate a haskell-backend bug report for the execution.',
        )
        args.add_argument(
            '--debugger',
            dest='debugger',
            default=False,
            action='store_true',
            help='Launch proof in an interactive debugger.',
        )
        args.add_argument(
            '--max-depth',
            dest='max_depth',
            default=None,
            type=int,
            help='The maximum number of computational steps to prove.',
        )
        args.add_argument(
            '--max-counterexamples',
            type=int,
            dest='max_counterexamples',
            default=None,
            help='Maximum number of counterexamples reported before a forcible stop.',
        )
        args.add_argument(
            '--branching-allowed',
            type=int,
            dest='branching_allowed',
            default=None,
            help='Number of branching events allowed before a forcible stop.',
        )
        args.add_argument(
            '--haskell-backend-arg',
            dest='haskell_backend_args',
            default=[],
            action='append',
            help='Arguments passed to the Haskell backend execution engine.',
        )
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
            default='MERGE',
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

    @cached_property
    def display_args(self) -> ArgumentParser:
        args = super().display_args
        args.add_argument(
            '--sort-collections',
            dest='sort_collections',
            default=False,
            action='store_true',
            help='Sort collections before outputting term.',
        )
        return args

    @cached_property
    def foundry_args(self) -> ArgumentParser:
        args = ArgumentParser(add_help=False)
        args.add_argument(
            '--foundry-project-root',
            dest='foundry_root',
            type=dir_path,
            default=Path('.'),
            help='Path to Foundry project root directory.',
        )
        return args

    @cached_property
    def rpc_args(self) -> ArgumentParser:
        args = ArgumentParser(add_help=False)
        args.add_argument(
            '--bug-report',
            default=False,
            action='store_true',
            help='Generate a haskell-backend bug report for the execution.',
        )
        args.add_argument(
            '--trace-rewrites',
            default=False,
            action='store_true',
            help='Log traces of all simplification and rewrite rule applications.',
        )
        return args

    @cached_property
    def smt_args(self) -> ArgumentParser:
        args = ArgumentParser(add_help=False)
        args.add_argument(
            '--smt-timeout', dest='smt_timeout', type=int, default=125, help='Timeout in ms to use for SMT queries.'
        )
        args.add_argument(
            '--smt-retry-limit',
            dest='smt_retry_limit',
            type=int,
            default=4,
            help='Number of times to retry SMT queries with scaling timeouts.',
        )
        return args

    @cached_property
    def explore_args(self) -> ArgumentParser:
        args = ArgumentParser(add_help=False)
        args.add_argument(
            '--break-every-step',
            dest='break_every_step',
            default=False,
            action='store_true',
            help='Store a node for every EVM opcode step (expensive).',
        )
        args.add_argument(
            '--break-on-jumpi',
            dest='break_on_jumpi',
            default=False,
            action='store_true',
            help='Store a node for every EVM jump opcode.',
        )
        args.add_argument(
            '--break-on-calls',
            dest='break_on_calls',
            default=True,
            action='store_true',
            help='Store a node for every EVM call made.',
        )
        args.add_argument(
            '--no-break-on-calls',
            dest='break_on_calls',
            action='store_false',
            help='Do not store a node for every EVM call made.',
        )
        args.add_argument(
            '--implication-every-block',
            dest='implication_every_block',
            default=True,
            action='store_true',
            help='Check subsumption into target state every basic block, not just at terminal nodes.',
        )
        args.add_argument(
            '--no-implication-every-block',
            dest='implication_every_block',
            action='store_false',
            help='Do not check subsumption into target state every basic block, not just at terminal nodes.',
        )
        args.add_argument(
            '--simplify-init',
            dest='simplify_init',
            default=True,
            action='store_true',
            help='Simplify the initial and target states at startup.',
        )
        args.add_argument(
            '--no-simplify-init',
            dest='simplify_init',
            action='store_false',
            help='Do not simplify the initial and target states at startup.',
        )
        args.add_argument(
            '--max-depth',
            dest='max_depth',
            default=1000,
            type=int,
            help='Store every Nth state in the CFG for inspection.',
        )
        args.add_argument(
            '--max-iterations',
            dest='max_iterations',
            default=None,
            type=int,
            help='Store every Nth state in the CFG for inspection.',
        )
        args.add_argument(
            '--kore-rpc-command',
            dest='kore_rpc_command',
            type=str,
            default='kore-rpc',
            help='Custom command to start RPC server',
        )
        args.add_argument(
            '--failure-information',
            dest='failure_info',
            default=True,
            action='store_true',
            help='Show failure summary for all failing tests',
        )
        args.add_argument(
            '--no-failure-information',
            dest='failure_info',
            action='store_false',
            help='Do not show failure summary for failing tests',
        )
        args.add_argument(
            '--auto-abstract-gas',
            dest='auto_abstract_gas',
            action='store_true',
            help='Automatically extract gas cell when infinite gas is enabled',
        )
        return args

    @cached_property
    def k_gen_args(self) -> ArgumentParser:
        args = ArgumentParser(add_help=False)
        args.add_argument(
            '--require',
            dest='requires',
            default=[],
            action='append',
            help='Extra K requires to include in generated output.',
        )
        args.add_argument(
            '--module-import',
            dest='imports',
            default=[],
            action='append',
            help='Extra modules to import into generated main module.',
        )
        return args

    @cached_property
    def kcfg_show_args(self) -> ArgumentParser:
        args = ArgumentParser(add_help=False)
        args.add_argument(
            '--node',
            type=node_id_like,
            dest='nodes',
            default=[],
            action='append',
            help='List of nodes to display as well.',
        )
        args.add_argument(
            '--node-delta',
            type=arg_pair_of(node_id_like, node_id_like),
            dest='node_deltas',
            default=[],
            action='append',
            help='List of nodes to display delta for.',
        )
        args.add_argument(
            '--failure-information',
            dest='failure_info',
            default=False,
            action='store_true',
            help='Show failure summary for cfg',
        )
        args.add_argument(
            '--no-failure-information',
            dest='failure_info',
            action='store_false',
            help='Do not show failure summary for cfg',
        )
        args.add_argument(
            '--to-module', dest='to_module', default=False, action='store_true', help='Output edges as a K module.'
        )
        args.add_argument(
            '--pending', dest='pending', default=False, action='store_true', help='Also display pending nodes'
        )
        args.add_argument(
            '--failing', dest='failing', default=False, action='store_true', help='Also display failing nodes'
        )
        return args
