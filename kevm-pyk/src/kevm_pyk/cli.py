from __future__ import annotations

from argparse import ArgumentParser
from functools import cached_property
from typing import TYPE_CHECKING

from pyk.cli.args import KCLIArgs
from pyk.kore.rpc import FallbackReason

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
    def target_args(self) -> ArgumentParser:
        args = ArgumentParser(add_help=False)
        args.add_argument('--target', choices=['llvm', 'haskell', 'haskell-standalone', 'foundry'])
        return args

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
        args.add_argument(
            '--always-check-subsumption',
            dest='always-check_subsumption',
            default=True,
            action='store_true',
            help='Check subsumption even on non-terminal nodes (default)(experimental).',
        )
        args.add_argument(
            '--no-always-check-subsumption',
            dest='always-check_subsumption',
            action='store_false',
            help='Do not check subsumption on non-terminal nodes (experimental).',
        )
        args.add_argument(
            '--fast-check-subsumption',
            dest='fast_check_subsumption',
            default=False,
            action='store_true',
            help='Use fast-check on k-cell to determine subsumption (experimental).',
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
            'SHANGHAI',
        )
        modes = ('NORMAL', 'VMTESTS')

        args = ArgumentParser(add_help=False)
        args.add_argument(
            '--schedule',
            choices=schedules,
            default='SHANGHAI',
            help=f"schedule to use for execution [{'|'.join(schedules)}]",
        )
        args.add_argument('--chainid', type=int, default=1, help='chain ID to use for execution')
        args.add_argument(
            '--mode',
            choices=modes,
            default='NORMAL',
            help="execution mode to use [{'|'.join(modes)}]",
        )
        args.add_argument(
            '--no-gas', action='store_false', dest='usegas', default=True, help='omit gas cost computations'
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
    def rpc_args(self) -> ArgumentParser:
        args = ArgumentParser(add_help=False)
        args.add_argument(
            '--trace-rewrites',
            dest='trace_rewrites',
            default=False,
            action='store_true',
            help='Log traces of all simplification and rewrite rule applications.',
        )
        args.add_argument(
            '--kore-rpc-command',
            dest='kore_rpc_command',
            type=str,
            default=None,
            help='Custom command to start RPC server',
        )
        args.add_argument(
            '--use-booster',
            dest='use_booster',
            default=False,
            action='store_true',
            help='Use the booster RPC server instead of kore-rpc.',
        )
        args.add_argument(
            '--fallback-on',
            dest='fallback_on',
            type=list_of(FallbackReason, delim=','),
            help='Comma-separated reasons to fallback from booster to kore, only usable with --use-booster. Options [Branching,Aborted,Stuck].',
        )
        args.add_argument(
            '--post-exec-simplify',
            dest='post_exec_simplify',
            default=True,
            action='store_true',
            help='Always simplify states with kore backend after booster execution, only usable with --use-booster.',
        )
        args.add_argument(
            '--no-post-exec-simplify',
            dest='post_exec_simplify',
            action='store_false',
            help='Do not simplify states with kore backend after booster execution, only usable with --use-booster.',
        )
        args.add_argument(
            '--interim-simplification',
            dest='interim_simplification',
            type=int,
            help='Max number of steps to execute before applying simplifier to term in booster backend, only usable with --use-booster.',
        )
        args.add_argument(
            '--port',
            dest='port',
            type=int,
            default=None,
            help='Use existing RPC server on named port',
        )
        args.add_argument(
            '--maude-port',
            dest='maude_port',
            type=int,
            default=None,
            help='Use existing Maude RPC server on named port',
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
            default=False,
            action='store_true',
            help='Store a node for every EVM call made.',
        )
        args.add_argument(
            '--no-break-on-calls',
            dest='break_on_calls',
            default=True,
            action='store_false',
            help='Do not store a node for every EVM call made (default).',
        )
        args.add_argument(
            '--break-on-storage',
            dest='break_on_storage',
            default=False,
            action='store_true',
            help='Store a node for every EVM SSTORE/SLOAD made.',
        )
        args.add_argument(
            '--break-on-basic-blocks',
            dest='break_on_basic_blocks',
            default=False,
            action='store_true',
            help='Store a node for every EVM basic block (implies --break-on-calls).',
        )
        args.add_argument(
            '--max-depth',
            dest='max_depth',
            default=1000,
            type=int,
            help='Maximum number of K steps before the state is saved in a new node in the CFG. Branching will cause this to happen earlier.',
        )
        args.add_argument(
            '--max-iterations',
            dest='max_iterations',
            default=None,
            type=int,
            help='Number of times to expand the next pending node in the CFG.',
        )
        args.add_argument(
            '--failure-information',
            dest='failure_info',
            default=True,
            action='store_true',
            help='Show failure summary for all failing tests (default)',
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
        args.add_argument(
            '--counterexample-information',
            dest='counterexample_info',
            default=True,
            action='store_true',
            help='Show models for failing nodes (default)',
        )
        args.add_argument(
            '--no-counterexample-information',
            dest='counterexample_info',
            action='store_false',
            help='Do not show models for failing nodes.',
        )
        args.add_argument(
            '--fail-fast',
            dest='fail_fast',
            default=True,
            action='store_true',
            help='Stop execution on other branches if a failing node is detected (default).',
        )
        args.add_argument(
            '--no-fail-fast',
            dest='fail_fast',
            action='store_false',
            help='Continue execution on other branches if a failing node is detected.',
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
        args.add_argument(
            '--counterexample-information',
            dest='counterexample_info',
            default=False,
            action='store_true',
            help="Show models for failing nodes. Should be called with the '--failure-information' flag",
        )
        return args
