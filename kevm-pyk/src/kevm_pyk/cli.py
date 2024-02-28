from __future__ import annotations

from argparse import ArgumentParser
from functools import cached_property
from pathlib import Path
from typing import TYPE_CHECKING, Any

from pyk.cli.args import (
    BugReportOptions,
    DisplayOptions,
    KDefinitionOptions,
    KompileOptions,
    LoggingOptions,
    Options,
    ParallelOptions,
    SMTOptions,
    SpecOptions,
)
from pyk.cli.utils import file_path
from pyk.kore.rpc import FallbackReason
from pyk.kore.tools import PrintOutput
from pyk.ktool.krun import KRunOutput

from .kompile import KompileTarget
from .utils import arg_pair_of

if TYPE_CHECKING:
    from argparse import _SubParsersAction
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


class KEVMDisplayOptions(DisplayOptions):
    @staticmethod
    def default() -> dict[str, Any]:
        return {'sort_collections': False}

    @staticmethod
    def args(parser: ArgumentParser) -> ArgumentParser:
        parser.add_argument(
            '--sort-collections',
            dest='sort_collections',
            default=None,
            action='store_true',
            help='Sort collections before outputting term.',
        )
        return parser


class KOptions(KDefinitionOptions):

    @staticmethod
    def args(parser: ArgumentParser) -> ArgumentParser:
        parser.add_argument('--depth', default=None, type=int, help='Maximum depth to execute to.')
        return parser


class KompileSpecOptions(LoggingOptions, KOptions, KompileOptions):
    @staticmethod
    def default() -> dict[str, Any]:
        return {
            'debug_build': False,
        }

    @staticmethod
    def parser(base: _SubParsersAction) -> _SubParsersAction:
        base.add_parser(
            'kompile-spec',
            help='Kompile KEVM specification.',
            parents=[KompileSpecOptions.all_args()],
        )
        return base

    @staticmethod
    def args(parser: ArgumentParser) -> ArgumentParser:
        parser.add_argument('main_file', type=file_path, help='Path to file with main module.')
        parser.add_argument('--target', type=KompileTarget, help='[haskell|maude]')
        parser.add_argument(
            '-o', '--output-definition', type=Path, dest='output_dir', help='Path to write kompiled definition to.'
        )
        parser.add_argument(
            '--debug-build', dest='debug_build', default=None, help='Enable debug symbols in LLVM builds.'
        )
        return parser


class ShowKCFGOptions(LoggingOptions, KOptions, SpecOptions, DisplayOptions):
    @staticmethod
    def parser(base: _SubParsersAction) -> _SubParsersAction:
        base.add_parser(
            'show-kcfg',
            help='Print the CFG for a given proof.',
            parents=[ShowKCFGOptions.all_args()],
        )
        return base

    @staticmethod
    def args(parser: ArgumentParser) -> ArgumentParser:
        parser.add_argument(
            '--node',
            type=node_id_like,
            dest='nodes',
            default=[],
            action='append',
            help='List of nodes to display as well.',
        )
        parser.add_argument(
            '--node-delta',
            type=arg_pair_of(node_id_like, node_id_like),
            dest='node_deltas',
            default=[],
            action='append',
            help='List of nodes to display delta for.',
        )
        parser.add_argument(
            '--failure-information',
            dest='failure_info',
            default=False,
            action='store_true',
            help='Show failure summary for cfg',
        )
        parser.add_argument(
            '--no-failure-information',
            dest='failure_info',
            action='store_false',
            help='Do not show failure summary for cfg',
        )
        parser.add_argument(
            '--to-module', dest='to_module', default=False, action='store_true', help='Output edges as a K module.'
        )
        parser.add_argument(
            '--pending', dest='pending', default=False, action='store_true', help='Also display pending nodes'
        )
        parser.add_argument(
            '--failing', dest='failing', default=False, action='store_true', help='Also display failing nodes'
        )
        parser.add_argument(
            '--counterexample-information',
            dest='counterexample_info',
            default=False,
            action='store_true',
            help="Show models for failing nodes. Should be called with the '--failure-information' flag",
        )
        return parser


class KProveOptions(Options):
    @staticmethod
    def args(parser: ArgumentParser) -> ArgumentParser:
        parser.add_argument(
            '--debug-equations',
            type=list_of(str, delim=','),
            default=[],
            help='Comma-separate list of equations to debug.',
        )
        parser.add_argument(
            '--always-check-subsumption',
            dest='always-check_subsumption',
            default=True,
            action='store_true',
            help='Check subsumption even on non-terminal nodes.',
        )
        parser.add_argument(
            '--no-always-check-subsumption',
            dest='always-check_subsumption',
            action='store_false',
            help='Do not check subsumption on non-terminal nodes.',
        )
        parser.add_argument(
            '--fast-check-subsumption',
            dest='fast_check_subsumption',
            default=False,
            action='store_true',
            help='Use fast-check on k-cell to determine subsumption.',
        )
        return parser


class RPCOptions(Options):
    @staticmethod
    def args(parser: ArgumentParser) -> ArgumentParser:
        parser.add_argument(
            '--trace-rewrites',
            dest='trace_rewrites',
            default=False,
            action='store_true',
            help='Log traces of all simplification and rewrite rule applications.',
        )
        parser.add_argument(
            '--kore-rpc-command',
            dest='kore_rpc_command',
            type=str,
            default=None,
            help='Custom command to start RPC server',
        )
        parser.add_argument(
            '--use-booster',
            dest='use_booster',
            default=False,
            action='store_true',
            help='Use the booster RPC server instead of kore-rpc.',
        )
        parser.add_argument(
            '--fallback-on',
            dest='fallback_on',
            type=list_of(FallbackReason, delim=','),
            help='Comma-separated reasons to fallback from booster to kore, only usable with --use-booster. Options [Branching,Aborted,Stuck].',
        )
        parser.add_argument(
            '--post-exec-simplify',
            dest='post_exec_simplify',
            default=True,
            action='store_true',
            help='Always simplify states with kore backend after booster execution, only usable with --use-booster.',
        )
        parser.add_argument(
            '--no-post-exec-simplify',
            dest='post_exec_simplify',
            action='store_false',
            help='Do not simplify states with kore backend after booster execution, only usable with --use-booster.',
        )
        parser.add_argument(
            '--interim-simplification',
            dest='interim_simplification',
            type=int,
            help='Max number of steps to execute before applying simplifier to term in booster backend, only usable with --use-booster.',
        )
        parser.add_argument(
            '--port',
            dest='port',
            type=int,
            default=None,
            help='Use existing RPC server on named port',
        )
        parser.add_argument(
            '--maude-port',
            dest='maude_port',
            type=int,
            default=None,
            help='Use existing Maude RPC server on named port',
        )
        return parser


class ExploreOptions(Options):

    @staticmethod
    def args(parser: ArgumentParser) -> ArgumentParser:
        parser.add_argument(
            '--break-every-step',
            dest='break_every_step',
            default=False,
            action='store_true',
            help='Store a node for every EVM opcode step (expensive).',
        )
        parser.add_argument(
            '--break-on-jumpi',
            dest='break_on_jumpi',
            default=False,
            action='store_true',
            help='Store a node for every EVM jump opcode.',
        )
        parser.add_argument(
            '--break-on-calls',
            dest='break_on_calls',
            default=False,
            action='store_true',
            help='Store a node for every EVM call made.',
        )
        parser.add_argument(
            '--no-break-on-calls',
            dest='break_on_calls',
            default=True,
            action='store_false',
            help='Do not store a node for every EVM call made.',
        )
        parser.add_argument(
            '--break-on-storage',
            dest='break_on_storage',
            default=False,
            action='store_true',
            help='Store a node for every EVM SSTORE/SLOAD made.',
        )
        parser.add_argument(
            '--break-on-basic-blocks',
            dest='break_on_basic_blocks',
            default=False,
            action='store_true',
            help='Store a node for every EVM basic block (implies --break-on-calls).',
        )
        parser.add_argument(
            '--max-depth',
            dest='max_depth',
            default=1000,
            type=int,
            help='Maximum number of K steps before the state is saved in a new node in the CFG. Branching will cause this to happen earlier.',
        )
        parser.add_argument(
            '--max-iterations',
            dest='max_iterations',
            default=None,
            type=int,
            help='Number of times to expand the next pending node in the CFG.',
        )
        parser.add_argument(
            '--failure-information',
            dest='failure_info',
            default=True,
            action='store_true',
            help='Show failure summary for all failing tests',
        )
        parser.add_argument(
            '--no-failure-information',
            dest='failure_info',
            action='store_false',
            help='Do not show failure summary for failing tests',
        )
        parser.add_argument(
            '--auto-abstract-gas',
            dest='auto_abstract_gas',
            action='store_true',
            help='Automatically extract gas cell when infinite gas is enabled',
        )
        parser.add_argument(
            '--counterexample-information',
            dest='counterexample_info',
            default=True,
            action='store_true',
            help='Show models for failing nodes.',
        )
        parser.add_argument(
            '--no-counterexample-information',
            dest='counterexample_info',
            action='store_false',
            help='Do not show models for failing nodes.',
        )
        parser.add_argument(
            '--fail-fast',
            dest='fail_fast',
            default=True,
            action='store_true',
            help='Stop execution on other branches if a failing node is detected.',
        )
        parser.add_argument(
            '--no-fail-fast',
            dest='fail_fast',
            action='store_false',
            help='Continue execution on other branches if a failing node is detected.',
        )
        return parser


class ProveOptions(
    LoggingOptions, KOptions, ParallelOptions, KProveOptions, BugReportOptions, SMTOptions, ExploreOptions, SpecOptions
):
    @staticmethod
    def parser(base: _SubParsersAction) -> _SubParsersAction:
        base.add_parser(
            'prove',
            help='Run KEVM proof.',
            parents=[ProveOptions.all_args()],
        )
        return base

    @staticmethod
    def args(parser: ArgumentParser) -> ArgumentParser:
        parser.add_argument(
            '--reinit',
            dest='reinit',
            default=False,
            action='store_true',
            help='Reinitialize CFGs even if they already exist.',
        )
        return parser


class VersionOptions(LoggingOptions):
    @staticmethod
    def parser(base: _SubParsersAction) -> _SubParsersAction:
        base.add_parser(
            'version',
            help='Print KEVM version and exit.',
            parents=[VersionOptions.all_args()],
        )
        return base


class PruneProofOptions(LoggingOptions, KOptions, SpecOptions):
    @staticmethod
    def parser(base: _SubParsersAction) -> _SubParsersAction:
        base.add_parser(
            'prune-proof',
            help='Remove a node and its successors from the proof state.',
            parents=[PruneProofOptions.all_args()],
        )
        return base

    @staticmethod
    def args(parser: ArgumentParser) -> ArgumentParser:
        parser.add_argument('node', type=node_id_like, help='Node to remove CFG subgraph from.')
        return parser


class KProveLegacyOptions(Options):
    @staticmethod
    def args(parser: ArgumentParser) -> ArgumentParser:
        parser.add_argument(
            '--bug-report',
            default=False,
            action='store_true',
            help='Generate a haskell-backend bug report for the execution.',
        )
        parser.add_argument(
            '--debugger',
            dest='debugger',
            default=False,
            action='store_true',
            help='Launch proof in an interactive debugger.',
        )
        parser.add_argument(
            '--max-depth',
            dest='max_depth',
            default=None,
            type=int,
            help='The maximum number of computational steps to prove.',
        )
        parser.add_argument(
            '--max-counterexamples',
            type=int,
            dest='max_counterexamples',
            default=None,
            help='Maximum number of counterexamples reported before a forcible stop.',
        )
        parser.add_argument(
            '--branching-allowed',
            type=int,
            dest='branching_allowed',
            default=None,
            help='Number of branching events allowed before a forcible stop.',
        )
        parser.add_argument(
            '--haskell-backend-arg',
            dest='haskell_backend_args',
            default=[],
            action='append',
            help='Arguments passed to the Haskell backend execution engine.',
        )
        return parser


class ProveLegacyOptions(LoggingOptions, KOptions, SpecOptions, KProveLegacyOptions):
    @staticmethod
    def parser(base: _SubParsersAction) -> _SubParsersAction:
        base.add_parser(
            'prove-legacy',
            help='Run KEVM proof using the legacy kprove binary.',
            parents=[ProveLegacyOptions.all_args()],
        )
        return base

    @staticmethod
    def args(parser: ArgumentParser) -> ArgumentParser:
        parser.add_argument(
            '--bug-report-legacy', default=False, action='store_true', help='Generate a legacy bug report.'
        )
        return parser


class ViewKCFGOptions(LoggingOptions, KOptions, SpecOptions):
    @staticmethod
    def parser(base: _SubParsersAction) -> _SubParsersAction:
        base.add_parser(
            'view-kcfg',
            help='Explore a given proof in the KCFG visualizer.',
            parents=[ViewKCFGOptions.all_args()],
        )
        return base


class TargetOptions(Options):
    @staticmethod
    def args(parser: ArgumentParser) -> ArgumentParser:
        parser.add_argument('--target', choices=['llvm', 'haskell', 'haskell-standalone', 'foundry'])
        return parser


class EVMChainOptions(Options):
    @staticmethod
    def args(parser: ArgumentParser) -> ArgumentParser:
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

        parser.add_argument(
            '--schedule',
            choices=schedules,
            default='SHANGHAI',
            help=f"schedule to use for execution [{'|'.join(schedules)}]",
        )
        parser.add_argument('--chainid', type=int, default=1, help='chain ID to use for execution')
        parser.add_argument(
            '--mode',
            choices=modes,
            default='NORMAL',
            help="execution mode to use [{'|'.join(modes)}]",
        )
        parser.add_argument(
            '--no-gas', action='store_false', dest='usegas', default=True, help='omit gas cost computations'
        )
        return parser


class RunOptions(LoggingOptions, KOptions, TargetOptions, EVMChainOptions):
    @staticmethod
    def parser(base: _SubParsersAction) -> _SubParsersAction:
        base.add_parser(
            'run',
            help='Run KEVM test/simulation.',
            parents=[RunOptions.all_args()],
        )
        return base

    @staticmethod
    def args(parser: ArgumentParser) -> ArgumentParser:
        parser.add_argument('input_file', type=file_path, help='Path to input file.')
        parser.add_argument(
            '--output',
            default=KRunOutput.PRETTY,
            type=KRunOutput,
            choices=list(KRunOutput),
        )
        parser.add_argument(
            '--expand-macros',
            dest='expand_macros',
            default=True,
            action='store_true',
            help='Expand macros on the input term before execution.',
        )
        parser.add_argument(
            '--no-expand-macros',
            dest='expand_macros',
            action='store_false',
            help='Do not expand macros on the input term before execution.',
        )
        parser.add_argument(
            '--debugger',
            dest='debugger',
            action='store_true',
            help='Run GDB debugger for execution.',
        )
        return parser


class KastOptions(LoggingOptions, TargetOptions, EVMChainOptions, KOptions):
    @staticmethod
    def parser(base: _SubParsersAction) -> _SubParsersAction:
        base.add_parser(
            'kast',
            help='Run KEVM program.',
            parents=[KastOptions.all_args()],
        )
        return base

    @staticmethod
    def args(parser: ArgumentParser) -> ArgumentParser:
        parser.add_argument('input_file', type=file_path, help='Path to input file.')
        parser.add_argument(
            '--output',
            default=PrintOutput.KORE,
            type=PrintOutput,
            choices=list(PrintOutput),
        )
        return parser


class KEVMCLIArgs:

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
