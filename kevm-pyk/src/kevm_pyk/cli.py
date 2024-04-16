from __future__ import annotations

import logging
from argparse import ArgumentParser
from functools import cached_property
from pathlib import Path
from typing import TYPE_CHECKING, Any

import tomli
from pyk.cli.args import BugReportOptions
from pyk.cli.args import DisplayOptions as PykDisplayOptions
from pyk.cli.args import (
    KCLIArgs,
    KDefinitionOptions,
    KompileOptions,
    LoggingOptions,
    Options,
    ParallelOptions,
    SaveDirOptions,
    SMTOptions,
    SpecOptions,
)
from pyk.cli.utils import dir_path, file_path
from pyk.kore.rpc import FallbackReason
from pyk.kore.tools import PrintOutput
from pyk.ktool.krun import KRunOutput

from .kompile import KompileTarget
from .utils import arg_pair_of

if TYPE_CHECKING:
    from argparse import Namespace
    from collections.abc import Callable
    from typing import Final, TypeVar

    from pyk.kcfg.kcfg import NodeIdLike

    T = TypeVar('T')

_LOGGER: Final = logging.getLogger(__name__)


def list_of(elem_type: Callable[[str], T], delim: str = ';') -> Callable[[str], list[T]]:
    def parse(s: str) -> list[T]:
        return [elem_type(elem) for elem in s.split(delim)]

    return parse


def node_id_like(s: str) -> NodeIdLike:
    try:
        return int(s)
    except ValueError:
        return s


def generate_options(args: dict[str, Any]) -> LoggingOptions:
    command = args['command']
    match command:
        case 'version':
            return VersionOptions(args)
        case 'kompile-spec':
            return KompileSpecOptions(args)
        case 'prove-legacy':
            return ProveLegacyOptions(args)
        case 'prove':
            return ProveOptions(args)
        case 'prune':
            return PruneOptions(args)
        case 'section-edge':
            return SectionEdgeOptions(args)
        case 'show-kcfg':
            return ShowKCFGOptions(args)
        case 'view-kcfg':
            return ViewKCFGOptions(args)
        case 'kast':
            return KastOptions(args)
        case 'run':
            return RunOptions(args)
        case _:
            raise ValueError(f'Unrecognized command: {command}')


def get_option_string_destination(command: str, option_string: str) -> str:
    option_string_destinations = {}
    match command:
        case 'version':
            option_string_destinations = VersionOptions.from_option_string()
        case 'kompile-spec':
            option_string_destinations = KompileSpecOptions.from_option_string()
        case 'prove-legacy':
            option_string_destinations = ProveLegacyOptions.from_option_string()
        case 'prove':
            option_string_destinations = ProveOptions.from_option_string()
        case 'prune':
            option_string_destinations = PruneOptions.from_option_string()
        case 'section-edge':
            option_string_destinations = SectionEdgeOptions.from_option_string()
        case 'show-kcfg':
            option_string_destinations = ShowKCFGOptions.from_option_string()
        case 'view-kcfg':
            option_string_destinations = ViewKCFGOptions.from_option_string()
        case 'kast':
            option_string_destinations = KastOptions.from_option_string()
        case 'run':
            option_string_destinations = RunOptions.from_option_string()

    if option_string in option_string_destinations:
        return option_string_destinations[option_string]
    else:
        return option_string.replace('-', '_')


def _create_argument_parser() -> ArgumentParser:
    def list_of(elem_type: Callable[[str], T], delim: str = ';') -> Callable[[str], list[T]]:
        def parse(s: str) -> list[T]:
            return [elem_type(elem) for elem in s.split(delim)]

        return parse

    kevm_cli_args = KEVMCLIArgs()
    config_args = ConfigArgs()
    parser = ArgumentParser(prog='kevm-pyk')

    command_parser = parser.add_subparsers(dest='command', required=True)

    command_parser.add_parser(
        'version', help='Print KEVM version and exit.', parents=[kevm_cli_args.logging_args, config_args.config_args]
    )

    kevm_kompile_spec_args = command_parser.add_parser(
        'kompile-spec',
        help='Kompile KEVM specification.',
        parents=[kevm_cli_args.logging_args, kevm_cli_args.k_args, kevm_cli_args.kompile_args, config_args.config_args],
    )
    kevm_kompile_spec_args.add_argument('main_file', type=file_path, help='Path to file with main module.')
    kevm_kompile_spec_args.add_argument('--target', type=KompileTarget, help='[haskell|maude]')

    kevm_kompile_spec_args.add_argument(
        '--debug-build', dest='debug_build', default=None, help='Enable debug symbols in LLVM builds.'
    )

    prove_args = command_parser.add_parser(
        'prove',
        help='Run KEVM proof.',
        parents=[
            kevm_cli_args.logging_args,
            kevm_cli_args.parallel_args,
            kevm_cli_args.k_args,
            kevm_cli_args.kprove_args,
            kevm_cli_args.rpc_args,
            kevm_cli_args.bug_report_args,
            kevm_cli_args.smt_args,
            kevm_cli_args.explore_args,
            kevm_cli_args.spec_args,
            config_args.config_args,
        ],
    )
    prove_args.add_argument(
        '--reinit',
        dest='reinit',
        default=None,
        action='store_true',
        help='Reinitialize CFGs even if they already exist.',
    )

    prune_args = command_parser.add_parser(
        'prune',
        help='Remove a node and its successors from the proof state.',
        parents=[kevm_cli_args.logging_args, kevm_cli_args.k_args, kevm_cli_args.spec_args, config_args.config_args],
    )
    prune_args.add_argument('node', type=node_id_like, help='Node to remove CFG subgraph from.')

    section_edge_args = command_parser.add_parser(
        'section-edge',
        help='Break an edge into sections.',
        parents=[kevm_cli_args.logging_args, kevm_cli_args.k_args, kevm_cli_args.spec_args, config_args.config_args],
    )
    section_edge_args.add_argument('edge', type=arg_pair_of(str, str), help='Edge to section in CFG.')
    section_edge_args.add_argument('--sections', type=int, help='Number of sections to make from edge (>= 2).')
    section_edge_args.add_argument(
        '--use-booster',
        dest='use_booster',
        default=None,
        action='store_true',
        help="Use the booster RPC server instead of kore-rpc. Requires calling kompile with '--target haskell-booster' flag",
    )

    prove_legacy_args = command_parser.add_parser(
        'prove-legacy',
        help='Run KEVM proof using the legacy kprove binary.',
        parents=[
            kevm_cli_args.logging_args,
            kevm_cli_args.k_args,
            kevm_cli_args.spec_args,
            kevm_cli_args.kprove_legacy_args,
            config_args.config_args,
        ],
    )
    prove_legacy_args.add_argument(
        '--bug-report-legacy', default=None, action='store_true', help='Generate a legacy bug report.'
    )

    command_parser.add_parser(
        'view-kcfg',
        help='Explore a given proof in the KCFG visualizer.',
        parents=[kevm_cli_args.logging_args, kevm_cli_args.k_args, kevm_cli_args.spec_args, config_args.config_args],
    )

    command_parser.add_parser(
        'show-kcfg',
        help='Print the CFG for a given proof.',
        parents=[
            kevm_cli_args.logging_args,
            kevm_cli_args.k_args,
            kevm_cli_args.kcfg_show_args,
            kevm_cli_args.spec_args,
            kevm_cli_args.display_args,
            config_args.config_args,
        ],
    )

    run_args = command_parser.add_parser(
        'run',
        help='Run KEVM test/simulation.',
        parents=[
            kevm_cli_args.logging_args,
            kevm_cli_args.target_args,
            kevm_cli_args.evm_chain_args,
            kevm_cli_args.k_args,
            config_args.config_args,
        ],
    )
    run_args.add_argument('input_file', type=file_path, help='Path to input file.')
    run_args.add_argument(
        '--output',
        type=KRunOutput,
        choices=list(KRunOutput),
    )
    run_args.add_argument(
        '--expand-macros',
        dest='expand_macros',
        default=None,
        action='store_true',
        help='Expand macros on the input term before execution.',
    )
    run_args.add_argument(
        '--no-expand-macros',
        dest='expand_macros',
        action='store_false',
        help='Do not expand macros on the input term before execution.',
    )
    run_args.add_argument(
        '--debugger',
        dest='debugger',
        action='store_true',
        help='Run GDB debugger for execution.',
    )

    kast_args = command_parser.add_parser(
        'kast',
        help='Run KEVM program.',
        parents=[
            kevm_cli_args.logging_args,
            kevm_cli_args.target_args,
            kevm_cli_args.evm_chain_args,
            kevm_cli_args.k_args,
            config_args.config_args,
        ],
    )
    kast_args.add_argument('input_file', type=file_path, help='Path to input file.')
    kast_args.add_argument(
        '--output',
        type=PrintOutput,
        choices=list(PrintOutput),
    )

    return parser


def parse_toml_args(args: Namespace) -> dict[str, Any]:
    def get_profile(toml_profile: dict[str, Any], profile_list: list[str]) -> dict[str, Any]:
        if len(profile_list) == 0 or profile_list[0] not in toml_profile:
            return {k: v for k, v in toml_profile.items() if type(v) is not dict}
        elif len(profile_list) == 1:
            return {k: v for k, v in toml_profile[profile_list[0]].items() if type(v) is not dict}
        return get_profile(toml_profile[profile_list[0]], profile_list[1:])

    toml_args: dict[str, Any] = {}
    if not hasattr(args, 'config_file') or not args.config_file.is_file():
        return {}

    with open(args.config_file, 'rb') as config_file:
        try:
            toml_args = tomli.load(config_file)
        except tomli.TOMLDecodeError:
            _LOGGER.error(
                'Input config file is not in TOML format, ignoring the file and carrying on with the provided command line agruments'
            )

    toml_args = (
        get_profile(toml_args[args.command], args.config_profile.split('.')) if args.command in toml_args else {}
    )

    toml_adj_args: dict[str, Any] = {}
    for k, v in toml_args.items():
        opt_string = get_option_string_destination(args.command, k)
        if opt_string[:3] == 'no_':
            toml_adj_args[opt_string[3:]] = not v
        elif k == 'optimization-level':
            level = toml_args[k] if toml_args[k] >= 0 else 0
            level = level if toml_args[k] <= 3 else 3
            toml_adj_args['o' + str(level)] = True
        else:
            toml_adj_args[opt_string] = v

    return toml_adj_args


class KOptions(KDefinitionOptions):
    definition_dir: Path | None
    depth: int | None

    @staticmethod
    def default() -> dict[str, Any]:
        return {
            'definition_dir': None,
            'depth': None,
        }

    @staticmethod
    def from_option_string() -> dict[str, str]:
        return {
            'definition': 'definition_dir',
        }


class KProveLegacyOptions(Options):
    bug_report: bool
    debugger: bool
    max_depth: int | None
    max_counterexamples: int | None
    branching_allowed: int | None
    haskell_backend_args: list[str]

    @staticmethod
    def default() -> dict[str, Any]:
        return {
            'bug_report': False,
            'debugger': False,
            'max_depth': None,
            'max_counterexamples': None,
            'branching_allowed': None,
            'haskell_backend_args': [],
        }


class RPCOptions(Options):
    trace_rewrites: bool
    kore_rpc_command: str | None
    use_booster: bool
    fallback_on: list[FallbackReason]
    post_exec_simplify: bool
    interim_simplification: int | None
    port: int | None
    maude_port: int | None

    @staticmethod
    def default() -> dict[str, Any]:
        return {
            'trace_rewrites': False,
            'kore_rpc_command': None,
            'use_booster': False,
            'fallback_on': [],
            'post_exec_simplify': True,
            'interim_simplification': None,
            'port': None,
            'maude_port': None,
        }


class ExploreOptions(Options):
    break_every_step: bool
    break_on_jumpi: bool
    break_on_calls: bool
    break_on_storage: bool
    break_on_basic_blocks: bool
    max_depth: int
    max_iterations: int | None
    failure_info: bool
    auto_abstract_gas: bool
    counterexample_info: bool
    fail_fast: bool

    @staticmethod
    def default() -> dict[str, Any]:
        return {
            'break_every_step': False,
            'break_on_jumpi': False,
            'break_on_calls': False,
            'break_on_storage': False,
            'break_on_basic_blocks': False,
            'max_depth': 1000,
            'max_iterations': None,
            'failure_info': True,
            'auto_abstract_gas': False,
            'counterexample_info': True,
            'fail_fast': True,
        }

    @staticmethod
    def from_option_string() -> dict[str, str]:
        return {
            'failure-information': 'failure_info',
            'no-failure-information': 'no_failure_info',
        }


class KProveOptions(Options):
    debug_equations: list[str]
    always_check_subsumption: bool
    fast_check_subsumption: bool

    @staticmethod
    def default() -> dict[str, Any]:
        return {
            'debug_equations': [],
            'always_check_subsumption': True,
            'fast_check_subsumption': False,
        }


class KCFGShowOptions(Options):
    nodes: list[NodeIdLike]
    node_deltas: list[tuple[NodeIdLike, NodeIdLike]]
    failure_info: bool
    to_module: bool
    pending: bool
    failing: bool
    counterexample_info: bool

    @staticmethod
    def default() -> dict[str, Any]:
        return {
            'nodes': [],
            'node_deltas': [],
            'failure_info': False,
            'to_module': False,
            'pending': False,
            'failing': False,
            'counterexample_info': False,
        }

    @staticmethod
    def from_option_string() -> dict[str, str]:
        return {
            'counterexample-information': 'counterexample_info',
            'no-counterexample-information': 'no_counterexample_info',
            'node': 'nodes',
            'node-delta': 'node_deltas',
        }


class TargetOptions(Options):
    target: str | None

    @staticmethod
    def default() -> dict[str, Any]:
        return {
            'target': None,
        }


class EVMChainOptions(Options):
    schedule: str
    chainid: int
    mode: str
    usegas: bool

    @staticmethod
    def default() -> dict[str, Any]:
        return {
            'schedule': 'SHANGHAI',
            'chainid': 1,
            'mode': 'NORMAL',
            'use_gas': True,
        }

    @staticmethod
    def from_option_string() -> dict[str, str]:
        return {
            'no-gas': 'no_usegas',
        }


class DisplayOptions(PykDisplayOptions):
    sort_collections: bool

    @staticmethod
    def default() -> dict[str, Any]:
        return {
            'sort_collections': False,
        }


class KGenOptions(Options):
    requires: list[str]
    imports: list[str]

    @staticmethod
    def default() -> dict[str, Any]:
        return {
            'requires': [],
            'imports': [],
        }

    @staticmethod
    def from_option_string() -> dict[str, str]:
        return {
            'require': 'requires',
            'module-import': 'imports',
        }


class VersionOptions(LoggingOptions): ...


class KompileSpecOptions(LoggingOptions, KOptions, KompileOptions):
    main_file: Path
    target: KompileTarget
    debug_build: bool

    @staticmethod
    def default() -> dict[str, Any]:
        return {
            'target': KompileTarget.HASKELL,
            'debug_build': False,
        }


class ProveLegacyOptions(LoggingOptions, KOptions, SpecOptions, KProveLegacyOptions):
    bug_report_legacy: bool

    @staticmethod
    def default() -> dict[str, Any]:
        return {
            'bug_report_legacy': False,
        }


class ProveOptions(
    LoggingOptions,
    ParallelOptions,
    KOptions,
    RPCOptions,
    BugReportOptions,
    SMTOptions,
    ExploreOptions,
    SpecOptions,
    KProveOptions,
):
    reinit: bool

    @staticmethod
    def default() -> dict[str, Any]:
        return {
            'reinit': False,
        }


class PruneOptions(LoggingOptions, KOptions, SpecOptions):
    node: NodeIdLike


class SectionEdgeOptions(
    LoggingOptions,
    KOptions,
    RPCOptions,
    SMTOptions,
    SpecOptions,
    BugReportOptions,
):
    edge: tuple[str, str]
    sections: int

    @staticmethod
    def default() -> dict[str, Any]:
        return {
            'sections': 2,
            'use_booster': False,
        }


class ShowKCFGOptions(
    LoggingOptions,
    KCFGShowOptions,
    KOptions,
    SpecOptions,
    DisplayOptions,
): ...


class ViewKCFGOptions(
    LoggingOptions,
    KOptions,
    SpecOptions,
): ...


class RunOptions(
    LoggingOptions,
    KOptions,
    EVMChainOptions,
    TargetOptions,
    SaveDirOptions,
):
    input_file: Path
    output: KRunOutput
    expand_macros: bool
    debugger: bool

    @staticmethod
    def default() -> dict[str, Any]:
        return {
            'output': KRunOutput.PRETTY,
            'expand_macros': True,
            'debugger': False,
        }


class KastOptions(
    LoggingOptions,
    TargetOptions,
    EVMChainOptions,
    KOptions,
    SaveDirOptions,
):
    input_file: Path
    output: PrintOutput

    @staticmethod
    def default() -> dict[str, Any]:
        return {
            'output': PrintOutput.KORE,
        }


class ConfigArgs:
    @cached_property
    def config_args(self) -> ArgumentParser:
        args = ArgumentParser(add_help=False)
        args.add_argument(
            '--config-file',
            dest='config_file',
            type=file_path,
            default=Path('./kevm-pyk.toml'),
            help='Path to Pyk config file.',
        )
        args.add_argument(
            '--config-profile',
            dest='config_profile',
            default='default',
            help='Config profile to be used.',
        )
        return args


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
        args.add_argument('--definition', type=dir_path, dest='definition_dir', help='Path to definition to use.')
        args.add_argument(
            '--debug-equations',
            type=list_of(str, delim=','),
            default=[],
            help='Comma-separate list of equations to debug.',
        )
        args.add_argument(
            '--always-check-subsumption',
            dest='always_check_subsumption',
            default=True,
            action='store_true',
            help='Check subsumption even on non-terminal nodes (default, experimental).',
        )
        args.add_argument(
            '--no-always-check-subsumption',
            dest='always_check_subsumption',
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
        args.add_argument('--definition', type=dir_path, dest='definition_dir', help='Path to definition to use.')
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
            help=f"schedule to use for execution [{'|'.join(schedules)}].",
        )
        args.add_argument('--chainid', type=int, default=1, help='chain ID to use for execution.')
        args.add_argument(
            '--mode',
            choices=modes,
            default='NORMAL',
            help="execution mode to use [{'|'.join(modes)}].",
        )
        args.add_argument(
            '--no-gas', action='store_false', dest='usegas', default=True, help='omit gas cost computations.'
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
            help='Custom command to start RPC server.',
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
            help='Use existing RPC server on named port.',
        )
        args.add_argument(
            '--maude-port',
            dest='maude_port',
            type=int,
            default=None,
            help='Use existing Maude RPC server on named port.',
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
            help='Show failure summary for all failing tests (default).',
        )
        args.add_argument(
            '--no-failure-information',
            dest='failure_info',
            action='store_false',
            help='Do not show failure summary for failing tests.',
        )
        args.add_argument(
            '--auto-abstract-gas',
            dest='auto_abstract_gas',
            action='store_true',
            help='Automatically extract gas cell when infinite gas is enabled.',
        )
        args.add_argument(
            '--counterexample-information',
            dest='counterexample_info',
            default=True,
            action='store_true',
            help='Show models for failing nodes (default).',
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
            help='Show failure summary for cfg.',
        )
        args.add_argument(
            '--no-failure-information',
            dest='failure_info',
            action='store_false',
            help='Do not show failure summary for cfg.',
        )
        args.add_argument(
            '--to-module', dest='to_module', default=False, action='store_true', help='Output edges as a K module.'
        )
        args.add_argument(
            '--pending', dest='pending', default=False, action='store_true', help='Also display pending nodes.'
        )
        args.add_argument(
            '--failing', dest='failing', default=False, action='store_true', help='Also display failing nodes.'
        )
        args.add_argument(
            '--counterexample-information',
            dest='counterexample_info',
            default=False,
            action='store_true',
            help="Show models for failing nodes. Should be called with the '--failure-information' flag.",
        )
        return args
