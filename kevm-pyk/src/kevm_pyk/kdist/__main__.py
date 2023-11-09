from __future__ import annotations

import fnmatch
import logging
from argparse import ArgumentParser
from typing import TYPE_CHECKING

from pyk.cli.args import KCLIArgs
from pyk.cli.utils import loglevel

from .. import kdist

if TYPE_CHECKING:
    from argparse import Namespace
    from typing import Final


_LOGGER: Final = logging.getLogger(__name__)
_LOG_FORMAT: Final = '%(levelname)s %(asctime)s %(name)s - %(message)s'


def main() -> None:
    args = _parse_arguments()

    logging.basicConfig(level=loglevel(args), format=_LOG_FORMAT)

    if args.command == 'build':
        _exec_build(**vars(args))

    elif args.command == 'clean':
        _exec_clean(args.target)

    elif args.command == 'which':
        _exec_which(args.target)

    elif args.command == 'list':
        _exec_list()

    else:
        raise AssertionError()


def _exec_build(
    command: str,
    targets: list[str],
    jobs: int,
    force: bool,
    enable_llvm_debug: bool,
    verbose: bool,
    debug: bool,
) -> None:
    all_target_fqns = kdist.targets()
    target_fqns = []
    for pattern in targets:
        matches = fnmatch.filter(all_target_fqns, pattern)
        if not matches:
            raise ValueError(f'No target matches pattern: {pattern!r}')
        target_fqns += matches

    verbose = verbose or debug
    kdist.build(
        target_fqns=target_fqns,
        jobs=jobs,
        force=force,
        enable_llvm_debug=enable_llvm_debug,
        verbose=verbose,
    )


def _exec_clean(target: str | None) -> None:
    res = kdist.clean(target)
    print(res)


def _exec_which(target: str | None) -> None:
    res = kdist.which(target)
    print(res)


def _exec_list() -> None:
    plugins = kdist.plugins()
    for plugin in plugins:
        print(plugin)
        for target in plugins[plugin]:
            print(f'* {target}')


def _parse_arguments() -> Namespace:
    def add_target_arg(parser: ArgumentParser, help_text: str) -> None:
        parser.add_argument(
            'target',
            metavar='TARGET',
            nargs='?',
            help=help_text,
        )

    k_cli_args = KCLIArgs()

    parser = ArgumentParser(prog='kevm-dist', parents=[k_cli_args.logging_args])
    command_parser = parser.add_subparsers(dest='command', required=True)

    build_parser = command_parser.add_parser('build', help='build targets')
    build_parser.add_argument('targets', metavar='TARGET', nargs='*', default='*', help='target to build')
    build_parser.add_argument('-f', '--force', action='store_true', default=False, help='force build')
    build_parser.add_argument('-j', '--jobs', metavar='N', type=int, default=1, help='maximal number of build jobs')
    build_parser.add_argument(
        '--enable-llvm-debug', action='store_true', default=True, help='enable debug symbols for the LLVM target'
    )

    clean_parser = command_parser.add_parser('clean', help='clean targets')
    add_target_arg(clean_parser, 'target to clean')

    which_parser = command_parser.add_parser('which', help='print target location')
    add_target_arg(which_parser, 'target to print directory for')

    command_parser.add_parser('list', help='print list of available targets')

    return parser.parse_args()


if __name__ == '__main__':
    main()
