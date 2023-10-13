from __future__ import annotations

import logging
import time
from argparse import ArgumentParser
from concurrent.futures import ThreadPoolExecutor
from typing import TYPE_CHECKING

from pyk.cli.args import KCLIArgs
from pyk.cli.utils import loglevel

from .. import kdist

if TYPE_CHECKING:
    from argparse import Namespace
    from concurrent.futures import Future
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
    _LOGGER.info(f"Building targets: {', '.join(targets)}")

    verbose = verbose or debug

    delay_llvm = 'llvm' in targets and 'plugin' in targets

    with ThreadPoolExecutor(max_workers=jobs) as pool:
        pending: list[Future] = []
        plugin: Future | None = None

        for target in targets:
            if target == 'llvm' and delay_llvm:
                continue

            plugin = pool.submit(
                kdist.build, target=target, force=force, enable_llvm_debug=enable_llvm_debug, verbose=verbose
            )
            pending.append(plugin)

        while pending:
            current = next((future for future in pending if future.done()), None)

            if current is None:
                time.sleep(0.01)
                continue

            result = current.result()
            print(result)

            if current == plugin and delay_llvm:
                pending.append(
                    pool.submit(
                        kdist.build, target='llvm', force=force, enable_llvm_debug=enable_llvm_debug, verbose=verbose
                    )
                )

            pending.remove(current)


def _exec_clean(target: str | None) -> None:
    res = kdist.clean(target)
    print(res)


def _exec_which(target: str | None) -> None:
    res = kdist.which(target)
    print(res)


def _parse_arguments() -> Namespace:
    targets = list(kdist.targets())

    def target(s: str) -> str:
        #  choices does not work well with nargs="*"
        if s not in targets:
            raise TypeError()
        return s

    def add_target_arg(parser: ArgumentParser, help_text: str) -> None:
        parser.add_argument(
            'target',
            metavar='TARGET',
            nargs='?',
            choices=targets,
            help=help_text,
        )

    k_cli_args = KCLIArgs()

    parser = ArgumentParser(prog='kevm-dist', parents=[k_cli_args.logging_args])
    command_parser = parser.add_subparsers(dest='command', required=True)

    build_parser = command_parser.add_parser('build', help='build targets')
    build_parser.add_argument(
        'targets', metavar='TARGET', nargs='*', type=target, default=targets, help='target to build'
    )
    build_parser.add_argument('-f', '--force', action='store_true', default=False, help='force build')
    build_parser.add_argument('-j', '--jobs', metavar='N', type=int, default=1, help='maximal number of build jobs')
    build_parser.add_argument(
        '--enable-llvm-debug', action='store_true', default=True, help='enable debug symbols for the LLVM target'
    )

    clean_parser = command_parser.add_parser('clean', help='clean targets')
    add_target_arg(clean_parser, 'target to clean')

    which_parser = command_parser.add_parser('which', help='print target location')
    add_target_arg(which_parser, 'target to print directory for')

    return parser.parse_args()


if __name__ == '__main__':
    main()
