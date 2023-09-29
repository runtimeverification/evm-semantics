from __future__ import annotations

import logging
import os
import shutil
import time
from argparse import ArgumentParser
from concurrent.futures import ThreadPoolExecutor
from contextlib import contextmanager
from distutils.dir_util import copy_tree
from enum import Enum
from pathlib import Path
from subprocess import CalledProcessError
from tempfile import TemporaryDirectory
from typing import TYPE_CHECKING, Literal

from pyk.cli.args import KCLIArgs
from pyk.cli.utils import loglevel
from pyk.kbuild.utils import sync_files
from pyk.utils import hash_str, run_process
from xdg_base_dirs import xdg_cache_home

from . import config
from .kompile import KompileTarget, kevm_kompile

if TYPE_CHECKING:
    from argparse import Namespace
    from collections.abc import Iterator, Mapping
    from concurrent.futures import Future
    from typing import Any, Final


_LOGGER: Final = logging.getLogger(__name__)
_LOG_FORMAT: Final = '%(levelname)s %(asctime)s %(name)s - %(message)s'


def _dist_dir() -> Path:
    dist_dir_env = os.getenv('KEVM_DIST_DIR')  # Used by Nix flake to set the output
    if dist_dir_env:
        return Path(dist_dir_env).resolve()

    digest = hash_str({'module-dir': config.MODULE_DIR})[:7]
    return xdg_cache_home() / f'evm-semantics-{digest}'


DIST_DIR: Final = _dist_dir()


# ---------
# K targets
# ---------


class DistTarget(Enum):
    LLVM = 'llvm'
    HASKELL = 'haskell'
    HASKELL_STANDALONE = 'haskell-standalone'
    FOUNDRY = 'foundry'

    @property
    def path(self) -> Path:
        return DIST_DIR / self.value

    def get(self) -> Path:
        if not self.path.exists():
            raise ValueError(f'Target {self.name} is not built')
        return self.path

    def get_or_none(self) -> Path | None:
        if not self.path.exists():
            return None
        return self.path

    def build(self, *, force: bool = False, enable_llvm_debug: bool = False, verbose: bool = False) -> Path:
        if force or not self.path.exists():
            self._do_build(enable_llvm_debug=enable_llvm_debug, verbose=verbose)
        return self.path

    def clean(self) -> Path:
        shutil.rmtree(self.path, ignore_errors=True)
        return self.path

    def _do_build(self, *, enable_llvm_debug: bool, verbose: bool) -> None:
        _LOGGER.info(f'Building target {self.name}: {self.path}')
        DIST_DIR.mkdir(parents=True, exist_ok=True)
        try:
            kevm_kompile(
                output_dir=self.path, enable_llvm_debug=enable_llvm_debug, verbose=verbose, **_TARGET_PARAMS[self]
            )
        except RuntimeError:
            self.clean()
            raise


_TARGET_PARAMS: Final[Mapping[DistTarget, Any]] = {
    DistTarget.LLVM: {
        'target': KompileTarget.LLVM,
        'main_file': config.EVM_SEMANTICS_DIR / 'driver.md',
        'main_module': 'ETHEREUM-SIMULATION',
        'syntax_module': 'ETHEREUM-SIMULATION',
        'optimization': 2,
    },
    DistTarget.HASKELL: {
        'target': KompileTarget.HASKELL,
        'main_file': config.EVM_SEMANTICS_DIR / 'edsl.md',
        'main_module': 'EDSL',
        'syntax_module': 'EDSL',
    },
    DistTarget.HASKELL_STANDALONE: {
        'target': KompileTarget.HASKELL_STANDALONE,
        'main_file': config.EVM_SEMANTICS_DIR / 'driver.md',
        'main_module': 'ETHEREUM-SIMULATION',
        'syntax_module': 'ETHEREUM-SIMULATION',
    },
    DistTarget.FOUNDRY: {
        'target': KompileTarget.FOUNDRY,
        'main_file': config.EVM_SEMANTICS_DIR / 'foundry.md',
        'main_module': 'FOUNDRY',
        'syntax_module': 'FOUNDRY',
    },
}


# --------------
# Plugin project
# --------------


PLUGIN_DIR: Final = DIST_DIR / 'plugin'


def check_plugin() -> Path:
    if not PLUGIN_DIR.exists():
        raise ValueError('Plugin project is not built')
    return PLUGIN_DIR


def build_plugin(*, force: bool = False, verbose: bool = False) -> Path:
    if force or not PLUGIN_DIR.exists():
        _do_build_plugin(verbose=verbose)
    return PLUGIN_DIR


def clean_plugin() -> Path:
    shutil.rmtree(PLUGIN_DIR, ignore_errors=True)
    return PLUGIN_DIR


def _do_build_plugin(*, verbose: bool) -> None:
    _LOGGER.info(f'Building Plugin project: {PLUGIN_DIR}')

    sync_files(
        source_dir=config.PLUGIN_DIR / 'plugin-c',
        target_dir=PLUGIN_DIR / 'plugin-c',
        file_names=[
            'blake2.cpp',
            'blake2.h',
            'crypto.cpp',
            'plugin_util.cpp',
            'plugin_util.h',
        ],
    )

    with _plugin_build_env() as build_dir:
        try:
            run_process(['make', 'libcryptopp', 'libff', 'libsecp256k1', '-j3'], cwd=build_dir, pipe_stdout=not verbose)
        except CalledProcessError:
            clean_plugin()
            raise

        output_dir = build_dir / 'build'
        copy_tree(str(output_dir / 'libcryptopp'), str(PLUGIN_DIR / 'libcryptopp'))
        copy_tree(str(output_dir / 'libff'), str(PLUGIN_DIR / 'libff'))
        copy_tree(str(output_dir / 'libsecp256k1'), str(PLUGIN_DIR / 'libsecp256k1'))


@contextmanager
def _plugin_build_env() -> Iterator[Path]:
    with TemporaryDirectory(prefix='evm-semantics-plugin-') as build_dir_str:
        build_dir = Path(build_dir_str)
        copy_tree(str(config.PLUGIN_DIR), str(build_dir))
        yield build_dir


# ---
# CLI
# ---


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


CliTarget = DistTarget | Literal['plugin']


def _exec_build(
    command: str,
    targets: list[str],
    jobs: int,
    force: bool,
    enable_llvm_debug: bool,
    verbose: bool,
    debug: bool,
) -> None:
    _LOGGER.info(f"Building tagets: {', '.join(targets)}")

    verbose = verbose or debug

    delay_llvm = 'llvm' in targets and 'plugin' in targets

    with ThreadPoolExecutor(max_workers=jobs) as pool:
        pending: list[Future] = []
        plugin: Future | None = None

        for target in targets:
            if target == 'llvm' and delay_llvm:
                continue

            if target == 'plugin':
                plugin = pool.submit(build_plugin, force=force, verbose=verbose)
                pending.append(plugin)
                continue

            pending.append(
                pool.submit(DistTarget(target).build, force=force, enable_llvm_debug=enable_llvm_debug, verbose=verbose)
            )

        while pending:
            current = next((future for future in pending if future.done()), None)

            if current is None:
                time.sleep(0.1)
                continue

            result = current.result()
            print(result)

            if current == plugin and delay_llvm:
                pending += [pool.submit(DistTarget.LLVM.build, force=force)]

            pending.remove(current)


def _exec_clean(target: str | None) -> None:
    if not target:
        shutil.rmtree(DIST_DIR, ignore_errors=True)
        print(DIST_DIR)
        return

    cli_target = _cli_target(target)
    if isinstance(cli_target, DistTarget):
        cli_target.clean()
        print(cli_target.path)
        return

    clean_plugin()
    print(PLUGIN_DIR)


def _exec_which(target: str | None) -> None:
    if not target:
        print(DIST_DIR)
        return

    cli_target = _cli_target(target)
    if isinstance(cli_target, DistTarget):
        print(cli_target.path)
        return

    print(PLUGIN_DIR)


def _parse_arguments() -> Namespace:
    targets = [item.value for item in DistTarget] + ['plugin']

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


def _cli_target(s: str) -> CliTarget:
    try:
        return DistTarget(s)
    except ValueError:
        if s == 'plugin':
            return 'plugin'
        raise TypeError(f'Invalid target: {s}') from None


if __name__ == '__main__':
    main()
