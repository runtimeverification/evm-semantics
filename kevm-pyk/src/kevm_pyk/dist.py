from __future__ import annotations

import logging
import os
import shutil
import time
from abc import ABC, abstractmethod
from argparse import ArgumentParser
from concurrent.futures import ThreadPoolExecutor
from contextlib import contextmanager
from distutils.dir_util import copy_tree
from pathlib import Path
from tempfile import TemporaryDirectory
from typing import TYPE_CHECKING

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


# -------
# Targets
# -------


class Target(ABC):
    @abstractmethod
    def build(self, output_dir: Path, args: dict[str, Any]) -> None:
        ...


class KEVMTarget(Target):
    _kompile_args: dict[str, Any]

    def __init__(self, kompile_args: Mapping[str, Any]):
        self._kompile_args = dict(kompile_args)

    def build(self, output_dir: Path, args: dict[str, Any]) -> None:
        verbose = args.get('verbose', False)
        enable_llvm_debug = args.get('enable_llvm_debug', False)

        kevm_kompile(
            output_dir=output_dir,
            enable_llvm_debug=enable_llvm_debug,
            verbose=verbose,
            **self._kompile_args,
        )


class PluginTarget(Target):
    def build(self, output_dir: Path, args: dict[str, Any]) -> None:
        verbose = args.get('verbose', False)

        sync_files(
            source_dir=config.PLUGIN_DIR / 'plugin-c',
            target_dir=output_dir / 'plugin-c',
            file_names=[
                'blake2.cpp',
                'blake2.h',
                'crypto.cpp',
                'plugin_util.cpp',
                'plugin_util.h',
            ],
        )

        with self._build_env() as build_dir:
            run_process(
                ['make', 'libcryptopp', 'libff', 'libsecp256k1', '-j3'],
                cwd=build_dir,
                pipe_stdout=not verbose,
            )
            copy_tree(str(build_dir / 'build/libcryptopp'), str(output_dir / 'libcryptopp'))
            copy_tree(str(build_dir / 'build/libff'), str(output_dir / 'libff'))
            copy_tree(str(build_dir / 'build/libsecp256k1'), str(output_dir / 'libsecp256k1'))

    @contextmanager
    def _build_env(self) -> Iterator[Path]:
        with TemporaryDirectory(prefix='evm-semantics-plugin-') as build_dir_str:
            build_dir = Path(build_dir_str)
            copy_tree(str(config.PLUGIN_DIR), str(build_dir))
            yield build_dir


TARGETS: Final = {
    'llvm': KEVMTarget(
        {
            'target': KompileTarget.LLVM,
            'main_file': config.EVM_SEMANTICS_DIR / 'driver.md',
            'main_module': 'ETHEREUM-SIMULATION',
            'syntax_module': 'ETHEREUM-SIMULATION',
            'optimization': 2,
        },
    ),
    'haskell': KEVMTarget(
        {
            'target': KompileTarget.HASKELL,
            'main_file': config.EVM_SEMANTICS_DIR / 'edsl.md',
            'main_module': 'EDSL',
            'syntax_module': 'EDSL',
        },
    ),
    'haskell-standalone': KEVMTarget(
        {
            'target': KompileTarget.HASKELL_STANDALONE,
            'main_file': config.EVM_SEMANTICS_DIR / 'driver.md',
            'main_module': 'ETHEREUM-SIMULATION',
            'syntax_module': 'ETHEREUM-SIMULATION',
        },
    ),
    'foundry': KEVMTarget(
        {
            'target': KompileTarget.FOUNDRY,
            'main_file': config.EVM_SEMANTICS_DIR / 'foundry.md',
            'main_module': 'FOUNDRY',
            'syntax_module': 'FOUNDRY',
        },
    ),
    'plugin': PluginTarget(),
}


# -----
# Build
# -----


def _dist_dir() -> Path:
    dist_dir_env = os.getenv('KEVM_DIST_DIR')  # Used by Nix flake to set the output
    if dist_dir_env:
        return Path(dist_dir_env).resolve()

    digest = hash_str({'module-dir': config.MODULE_DIR})[:7]
    return xdg_cache_home() / f'evm-semantics-{digest}'


DIST_DIR: Final = _dist_dir()


def check(target: str) -> None:
    if target not in TARGETS:
        raise ValueError('Undefined target: {target}')


def which(target: str | None = None) -> Path:
    if target:
        check(target)
        return DIST_DIR / target
    return DIST_DIR


def clean(target: str | None = None) -> Path:
    res = which(target)
    shutil.rmtree(res, ignore_errors=True)
    return res


def get(target: str) -> Path:
    res = which(target)
    if not res.exists():
        raise ValueError('Target is not built: {target}')
    return res


def get_or_none(target: str) -> Path | None:
    res = which(target)
    if not res.exists():
        return None
    return res


def build(target: str, *, force: bool = False, **kwargs: Any) -> Path:
    res = which(target)
    if not force and res.exists():
        return res

    _target = TARGETS[target]

    with TemporaryDirectory(prefix=f'kevm-dist-{target}-') as build_dir_str:
        build_dir = Path(build_dir_str)
        _target.build(output_dir=build_dir, args=kwargs)
        # TODO Locking
        shutil.copytree(build_dir_str, str(res), dirs_exist_ok=True)

    return res


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
                build, target=target, force=force, enable_llvm_debug=enable_llvm_debug, verbose=verbose
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
                    pool.submit(build, target='llvm', force=force, enable_llvm_debug=enable_llvm_debug, verbose=verbose)
                )

            pending.remove(current)


def _exec_clean(target: str | None) -> None:
    res = clean(target)
    print(res)


def _exec_which(target: str | None) -> None:
    res = which(target)
    print(res)


def _parse_arguments() -> Namespace:
    targets = list(TARGETS)

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
