from __future__ import annotations

import logging
import shutil
from contextlib import contextmanager
from distutils.dir_util import copy_tree
from pathlib import Path
from subprocess import CalledProcessError
from tempfile import TemporaryDirectory
from typing import TYPE_CHECKING

from pyk.kbuild.utils import sync_files
from pyk.utils import hash_str, run_process
from xdg_base_dirs import xdg_cache_home

from . import config
from .kompile import KompileTarget, kevm_kompile

if TYPE_CHECKING:
    from collections.abc import Iterator, Mapping
    from typing import Any, Final


_LOGGER: Final = logging.getLogger(__name__)


DIGEST: Final = hash_str({'module-dir': config.MODULE_DIR})[:7]
DIST_DIR: Final = xdg_cache_home() / f'evm-semantics-{DIGEST}'


# ---------
# K targets
# ---------


def build(target: str) -> Path:
    target_dir = _target_dir(target)
    _LOGGER.info(f'Building target: {target_dir}')
    target_dir.mkdir(parents=True, exist_ok=True)
    return kevm_kompile(output_dir=target_dir, **_TARGETS[target])


def clean(target: str | None = None) -> Path:
    dir_to_clean = _target_dir(target) if target is not None else DIST_DIR
    shutil.rmtree(dir_to_clean, ignore_errors=True)
    return dir_to_clean


def llvm_dir() -> Path:
    return _get('llvm')


def haskell_dir() -> Path:
    return _get('haskell')


def haskell_standalone_dir() -> Path:
    return _get('haskell-standalone')


def foundry_dir() -> Path:
    return _get('foundry')


_TARGETS: Final[Mapping[str, Any]] = {
    'llvm': {
        'target': KompileTarget.LLVM,
        'main_file': config.EVM_SEMANTICS_DIR / 'driver.md',
        'main_module': 'ETHEREUM-SIMULATION',
        'syntax_module': 'ETHEREUM-SIMULATION',
    },
    'haskell': {
        'target': KompileTarget.HASKELL,
        'main_file': config.EVM_SEMANTICS_DIR / 'edsl.md',
        'main_module': 'EDSL',
        'syntax_module': 'EDSL',
    },
    'haskell-standalone': {
        'target': KompileTarget.HASKELL_STANDALONE,
        'main_file': config.EVM_SEMANTICS_DIR / 'driver.md',
        'main_module': 'ETHEREUM-SIMULATION',
        'syntax_module': 'ETHEREUM-SIMULATION',
    },
    'foundry': {
        'target': KompileTarget.FOUNDRY,
        'main_file': config.EVM_SEMANTICS_DIR / 'foundry.md',
        'main_module': 'FOUNDRY',
        'syntax_module': 'FOUNDRY',
    },
}


def _get(target: str) -> Path:
    target_dir = _target_dir(target)
    if target_dir.exists():
        return target_dir
    return build(target)


def _target_dir(target: str) -> Path:
    _check_target(target)
    return DIST_DIR / target


def _check_target(target: str) -> None:
    if target not in _TARGETS:
        raise ValueError(f'Unknown build target: {target}')


# --------------
# Plugin project
# --------------


def plugin_dir() -> Path:
    target_dir = DIST_DIR / 'plugin'
    if target_dir.exists():
        return target_dir
    return build_plugin()


def build_plugin() -> Path:
    target_dir = DIST_DIR / 'plugin'

    _LOGGER.info(f'Building plugin project: {target_dir}')

    sync_files(
        source_dir=config.PLUGIN_DIR / 'plugin-c',
        target_dir=target_dir / 'plugin-c',
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
            run_process(['make', 'libcryptopp', 'libff', 'libsecp256k1'], cwd=build_dir, pipe_stdout=False)
        except CalledProcessError as err:
            shutil.rmtree(DIST_DIR / 'plugin')
            raise RuntimeError('Compilation of native dependencies failed') from err

        output_dir = build_dir / 'build'
        copy_tree(str(output_dir / 'libcryptopp'), str(target_dir / 'libcryptopp'))
        copy_tree(str(output_dir / 'libff'), str(target_dir / 'libff'))
        copy_tree(str(output_dir / 'libsecp256k1'), str(target_dir / 'libsecp256k1'))

    return target_dir


@contextmanager
def _plugin_build_env() -> Iterator[Path]:
    with TemporaryDirectory(prefix='evm-semantics-plugin-') as build_dir_str:
        build_dir = Path(build_dir_str)
        copy_tree(str(config.PLUGIN_DIR), str(build_dir))
        yield build_dir
