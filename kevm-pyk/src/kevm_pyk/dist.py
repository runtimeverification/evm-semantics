from __future__ import annotations

import logging
import shutil
from contextlib import contextmanager
from distutils.dir_util import copy_tree
from enum import Enum
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


class DistTarget(Enum):
    LLVM = 'llvm'
    HASKELL = 'haskell'
    HASKELL_STANDALONE = 'haskell-standalone'
    FOUNDRY = 'foundry'

    @property
    def path(self) -> Path:
        return DIST_DIR / self.value

    def get(self) -> Path | None:
        if not self.path.exists():
            return None
        return self.path

    def check(self) -> Path:
        if not self.path.exists():
            raise ValueError(f'Target {self.name} is not built')
        return self.path

    def build(self, *, force: bool = False) -> Path:
        if force or not self.path.exists():
            self._do_build()
        return self.path

    def clean(self) -> Path:
        shutil.rmtree(self.path, ignore_errors=True)
        return self.path

    def _do_build(self) -> None:
        _LOGGER.info(f'Building target {self.name}: {self.path}')
        self.path.mkdir(parents=True, exist_ok=True)
        kevm_kompile(output_dir=self.path, **_TARGET_PARAMS[self])


_TARGET_PARAMS: Final[Mapping[DistTarget, Any]] = {
    DistTarget.LLVM: {
        'target': KompileTarget.LLVM,
        'main_file': config.EVM_SEMANTICS_DIR / 'driver.md',
        'main_module': 'ETHEREUM-SIMULATION',
        'syntax_module': 'ETHEREUM-SIMULATION',
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


def build_plugin(force: bool = False) -> Path:
    if force or not PLUGIN_DIR.exists():
        _do_build_plugin()
    return PLUGIN_DIR


def clean_plugin() -> Path:
    shutil.rmtree(PLUGIN_DIR, ignore_errors=True)
    return PLUGIN_DIR


def _do_build_plugin() -> None:
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
            run_process(['make', 'libcryptopp', 'libff', 'libsecp256k1'], cwd=build_dir, pipe_stdout=False)
        except CalledProcessError as err:
            clean_plugin()
            raise RuntimeError('Compilation of native dependencies of Plugin failed') from err

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
