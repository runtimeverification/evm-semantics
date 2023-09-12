from __future__ import annotations

import logging
import shutil
from pathlib import Path
from typing import TYPE_CHECKING

from pyk.utils import hash_str
from xdg_base_dirs import xdg_cache_home

import kevm_pyk

from .kompile import KompileTarget, kevm_kompile

if TYPE_CHECKING:
    from collections.abc import Mapping
    from typing import Any, Final


_LOGGER: Final = logging.getLogger(__name__)


MODULE_DIR: Final = Path(kevm_pyk.__file__).parent
DIGEST: Final = hash_str({'module-dir': MODULE_DIR})[:7]
DIST_DIR: Final = xdg_cache_home() / f'evm-semantics-{DIGEST}'
KPROJ_DIR: Final = MODULE_DIR / 'kproj'
KSRC_DIR: Final = KPROJ_DIR / 'evm-semantics'


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
        'main_file': KSRC_DIR / 'driver.md',
        'main_module': 'ETHEREUM-SIMULATION',
        'syntax_module': 'ETHEREUM-SIMULATION',
    },
    'haskell': {
        'target': KompileTarget.HASKELL,
        'main_file': KSRC_DIR / 'edsl.md',
        'main_module': 'EDSL',
        'syntax_module': 'EDSL',
    },
    'haskell-standalone': {
        'target': KompileTarget.HASKELL_STANDALONE,
        'main_file': KSRC_DIR / 'driver.md',
        'main_module': 'ETHEREUM-SIMULATION',
        'syntax_module': 'ETHEREUM-SIMULATION',
    },
    'foundry': {
        'target': KompileTarget.FOUNDRY,
        'main_file': KSRC_DIR / 'foundry.md',
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
