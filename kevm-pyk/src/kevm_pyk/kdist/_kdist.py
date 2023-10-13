from __future__ import annotations

import logging
import os
import shutil
from abc import ABC, abstractmethod
from pathlib import Path
from tempfile import TemporaryDirectory
from typing import TYPE_CHECKING

from pyk.utils import hash_str
from xdg_base_dirs import xdg_cache_home

from .. import config

if TYPE_CHECKING:
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


class Target(ABC):
    @abstractmethod
    def build(self, output_dir: Path, args: dict[str, Any]) -> None:
        ...


def targets() -> dict[str, Target]:
    from .targets import TARGETS

    return TARGETS


def check(target: str) -> None:
    if target not in targets():
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

    _target = targets()[target]

    with TemporaryDirectory(prefix=f'kevm-dist-{target}-') as build_dir_str:
        build_dir = Path(build_dir_str)
        _target.build(output_dir=build_dir, args=kwargs)
        # TODO Locking
        shutil.copytree(build_dir_str, str(res), dirs_exist_ok=True)

    return res
