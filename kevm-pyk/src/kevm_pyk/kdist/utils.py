from __future__ import annotations

import inspect
import os
from contextlib import contextmanager
from pathlib import Path
from typing import TYPE_CHECKING

from pyk.utils import check_dir_path

if TYPE_CHECKING:
    from collections.abc import Iterator
    from typing import Any


def package_path(obj: Any) -> Path:
    module = inspect.getmodule(obj)

    if not module:
        raise ValueError(f'Module not found object: {obj}')

    if not module.__file__:
        raise ValueError(f'Path not found for module: {module.__name__}')

    package_path = Path(module.__file__).parent.resolve()
    while True:
        init_file = package_path / '__init__.py'
        if not init_file.exists():
            return package_path
        if not package_path.parent.exists():
            return package_path
        package_path = package_path.parent


def files_for_path(path: str | Path) -> list[Path]:
    path = Path(path)

    if not path.exists():
        raise ValueError(f'Path does not exist: {path}')

    if path.is_file():
        return [path]

    return [file for file in path.rglob('*') if file.is_file()]


def timestamp(path: Path) -> int:
    return path.stat().st_mtime_ns


@contextmanager
def cwd(path: Path) -> Iterator[None]:
    check_dir_path(path)
    old_cwd = os.getcwd()
    os.chdir(str(path))
    yield
    os.chdir(old_cwd)
