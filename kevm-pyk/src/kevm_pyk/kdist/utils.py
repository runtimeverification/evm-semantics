from __future__ import annotations

import os
from contextlib import contextmanager
from typing import TYPE_CHECKING

from pyk.utils import check_dir_path

if TYPE_CHECKING:
    from collections.abc import Iterator
    from pathlib import Path


@contextmanager
def cwd(path: Path) -> Iterator[None]:
    check_dir_path(path)
    old_cwd = os.getcwd()
    os.chdir(str(path))
    yield
    os.chdir(old_cwd)
