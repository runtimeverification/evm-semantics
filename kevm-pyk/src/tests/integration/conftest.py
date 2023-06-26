from __future__ import annotations

from functools import partial
from typing import TYPE_CHECKING

import pytest

from .utils import gen_bin_runtime

if TYPE_CHECKING:
    from collections.abc import Callable
    from pathlib import Path


@pytest.fixture
def bin_runtime(tmp_path: Path) -> Callable[[Path], tuple[Path, str]]:
    return partial(gen_bin_runtime, output_dir=tmp_path)
