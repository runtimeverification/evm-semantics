from __future__ import annotations

from functools import partial
from typing import TYPE_CHECKING

import pytest

from .utils import gen_bin_runtime

if TYPE_CHECKING:
    from collections.abc import Callable
    from pathlib import Path

    from pytest import FixtureRequest, Parser


@pytest.fixture
def bin_runtime(tmp_path: Path) -> Callable[[Path], tuple[Path, str]]:
    return partial(gen_bin_runtime, output_dir=tmp_path)


def pytest_addoption(parser: Parser) -> None:
    parser.addoption(
        '--use-booster',
        action='store_true',
        default=False,
        help='Use the kore-rpc-booster binary instead of kore-rpc',
    )


@pytest.fixture(scope='module')
def use_booster(request: FixtureRequest) -> bool:
    return request.config.getoption('--use-booster')
