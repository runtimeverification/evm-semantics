from __future__ import annotations

from typing import TYPE_CHECKING

import pytest
from pyk.cli.utils import dir_path

if TYPE_CHECKING:
    from pathlib import Path

    from pytest import FixtureRequest, Parser, TempPathFactory


def pytest_addoption(parser: Parser) -> None:
    parser.addoption(
        '--kompiled-targets-dir',
        type=dir_path,
        help='Use pre-kompiled definitions for proof tests',
    )


@pytest.fixture(scope='session')
def kompiled_targets_dir(request: FixtureRequest, tmp_path_factory: TempPathFactory) -> Path:
    dir = request.config.getoption('--kompiled-targets-dir')
    if dir:
        return dir
    else:
        return tmp_path_factory.mktemp('kompiled_targets')
