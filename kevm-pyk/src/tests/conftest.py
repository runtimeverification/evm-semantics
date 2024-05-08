from __future__ import annotations

from typing import TYPE_CHECKING

import pytest
from pyk.cli.utils import dir_path
import _pytest.skipping

if TYPE_CHECKING:
    from pathlib import Path
    from pytest import FixtureRequest, Parser, TempPathFactory


def pytest_addoption(parser: Parser) -> None:
    parser.addoption(
        '--update-expected-output',
        action='store_true',
        default=False,
        help='Write expected output files for proof tests',
    )
    parser.addoption(
        '--use-booster',
        action='store_true',
        default=False,
        help='Use the kore-rpc-booster binary instead of kore-rpc',
    )
    parser.addoption(
        '--spec-name',
        default=None,
        type=str,
        help='Run only this specific specification (skip others)',
    )
    parser.addoption(
        '--kompiled-targets-dir',
        type=dir_path,
        help='Use pre-kompiled definitions for proof tests',
    )


@pytest.fixture
def update_expected_output(request: FixtureRequest) -> bool:
    return request.config.getoption('--update-expected-output')


@pytest.fixture(scope='session')
def use_booster(request: FixtureRequest) -> bool:
    return request.config.getoption('--use-booster')


@pytest.fixture(scope='session')
def spec_name(request: FixtureRequest) -> str | None:
    return request.config.getoption('--spec-name')


@pytest.fixture(scope='session')
def kompiled_targets_dir(request: FixtureRequest, tmp_path_factory: TempPathFactory) -> Path:
    dir = request.config.getoption('--kompiled-targets-dir')
    if dir:
        return dir
    else:
        return tmp_path_factory.mktemp('prekompiled')
