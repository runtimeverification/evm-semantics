from __future__ import annotations

from pathlib import Path
from typing import TYPE_CHECKING

import pytest

if TYPE_CHECKING:
    from pytest import FixtureRequest, Parser


def pytest_addoption(parser: Parser) -> None:
    parser.addoption(
        '--update-expected-output',
        action='store_true',
        default=False,
        help='Write expected output files for proof tests',
    )
    parser.addoption(
        '--no-use-booster',
        action='store_true',
        default=False,
        help='Do not the kore-rpc-booster binary instead of kore-rpc',
    )
    parser.addoption(
        '--spec-name',
        default=None,
        type=str,
        help='Run only this specific specification (skip others)',
    )
    parser.addoption(
        '--kompiled-targets-dir',
        type=Path,
        help='Use pre-kompiled definitions for proof tests',
    )


@pytest.fixture
def update_expected_output(request: FixtureRequest) -> bool:
    return request.config.getoption('--update-expected-output')


@pytest.fixture(scope='session')
def no_use_booster(request: FixtureRequest) -> bool:
    return request.config.getoption('--no-use-booster')


@pytest.fixture(scope='session')
def spec_name(request: FixtureRequest) -> str | None:
    return request.config.getoption('--spec-name')


@pytest.fixture(scope='session')
def kompiled_targets_dir(request: FixtureRequest) -> Path | None:
    return request.config.getoption('--kompiled-targets-dir')
