from __future__ import annotations

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
        '--use-booster',
        action='store_true',
        default=False,
        help='Use the kore-rpc-booster binary instead of kore-rpc',
    )
    parser.addoption(
        '--kore-rpc-command',
        type=str,
        default=None,
        help='Custom command to start RPC server',
    )


@pytest.fixture
def update_expected_output(request: FixtureRequest) -> bool:
    return request.config.getoption('--update-expected-output')


@pytest.fixture(scope='session')
def use_booster(request: FixtureRequest) -> bool:
    return request.config.getoption('--use-booster')

@pytest.fixture(scope='session')
def kore_rpc_command(request: FixtureRequest) -> str | None:
    return request.config.getoption('--kore-rpc-command')
