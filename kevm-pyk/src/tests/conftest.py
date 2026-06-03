from __future__ import annotations

from pathlib import Path
from typing import TYPE_CHECKING

import pytest

if TYPE_CHECKING:
    from pytest import FixtureRequest, Parser


def pytest_addoption(parser: Parser) -> None:
    parser.addoption(
        '--save-failing',
        action='store_true',
        default=False,
        help='Save failing tests to the failing.llvm file',
    )
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
        '--use-booster-dev',
        action='store_true',
        default=False,
        help='Use the booster-dev binary instead of kore-rpc',
    )
    parser.addoption(
        '--spec-name',
        default=None,
        type=str,
        help='Run only this specific specification (skip others)',
    )
    parser.addoption(
        '--claim-labels',
        default=None,
        type=str,
        help='Comma-separated claim labels to prove within a spec (e.g. foo-claim,bar-claim); proves all claims if omitted',
    )
    parser.addoption(
        '--kompiled-targets-dir',
        type=Path,
        help='Use pre-kompiled definitions for proof tests',
    )
    parser.addoption(
        '--force-sequential',
        default=False,
        action='store_true',
        help='Use sequential, single-threaded proof loop.',
    )
    parser.addoption(
        '--booster-log-dir',
        type=Path,
        default=None,
        help='Write per-spec Haskell backend JSON logs to this directory. Implies --haskell-logging.',
    )
    parser.addoption(
        '--haskell-logging',
        action='store_true',
        default=False,
        help='Enable KoreCalls+Simplify+SimplifyKore JSON logging for all proof tests. Use with --booster-log-dir to persist logs.',
    )
    parser.addoption(
        '--booster-log-levels',
        default=None,
        type=str,
        help=(
            'Comma-separated Booster log levels to enable (e.g. KoreCalls,Simplify,SimplifyKore,Aborts,Rewrite,SMT). '
            'Overrides the default set used by --haskell-logging. '
            'Available levels: Aborts, EquationWarnings, KoreCalls, Rewrite, RewriteKore, RewriteSuccess, '
            'Simplify, SimplifyKore, SimplifySuccess, SMT, TimeProfile, Timing.'
        ),
    )
    parser.addoption(
        '--booster-only-simplify',
        action='store_true',
        default=False,
        help='Skip the Kore simplification pass after Booster for all simplify/execute/implies calls.',
    )


@pytest.fixture
def save_failing(request: FixtureRequest) -> bool:
    return request.config.getoption('--save-failing')


@pytest.fixture
def update_expected_output(request: FixtureRequest) -> bool:
    return request.config.getoption('--update-expected-output')


@pytest.fixture(scope='session')
def no_use_booster(request: FixtureRequest) -> bool:
    return request.config.getoption('--no-use-booster')


@pytest.fixture(scope='session')
def use_booster_dev(request: FixtureRequest) -> bool:
    return request.config.getoption('--use-booster-dev')


@pytest.fixture(scope='session')
def force_sequential(request: FixtureRequest) -> bool:
    return request.config.getoption('--force-sequential')


@pytest.fixture(scope='session')
def spec_name(request: FixtureRequest) -> str | None:
    return request.config.getoption('--spec-name')


@pytest.fixture(scope='session')
def claim_labels(request: FixtureRequest) -> list[str] | None:
    raw: str | None = request.config.getoption('--claim-labels')
    if raw is None:
        return None
    return [label.strip() for label in raw.split(',') if label.strip()]


@pytest.fixture(scope='session')
def kompiled_targets_dir(request: FixtureRequest) -> Path | None:
    return request.config.getoption('--kompiled-targets-dir')


@pytest.fixture(scope='session')
def booster_log_dir(request: FixtureRequest) -> Path | None:
    d: Path | None = request.config.getoption('--booster-log-dir')
    if d is not None:
        d.mkdir(parents=True, exist_ok=True)
    return d


@pytest.fixture(scope='session')
def haskell_logging(request: FixtureRequest, booster_log_dir: Path | None) -> bool:
    return bool(request.config.getoption('--haskell-logging')) or booster_log_dir is not None


@pytest.fixture(scope='session')
def booster_log_levels(request: FixtureRequest, haskell_logging: bool) -> list[str] | None:
    """
    Return explicit log levels for the Booster backend, or None to use the default.

    When None is returned and haskell_logging is True, the test harness uses the default
    set (KoreCalls, Simplify, SimplifyKore) needed for kore-fallback analysis.

    Set via --booster-log-levels on the command line:
        pytest ... --booster-log-levels Aborts,Rewrite,SMT
    """
    raw: str | None = request.config.getoption('--booster-log-levels')
    if raw is None:
        return None
    return [level.strip() for level in raw.split(',') if level.strip()]


@pytest.fixture(scope='session')
def booster_only_simplify(request: FixtureRequest) -> bool:
    return request.config.getoption('--booster-only-simplify')
