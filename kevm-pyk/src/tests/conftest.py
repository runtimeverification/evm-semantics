from __future__ import annotations

from pathlib import Path
from typing import TYPE_CHECKING

import pytest
from pyk.cli.utils import list_of
from pyk.cterm.symbolic import HASKELL_LOGGING_ENTRIES

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
        type=list_of(str, delim=','),
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
        help='Capture per-request Haskell backend log bundles under this directory, one per-spec subdirectory of <request-id>.jsonl files. Implies --haskell-logging.',
    )
    parser.addoption(
        '--haskell-logging',
        action='store_true',
        default=False,
        help=(
            'Enable JSON logging of the default Haskell-backend entries '
            f'({",".join(HASKELL_LOGGING_ENTRIES)}) for all proof tests. '
            'Use with --booster-log-dir to persist logs.'
        ),
    )
    parser.addoption(
        '--booster-log-levels',
        default=None,
        type=list_of(str, delim=','),
        help=(
            'Comma-separated Haskell-backend log entries to enable, overriding the default set '
            f'used by --haskell-logging ({",".join(HASKELL_LOGGING_ENTRIES)}). '
            'Valid entries are defined by the backend; see its --log-level help.'
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
    return request.config.getoption('--claim-labels')


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
def booster_log_levels(request: FixtureRequest) -> list[str] | None:
    """
    Return explicit log entries for the Haskell backend, or None to use the default.

    When None is returned and haskell_logging is True, the harness falls back to
    HASKELL_LOGGING_ENTRIES. Set via --booster-log-levels on the command line:
        pytest ... --booster-log-levels Abort,Rewrite,SMT
    """
    return request.config.getoption('--booster-log-levels')


@pytest.fixture(scope='session')
def booster_only_simplify(request: FixtureRequest) -> bool:
    return request.config.getoption('--booster-only-simplify')
