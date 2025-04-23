from __future__ import annotations

import logging
import sys
from typing import TYPE_CHECKING

import pytest

from ..utils import REPO_ROOT, _skipped_tests, _test

if TYPE_CHECKING:
    from pathlib import Path
    from typing import Final


_LOGGER: Final = logging.getLogger(__name__)

sys.setrecursionlimit(10**8)

WORK_DIR: Final = REPO_ROOT / 'tests/execution-spec-tests'
TEST_DIR: Final = WORK_DIR / 'fixtures'
FAILING_TESTS_FILE: Final = WORK_DIR / 'failing.llvm'
SLOW_TESTS_FILE: Final = WORK_DIR / 'slow.llvm'

SKIPPED_TESTS: Final = _skipped_tests(TEST_DIR, SLOW_TESTS_FILE, FAILING_TESTS_FILE)


BCHAIN_TEST_DIR: Final = TEST_DIR / 'blockchain_tests'
BCHAIN_TESTS: Final = tuple(BCHAIN_TEST_DIR.rglob('**/*.json'))


def chain_id_always_one(_file: str) -> int:
    return 1


@pytest.mark.parametrize(
    'test_file',
    BCHAIN_TESTS,
    ids=[str(test_file.relative_to(BCHAIN_TEST_DIR)) for test_file in BCHAIN_TESTS],
)
def test_bchain(test_file: Path, save_failing: bool) -> None:
    _test(
        test_file,
        schedule='PRAGUE',
        mode='NORMAL',
        usegas=True,
        save_failing=save_failing,
        compute_chain_id=chain_id_always_one,
        skipped_tests=SKIPPED_TESTS,
        test_dir=TEST_DIR,
        failing_tests_file=FAILING_TESTS_FILE,
    )


BCHAIN_ENGINE_TEST_DIR: Final = TEST_DIR / 'blockchain_tests_engine'
BCHAIN_ENGINE_TESTS: Final = tuple(BCHAIN_ENGINE_TEST_DIR.rglob('**/*.json'))


@pytest.mark.parametrize(
    'test_file',
    BCHAIN_ENGINE_TESTS,
    ids=[str(test_file.relative_to(BCHAIN_ENGINE_TEST_DIR)) for test_file in BCHAIN_ENGINE_TESTS],
)
def test_bchain_engine(test_file: Path, save_failing: bool) -> None:
    _test(
        test_file,
        schedule='PRAGUE',
        mode='NORMAL',
        usegas=True,
        save_failing=save_failing,
        compute_chain_id=chain_id_always_one,
        skipped_tests=SKIPPED_TESTS,
        test_dir=TEST_DIR,
        failing_tests_file=FAILING_TESTS_FILE,
    )


STATE_TEST_DIR: Final = TEST_DIR / 'state_tests'
STATE_TESTS: Final = tuple(STATE_TEST_DIR.rglob('**/*.json'))


@pytest.mark.parametrize(
    'test_file',
    STATE_TESTS,
    ids=[str(test_file.relative_to(STATE_TEST_DIR)) for test_file in STATE_TESTS],
)
def test_state(test_file: Path, save_failing: bool) -> None:
    _test(
        test_file,
        schedule='PRAGUE',
        mode='NORMAL',
        usegas=True,
        save_failing=save_failing,
        compute_chain_id=chain_id_always_one,
        skipped_tests=SKIPPED_TESTS,
        test_dir=TEST_DIR,
        failing_tests_file=FAILING_TESTS_FILE,
    )


TRANSACTION_TEST_DIR: Final = TEST_DIR / 'transaction_tests'
TRANSACTION_TESTS: Final = tuple(TRANSACTION_TEST_DIR.rglob('**/*.json'))


@pytest.mark.parametrize(
    'test_file',
    TRANSACTION_TESTS,
    ids=[str(test_file.relative_to(TRANSACTION_TEST_DIR)) for test_file in TRANSACTION_TESTS],
)
def test_transaction(test_file: Path, save_failing: bool) -> None:
    _test(
        test_file,
        schedule='PRAGUE',
        mode='NORMAL',
        usegas=True,
        save_failing=save_failing,
        compute_chain_id=chain_id_always_one,
        skipped_tests=SKIPPED_TESTS,
        test_dir=TEST_DIR,
        failing_tests_file=FAILING_TESTS_FILE,
    )
