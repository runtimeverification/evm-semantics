from __future__ import annotations

import csv
import json
import logging
import sys
from typing import TYPE_CHECKING

import pytest

from kevm_pyk.interpreter import interpret

from ..utils import REPO_ROOT, _assert_exit_code_zero, _skipped_tests

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


def _test(gst_file: Path, *, schedule: str, mode: str, usegas: bool, save_failing: bool) -> None:
    skipped_gst_tests = SKIPPED_TESTS.get(gst_file, [])
    if '*' in skipped_gst_tests:
        pytest.skip()

    failing_tests: list[str] = []
    gst_file_relative_path: Final[str] = str(gst_file.relative_to(TEST_DIR))

    with gst_file.open() as f:
        gst_data = json.load(f)

    for test_name, test in gst_data.items():
        _LOGGER.info(f'Running test: {gst_file} - {test_name}')
        if test_name in skipped_gst_tests:
            continue
        res = interpret({test_name: test}, schedule, mode, 1, usegas, check=False)

        try:
            _assert_exit_code_zero(res)
        except AssertionError:
            if not save_failing:
                raise
            failing_tests.append(test_name)

    if not failing_tests:
        return
    if save_failing:
        with FAILING_TESTS_FILE.open('a', newline='') as ff:
            writer = csv.writer(ff)
            if len(failing_tests) == len(gst_data):
                writer.writerow([gst_file_relative_path, '*'])
            else:
                for test_name in sorted(failing_tests):
                    writer.writerow([gst_file_relative_path, test_name])
    raise AssertionError(f'Found failing tests in GST file {gst_file_relative_path}: {failing_tests}')


BCHAIN_TEST_DIR: Final = TEST_DIR / 'blockchain_tests'
BCHAIN_TESTS: Final = tuple(BCHAIN_TEST_DIR.rglob('**/*.json'))


@pytest.mark.parametrize(
    'test_file',
    BCHAIN_TESTS,
    ids=[str(test_file.relative_to(BCHAIN_TEST_DIR)) for test_file in BCHAIN_TESTS],
)
def test_bchain(test_file: Path, save_failing: bool) -> None:
    _test(test_file, schedule='CANCUN', mode='NORMAL', usegas=True, save_failing=save_failing)


BCHAIN_ENGINE_TEST_DIR: Final = TEST_DIR / 'blockchain_tests_engine'
BCHAIN_ENGINE_TESTS: Final = tuple(BCHAIN_ENGINE_TEST_DIR.rglob('**/*.json'))


@pytest.mark.parametrize(
    'test_file',
    BCHAIN_ENGINE_TESTS,
    ids=[str(test_file.relative_to(BCHAIN_ENGINE_TEST_DIR)) for test_file in BCHAIN_ENGINE_TESTS],
)
def test_bchain_engine(test_file: Path, save_failing: bool) -> None:
    _test(test_file, schedule='CANCUN', mode='NORMAL', usegas=True, save_failing=save_failing)


STATE_TEST_DIR: Final = TEST_DIR / 'state_tests'
STATE_TESTS: Final = tuple(STATE_TEST_DIR.rglob('**/*.json'))


@pytest.mark.parametrize(
    'test_file',
    STATE_TESTS,
    ids=[str(test_file.relative_to(STATE_TEST_DIR)) for test_file in STATE_TESTS],
)
def test_state(test_file: Path, save_failing: bool) -> None:
    _test(test_file, schedule='CANCUN', mode='NORMAL', usegas=True, save_failing=save_failing)


TRANSACTION_TEST_DIR: Final = TEST_DIR / 'transaction_tests'
TRANSACTION_TESTS: Final = tuple(TRANSACTION_TEST_DIR.rglob('**/*.json'))


@pytest.mark.parametrize(
    'test_file',
    TRANSACTION_TESTS,
    ids=[str(test_file.relative_to(TRANSACTION_TEST_DIR)) for test_file in TRANSACTION_TESTS],
)
def test_transaction(test_file: Path, save_failing: bool) -> None:
    _test(test_file, schedule='CANCUN', mode='NORMAL', usegas=True, save_failing=save_failing)
