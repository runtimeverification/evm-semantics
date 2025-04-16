from __future__ import annotations

import csv
import json
import logging
import sys
from pathlib import Path
from typing import TYPE_CHECKING

import pytest
from pyk.kdist import kdist
from pyk.kore.prelude import int_dv
from pyk.kore.syntax import App
from pyk.kore.tools import PrintOutput, kore_print

from kevm_pyk.interpreter import interpret

from ..utils import REPO_ROOT

if TYPE_CHECKING:
    from typing import Final

    from pyk.kore.syntax import Pattern


_LOGGER: Final = logging.getLogger(__name__)

sys.setrecursionlimit(10**8)

WORK_DIR: Final = REPO_ROOT / 'tests/execution-spec-tests'
TEST_DIR: Final = REPO_ROOT / 'tests/execution-spec-tests/fixtures'
GOLDEN: Final = (REPO_ROOT / 'tests/templates/output-success-llvm.json').read_text().rstrip()
TEST_FILES_WITH_CID_0: Final = (REPO_ROOT / 'tests/bchain.0.chainId').read_text().splitlines()
FAILING_TESTS_FILE: Final = WORK_DIR / 'failing.llvm'
SLOW_TESTS_FILE: Final = WORK_DIR / 'slow.llvm'
DOWNLOAD_FILE: Final = WORK_DIR / 'get_execution_spec_tests.sh'


def _test(gst_file: Path, *, schedule: str, mode: str, usegas: bool, save_failing: bool) -> None:
    skipped_gst_tests = SKIPPED_TESTS.get(gst_file, [])
    if '*' in skipped_gst_tests:
        pytest.skip()

    failing_tests: list[str] = []
    gst_file_relative_path: Final[str] = str(gst_file.relative_to(TEST_DIR))
    chainid = 0 if gst_file_relative_path in TEST_FILES_WITH_CID_0 else 1

    with gst_file.open() as f:
        gst_data = json.load(f)

    for test_name, test in gst_data.items():
        _LOGGER.info(f'Running test: {gst_file} - {test_name}')
        if test_name in skipped_gst_tests:
            continue
        res = interpret({test_name: test}, schedule, mode, chainid, usegas, check=False)

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


def _assert_exit_code_zero(pattern: Pattern) -> None:
    assert type(pattern) is App
    kevm_cell = pattern.args[0]
    assert type(kevm_cell) is App
    exit_code_cell = kevm_cell.args[1]
    assert type(exit_code_cell) is App

    exit_code = exit_code_cell.args[0]
    if exit_code == int_dv(0):
        return

    pretty = kore_print(pattern, definition_dir=kdist.get('evm-semantics.llvm'), output=PrintOutput.PRETTY)
    assert pretty == GOLDEN


def _skipped_tests() -> dict[Path, list[str]]:
    slow_tests = read_csv_file(SLOW_TESTS_FILE)
    failing_tests = read_csv_file(FAILING_TESTS_FILE)
    skipped: dict[Path, list[str]] = {}
    for test_file, test in slow_tests + failing_tests:
        test_file = TEST_DIR / test_file
        skipped.setdefault(test_file, []).append(test)
    return skipped


def read_csv_file(csv_file: Path) -> tuple[tuple[Path, str], ...]:
    with csv_file.open(newline='') as file:
        reader = csv.reader(file)
        return tuple((Path(row[0]), row[1]) for row in reader)


SKIPPED_TESTS: Final = _skipped_tests()

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
