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

TEST_DIR: Final = REPO_ROOT / 'tests/ethereum-tests'
GOLDEN: Final = (REPO_ROOT / 'tests/templates/output-success-llvm.json').read_text().rstrip()
TEST_FILES_WITH_CID_0: Final = (REPO_ROOT / 'tests/bchain.0.chainId').read_text().splitlines()
FAILING_TESTS_FILE: Final = REPO_ROOT / 'tests/failing.llvm'
SLOW_TESTS_FILE: Final = REPO_ROOT / 'tests/slow.llvm'


def _test(gst_file: Path, schedule: str, mode: str, usegas: bool, save_failing: bool = False) -> None:
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
            failing_tests.append(test_name)
            if not save_failing:
                raise AssertionError

    if failing_tests:
        if save_failing:
            with FAILING_TESTS_FILE.open('a') as ff:
                if len(failing_tests) == len(gst_data):
                    ff.write(f'{gst_file_relative_path},*\n')
                else:
                    for test_name in failing_tests:
                        ff.write(f'{gst_file_relative_path},{test_name}\n')
        raise AssertionError()


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

VM_TEST_DIR: Final = TEST_DIR / 'BlockchainTests/GeneralStateTests/VMTests'
VM_TESTS: Final = tuple(VM_TEST_DIR.glob('*/*.json'))
SKIPPED_VM_TESTS: Final = tuple(test_file for test_file in VM_TESTS if test_file in SKIPPED_TESTS)


@pytest.mark.parametrize(
    'test_file',
    VM_TESTS,
    ids=[str(test_file.relative_to(VM_TEST_DIR)) for test_file in VM_TESTS],
)
def test_vm(test_file: Path, save_failing: bool) -> None:
    _test(test_file, 'DEFAULT', 'VMTESTS', True, save_failing)


@pytest.mark.skip(reason='failing / slow VM tests')
@pytest.mark.parametrize(
    'test_file',
    SKIPPED_VM_TESTS,
    ids=[str(test_file.relative_to(VM_TEST_DIR)) for test_file in SKIPPED_VM_TESTS],
)
def test_rest_vm(test_file: Path, save_failing: bool) -> None:
    _test(test_file, 'DEFAULT', 'VMTESTS', True, save_failing)


ALL_TEST_DIR: Final = TEST_DIR / 'BlockchainTests/GeneralStateTests'
ALL_TESTS: Final = tuple(ALL_TEST_DIR.glob('**/*.json'))
BCHAIN_TESTS: Final = tuple(test_file for test_file in ALL_TESTS if test_file not in set(VM_TESTS))
SKIPPED_BCHAIN_TESTS: Final = tuple(test_file for test_file in BCHAIN_TESTS if test_file in SKIPPED_TESTS)


@pytest.mark.parametrize(
    'test_file',
    BCHAIN_TESTS,
    ids=[str(test_file.relative_to(ALL_TEST_DIR)) for test_file in BCHAIN_TESTS],
)
def test_bchain(test_file: Path, save_failing: bool) -> None:
    _test(test_file, 'CANCUN', 'NORMAL', True, save_failing)


@pytest.mark.skip(reason='failing / slow blockchain tests')
@pytest.mark.parametrize(
    'test_file',
    SKIPPED_BCHAIN_TESTS,
    ids=[str(test_file.relative_to(ALL_TEST_DIR)) for test_file in SKIPPED_BCHAIN_TESTS],
)
def test_rest_bchain(test_file: Path, save_failing: bool) -> None:
    _test(test_file, 'CANCUN', 'NORMAL', True, save_failing)
