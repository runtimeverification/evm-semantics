from __future__ import annotations

import csv
import json
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
    from collections.abc import Callable
    from typing import Any, Final

    from pyk.kore.syntax import Pattern

sys.setrecursionlimit(10**8)

TEST_DIR: Final = REPO_ROOT / 'tests/ethereum-tests'
GOLDEN: Final = (REPO_ROOT / 'tests/templates/output-success-llvm.json').read_text().rstrip()


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


def _skipped_tests() -> set[tuple[Path, str]]:
    slow_tests = read_csv_file(REPO_ROOT / 'tests/slow.llvm')
    failing_tests = read_csv_file(REPO_ROOT / 'tests/failing.llvm')
    return set(slow_tests + failing_tests)


def read_csv_file(csv_file: Path) -> tuple[tuple[Path, str], ...]:
    with csv_file.open(newline='') as file:
        reader = csv.reader(file)
        return tuple((Path(row[0]), row[1]) for row in reader)


SKIPPED_TESTS: Final = _skipped_tests()

VM_TEST_DIR: Final = TEST_DIR / 'BlockchainTests/GeneralStateTests/VMTests'
ALL_VM_TESTS_CSV: Final = REPO_ROOT / 'tests/all_vm_tests.csv'
VM_TEST_FILES: Final = tuple(VM_TEST_DIR.glob('*/*.json'))
ALL_VM_TESTS: Final = read_csv_file(ALL_VM_TESTS_CSV)
VM_TESTS: Final = tuple(test for test in ALL_VM_TESTS if test not in SKIPPED_TESTS)
REST_VM_TESTS: Final = tuple(test for test in ALL_VM_TESTS if test in SKIPPED_TESTS)
assert len(ALL_VM_TESTS) == len(VM_TESTS) + len(REST_VM_TESTS)


@pytest.mark.parametrize(
    'test_file, test_id',
    VM_TESTS,
    ids=[f'{test_file}:{test_id}' for test_file, test_id in VM_TESTS],
)
def test_vm(get_gst_data: Callable[[Path, str], dict[str, Any]], test_file: Path, test_id: str) -> None:
    # Given
    gst_file = TEST_DIR / test_file
    gst_input = get_gst_data(gst_file, test_id)

    # When
    res = interpret(gst_input, 'DEFAULT', 'VMTESTS', 1, True, check=False)

    # Then
    _assert_exit_code_zero(res)


@pytest.mark.skip(reason='failing / slow VM tests')
@pytest.mark.parametrize(
    'test_file, test_id',
    REST_VM_TESTS,
    ids=[f'{test_file}:{test_id}' for test_file, test_id in REST_VM_TESTS],
)
def test_rest_vm(get_gst_data: Callable[[Path, str], dict[str, Any]], test_file: Path, test_id: str) -> None:
    # Given
    gst_file = TEST_DIR / test_file
    gst_input = get_gst_data(gst_file, test_id)

    # When
    res = interpret(gst_input, 'DEFAULT', 'VMTESTS', 1, True, check=False)

    # Then
    _assert_exit_code_zero(res)


EXCLUDED_TESTS = SKIPPED_TESTS.union(ALL_VM_TESTS)

BCHAIN_TEST_DIR: Final = TEST_DIR / 'BlockchainTests/GeneralStateTests'
ALL_BCHAIN_TESTS_CSV: Final = REPO_ROOT / 'tests/all_bchain_tests.csv'
BCHAIN_TEST_FILES: Final = tuple(BCHAIN_TEST_DIR.glob('**/*.json'))
ALL_BCHAIN_TESTS: Final = read_csv_file(ALL_BCHAIN_TESTS_CSV)
BCHAIN_TESTS: Final = tuple(test for test in ALL_BCHAIN_TESTS if test not in EXCLUDED_TESTS)
REST_BCHAIN_TESTS: Final = tuple(test for test in ALL_BCHAIN_TESTS if test in EXCLUDED_TESTS)
assert len(ALL_BCHAIN_TESTS) == len(BCHAIN_TESTS) + len(REST_BCHAIN_TESTS)


@pytest.fixture(scope='session')
def gst_data() -> dict[Path, dict[str, Any]]:
    return {file: json.loads(file.read_text()) for file in BCHAIN_TEST_FILES + VM_TEST_FILES}


@pytest.fixture(scope='session')
def get_gst_data(gst_data: dict[Path, dict[str, Any]]) -> Callable[[Path, str], dict[str, Any]]:
    def _get_gst_data(test_file: Path, test_id: str) -> dict[str, Any]:
        return {test_id: gst_data[test_file][test_id]}

    return _get_gst_data


@pytest.mark.parametrize(
    'test_file, test_id',
    BCHAIN_TESTS,
    ids=[f'{test_file}:{test_id}' for test_file, test_id in BCHAIN_TESTS],
)
def test_bchain(get_gst_data: Callable[[Path, str], dict[str, Any]], test_file: Path, test_id: str) -> None:
    # Given
    gst_file = TEST_DIR / test_file
    gst_input = get_gst_data(gst_file, test_id)

    # When
    res = interpret(gst_input, 'SHANGHAI', 'NORMAL', 1, True, check=False)

    # Then
    _assert_exit_code_zero(res)


@pytest.mark.skip(reason='failing / slow blockchain tests')
@pytest.mark.parametrize(
    'test_file, test_id',
    REST_BCHAIN_TESTS,
    ids=[f'{test_file}:{test_id}' for test_file, test_id in REST_BCHAIN_TESTS],
)
def test_rest_bchain(get_gst_data: Callable[[Path, str], dict[str, Any]], test_file: Path, test_id: str) -> None:
    # Given
    gst_file = TEST_DIR / test_file
    gst_input = get_gst_data(gst_file, test_id)

    # When
    res = interpret(gst_input, 'SHANGHAI', 'NORMAL', 1, True, check=False)

    # Then
    _assert_exit_code_zero(res)


def test_csv_files(gst_data: dict[Path, dict[str, Any]], update_expected_output: bool) -> None:
    all_bchain_tests = [
        (file.relative_to(TEST_DIR), test_id) for file in BCHAIN_TEST_FILES for test_id in gst_data[file].keys()
    ]
    assert_or_update_csv_file(all_bchain_tests, ALL_BCHAIN_TESTS_CSV, update_expected_output)
    all_vm_tests = [(file.relative_to(TEST_DIR), test_id) for file in VM_TEST_FILES for test_id in gst_data[file]]
    assert_or_update_csv_file(all_vm_tests, ALL_VM_TESTS_CSV, update_expected_output)


def assert_or_update_csv_file(content: list[tuple[Path, str]], expected_file: Path, update: bool) -> None:
    def _write_csv(target: Path, content: tuple[tuple[Path, str], ...]) -> None:
        with open(target, 'w', newline='') as csvfile:
            writer = csv.writer(csvfile)
            writer.writerows(content)

    actual = tuple(sorted(content))
    if update:
        _write_csv(expected_file, actual)
    else:
        assert expected_file.is_file()
        expected_text = read_csv_file(expected_file)
        assert actual == expected_text
