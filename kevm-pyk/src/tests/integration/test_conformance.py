from __future__ import annotations

import json
import sys
from pathlib import Path
from typing import TYPE_CHECKING

import pytest
from pyk.kore.prelude import int_dv
from pyk.kore.syntax import App
from pyk.kore.tools import PrintOutput, kore_print

from kevm_pyk.interpreter import interpret
from kevm_pyk.kompile import KompileTarget

if TYPE_CHECKING:
    from typing import Final

    from pyk.kore.syntax import Pattern


sys.setrecursionlimit(10**8)

REPO_ROOT: Final = Path(__file__).parents[4]
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

    pretty = kore_print(pattern, KompileTarget.LLVM.definition_dir, output=PrintOutput.PRETTY)
    assert pretty == GOLDEN


def _skipped_tests() -> set[Path]:
    def read_test_list(path: Path) -> list[Path]:
        return [REPO_ROOT / test_path for test_path in path.read_text().splitlines()]

    slow_tests = read_test_list(REPO_ROOT / 'tests/slow.llvm')
    failing_tests = read_test_list(REPO_ROOT / 'tests/failing.llvm')
    return set(slow_tests + failing_tests)


SKIPPED_TESTS: Final = _skipped_tests()

VM_TEST_DIR: Final = TEST_DIR / 'LegacyTests/Constantinople/VMTests'
VM_TESTS: Final = tuple(VM_TEST_DIR.glob('*/*.json'))


@pytest.mark.parametrize('test_file', VM_TESTS, ids=[str(test_file.relative_to(VM_TEST_DIR)) for test_file in VM_TESTS])
def test_vm(test_file: Path) -> None:
    if test_file in SKIPPED_TESTS:
        pytest.skip()

    # Given
    with test_file.open() as f:
        gst_data = json.load(f)

    # When
    res = interpret(gst_data, 'DEFAULT', 'VMTESTS', 1)

    # Then
    _assert_exit_code_zero(res)


BCHAIN_NEW_TEST_DIR: Final = TEST_DIR / 'BlockchainTests/GeneralStateTests'
BCHAIN_NEW_TESTS: Final = tuple(BCHAIN_NEW_TEST_DIR.glob('*/*.json'))

BCHAIN_LEGACY_TEST_DIR: Final = TEST_DIR / 'LegacyTests/Constantinople/BlockchainTests/GeneralStateTests'
BCHAIN_LEGACY_TESTS: Final = tuple(BCHAIN_LEGACY_TEST_DIR.glob('*/*.json'))

BCHAIN_TESTS: Final = BCHAIN_NEW_TESTS + BCHAIN_LEGACY_TESTS


@pytest.mark.parametrize(
    'test_file', BCHAIN_TESTS, ids=[str(test_file.relative_to(TEST_DIR)) for test_file in BCHAIN_TESTS]
)
def test_bchain(test_file: Path) -> None:
    if test_file in SKIPPED_TESTS:
        pytest.skip()

    # Given
    with test_file.open() as f:
        gst_data = json.load(f)

    # When
    res = interpret(gst_data, 'MERGE', 'NORMAL', 1)

    # Then
    _assert_exit_code_zero(res)
