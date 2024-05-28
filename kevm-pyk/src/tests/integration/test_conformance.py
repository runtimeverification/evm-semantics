from __future__ import annotations

import json
import logging
import sys
from typing import TYPE_CHECKING

import pytest
from pyk.kdist import kdist
from pyk.kore.prelude import int_dv
from pyk.kore.syntax import App
from pyk.kore.tools import PrintOutput, kore_print

from kevm_pyk.interpreter import interpret

from ..utils import REPO_ROOT

if TYPE_CHECKING:
    from pathlib import Path
    from typing import Final

    from pyk.kore.syntax import Pattern


_LOGGER: Final = logging.getLogger(__name__)
_LOG_FORMAT: Final = '%(levelname)s %(asctime)s %(name)s - %(message)s'


sys.setrecursionlimit(10**8)

TEST_DIR: Final = REPO_ROOT / 'tests/ethereum-tests'
GOLDEN: Final = (REPO_ROOT / 'tests/templates/output-success-llvm.json').read_text().rstrip()


def _test(gst_file: Path, schedule: str, mode: str, chainid: int, usegas: bool) -> None:
    with gst_file.open() as f:
        gst_data = json.load(f)

    for test_name, test in gst_data.items():
        # TODO: check if has post-state block
        _LOGGER.info(f'Running test: {gst_file} - {test_name}')
        res = interpret(test_name, test, schedule, mode, chainid, usegas, check=False)
        _assert_exit_code_zero(res)


def _assert_exit_code_zero(pattern: Pattern) -> None:
    assert type(pattern) is App
    kevm_cell = pattern.args[0]
    assert type(kevm_cell) is App
    exit_code_cell = kevm_cell.args[1]
    assert type(exit_code_cell) is App

    exit_code = exit_code_cell.args[0]
    if exit_code == int_dv(0):
        return

    _LOGGER.warning(f'pattern: {pattern.text}')
    pretty = kore_print(pattern, definition_dir=kdist.get('evm-semantics.llvm'), output=PrintOutput.PRETTY)
    assert pretty == GOLDEN


def _skipped_tests() -> set[Path]:
    def read_test_list(path: Path) -> list[Path]:
        return [REPO_ROOT / test_path for test_path in path.read_text().splitlines()]

    slow_tests = read_test_list(REPO_ROOT / 'tests/slow.llvm')
    failing_tests = read_test_list(REPO_ROOT / 'tests/failing.llvm')
    return set(slow_tests + failing_tests)


SKIPPED_TESTS: Final = _skipped_tests()

VM_TEST_DIR: Final = TEST_DIR / 'BlockchainTests/GeneralStateTests/VMTests'
ALL_VM_TESTS: Final = tuple(VM_TEST_DIR.glob('*/*.json'))
VM_TESTS: Final = tuple(test_file for test_file in ALL_VM_TESTS if test_file not in SKIPPED_TESTS)
REST_VM_TESTS: Final = tuple(test_file for test_file in ALL_VM_TESTS if test_file in SKIPPED_TESTS)


@pytest.mark.parametrize(
    'test_file',
    VM_TESTS,
    ids=[str(test_file.relative_to(VM_TEST_DIR)) for test_file in VM_TESTS],
)
def test_vm(test_file: Path) -> None:
    _test(test_file, 'DEFAULT', 'VMTESTS', 1, True)


@pytest.mark.skip(reason='failing / slow VM tests')
@pytest.mark.parametrize(
    'test_file',
    REST_VM_TESTS,
    ids=[str(test_file.relative_to(VM_TEST_DIR)) for test_file in REST_VM_TESTS],
)
def test_rest_vm(test_file: Path) -> None:
    _test(test_file, 'DEFAULT', 'VMTESTS', 1, True)


BCHAIN_TEST_DIR: Final = TEST_DIR / 'BlockchainTests/GeneralStateTests'
ALL_BCHAIN_TESTS: Final = tuple(BCHAIN_TEST_DIR.glob('**/*.json'))
BCHAIN_TESTS: Final = tuple(
    test_file for test_file in ALL_BCHAIN_TESTS if test_file not in (list(SKIPPED_TESTS) + list(ALL_VM_TESTS))
)
REST_BCHAIN_TESTS: Final = tuple(
    test_file for test_file in ALL_BCHAIN_TESTS if test_file in SKIPPED_TESTS and test_file not in ALL_VM_TESTS
)


@pytest.mark.parametrize(
    'test_file',
    BCHAIN_TESTS,
    ids=[str(test_file.relative_to(TEST_DIR)) for test_file in BCHAIN_TESTS],
)
def test_bchain(test_file: Path) -> None:
    _test(test_file, 'SHANGHAI', 'NORMAL', 1, True)


@pytest.mark.skip(reason='failing / slow blockchain tests')
@pytest.mark.parametrize(
    'test_file',
    REST_BCHAIN_TESTS,
    ids=[str(test_file.relative_to(TEST_DIR)) for test_file in REST_BCHAIN_TESTS],
)
def test_rest_bchain(test_file: Path) -> None:
    _test(test_file, 'SHANGHAI', 'NORMAL', 1, True)
