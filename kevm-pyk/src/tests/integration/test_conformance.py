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


def _test(gst_file: Path, test_name: str, schedule: str, mode: str, chainid: int, usegas: bool) -> None:
    with gst_file.open() as f:
        gst_data = json.load(f)

        _LOGGER.info(f'Running test: {gst_file} - {test_name}')
        res = interpret({test_name: gst_data.get(test_name)}, schedule, mode, chainid, usegas, check=False)
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

    pretty = kore_print(pattern, definition_dir=kdist.get('evm-semantics.llvm'), output=PrintOutput.PRETTY)
    assert pretty == GOLDEN


def read_test_list(path: Path) -> list[tuple[Path, str]]:
    return [(REPO_ROOT / line.split(':')[0], line.split(':')[1]) for line in path.read_text().splitlines()]


def read_gst_file(gst_file: Path) -> list[str]:
    with gst_file.open() as f:
        gst_data = json.load(f)
    return gst_data.keys()


def _skipped_tests() -> set[tuple[Path, str]]:
    slow_tests = read_test_list(REPO_ROOT / 'tests/slow.llvm')
    failing_tests = read_test_list(REPO_ROOT / 'tests/failing.llvm')
    return set(slow_tests + failing_tests)


SKIPPED_TESTS: Final = _skipped_tests()

VM_TEST_DIR: Final = TEST_DIR / 'BlockchainTests/GeneralStateTests/VMTests'
ALL_VM_TESTS: Final = tuple((file, test_id) for file in VM_TEST_DIR.glob('*/*.json') for test_id in read_gst_file(file))
VM_TESTS: Final = tuple(test_tuple for test_tuple in ALL_VM_TESTS if test_tuple not in SKIPPED_TESTS)
REST_VM_TESTS: Final = tuple(test_tuple for test_tuple in ALL_VM_TESTS if test_tuple in SKIPPED_TESTS)


@pytest.mark.parametrize(
    'test_file, test_id',
    VM_TESTS,
    ids=[f'{test_file.relative_to(VM_TEST_DIR)}: {test_id}' for test_file, test_id in VM_TESTS],
)
def test_vm(test_file: Path, test_id: str) -> None:
    _test(test_file, test_id, 'DEFAULT', 'VMTESTS', 1, True)


@pytest.mark.skip(reason='failing / slow VM tests')
@pytest.mark.parametrize(
    'test_file, test_id',
    REST_VM_TESTS,
    ids=[f'{test_file.relative_to(VM_TEST_DIR)}: {test_id}' for test_file, test_id in REST_VM_TESTS],
)
def test_rest_vm(test_file: Path, test_id: str) -> None:
    _test(test_file, test_id, 'DEFAULT', 'VMTESTS', 1, True)


BCHAIN_TEST_DIR: Final = TEST_DIR / 'BlockchainTests/GeneralStateTests'
ALL_BCHAIN_TESTS: Final = tuple(
    (file, test_id) for file in BCHAIN_TEST_DIR.glob('**/*.json') for test_id in read_gst_file(file)
)
BCHAIN_TESTS: Final = tuple(
    test_tuple for test_tuple in ALL_BCHAIN_TESTS if test_tuple not in (list(SKIPPED_TESTS) + list(ALL_VM_TESTS))
)
REST_BCHAIN_TESTS: Final = tuple(
    test_tuple for test_tuple in ALL_BCHAIN_TESTS if test_tuple in SKIPPED_TESTS and test_tuple not in ALL_VM_TESTS
)


@pytest.mark.parametrize(
    'test_file, test_id',
    BCHAIN_TESTS,
    ids=[f'{test_file.relative_to(TEST_DIR)}: {test_id}' for test_file, test_id in BCHAIN_TESTS],
)
def test_bchain(test_file: Path, test_id: str) -> None:
    _test(test_file, test_id, 'SHANGHAI', 'NORMAL', 1, True)


@pytest.mark.skip(reason='failing / slow blockchain tests')
@pytest.mark.parametrize(
    'test_file, test_id',
    REST_BCHAIN_TESTS,
    ids=[f'{test_file.relative_to(TEST_DIR)}: {test_id}' for test_file, test_id in REST_BCHAIN_TESTS],
)
def test_rest_bchain(test_file: Path, test_id: str) -> None:
    _test(test_file, test_id, 'SHANGHAI', 'NORMAL', 1, True)
