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

TEST_DIR: Final = REPO_ROOT / 'tests/ethereum-tests'
GOLDEN: Final = (REPO_ROOT / 'tests/templates/output-success-llvm.json').read_text().rstrip()
TEST_FILES_WITH_CID_0: Final = (REPO_ROOT / 'tests/bchain.0.chainId').read_text().splitlines()
FAILING_TESTS_FILE: Final = REPO_ROOT / 'tests/failing.llvm'
SLOW_TESTS_FILE: Final = REPO_ROOT / 'tests/slow.llvm'


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


SKIPPED_TESTS: Final = _skipped_tests(TEST_DIR, SLOW_TESTS_FILE, FAILING_TESTS_FILE)

VM_TEST_DIR: Final = TEST_DIR / 'BlockchainTests/GeneralStateTests/VMTests'
VM_TESTS: Final = tuple(VM_TEST_DIR.glob('*/*.json'))
SKIPPED_VM_TESTS: Final = tuple(test_file for test_file in VM_TESTS if test_file in SKIPPED_TESTS)


@pytest.mark.parametrize(
    'test_file',
    VM_TESTS,
    ids=[str(test_file.relative_to(VM_TEST_DIR)) for test_file in VM_TESTS],
)
def test_vm(test_file: Path, save_failing: bool) -> None:
    _test(test_file, schedule='DEFAULT', mode='VMTESTS', usegas=True, save_failing=save_failing)


@pytest.mark.skip(reason='failing / slow VM tests')
@pytest.mark.parametrize(
    'test_file',
    SKIPPED_VM_TESTS,
    ids=[str(test_file.relative_to(VM_TEST_DIR)) for test_file in SKIPPED_VM_TESTS],
)
def test_rest_vm(test_file: Path, save_failing: bool) -> None:
    _test(test_file, schedule='DEFAULT', mode='VMTESTS', usegas=True, save_failing=save_failing)


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
    _test(test_file, schedule='CANCUN', mode='NORMAL', usegas=True, save_failing=save_failing)


@pytest.mark.skip(reason='failing / slow blockchain tests')
@pytest.mark.parametrize(
    'test_file',
    SKIPPED_BCHAIN_TESTS,
    ids=[str(test_file.relative_to(ALL_TEST_DIR)) for test_file in SKIPPED_BCHAIN_TESTS],
)
def test_rest_bchain(test_file: Path, save_failing: bool) -> None:
    _test(test_file, schedule='CANCUN', mode='NORMAL', usegas=True, save_failing=save_failing)
