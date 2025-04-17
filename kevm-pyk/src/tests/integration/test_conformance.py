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

TEST_DIR: Final = REPO_ROOT / 'tests/ethereum-tests'
GOLDEN: Final = (REPO_ROOT / 'tests/templates/output-success-llvm.json').read_text().rstrip()
TEST_FILES_WITH_CID_0: Final = (REPO_ROOT / 'tests/bchain.0.chainId').read_text().splitlines()
FAILING_TESTS_FILE: Final = REPO_ROOT / 'tests/failing.llvm'
SLOW_TESTS_FILE: Final = REPO_ROOT / 'tests/slow.llvm'


SKIPPED_TESTS: Final = _skipped_tests(TEST_DIR, SLOW_TESTS_FILE, FAILING_TESTS_FILE)


def compute_chain_id(gst_file: str) -> int:
    return 0 if gst_file in TEST_FILES_WITH_CID_0 else 1


VM_TEST_DIR: Final = TEST_DIR / 'BlockchainTests/GeneralStateTests/VMTests'
VM_TESTS: Final = tuple(VM_TEST_DIR.glob('*/*.json'))
SKIPPED_VM_TESTS: Final = tuple(test_file for test_file in VM_TESTS if test_file in SKIPPED_TESTS)


@pytest.mark.parametrize(
    'test_file',
    VM_TESTS,
    ids=[str(test_file.relative_to(VM_TEST_DIR)) for test_file in VM_TESTS],
)
def test_vm(test_file: Path, save_failing: bool) -> None:
    _test(
        test_file,
        schedule='DEFAULT',
        mode='VMTESTS',
        usegas=True,
        save_failing=save_failing,
        compute_chain_id=compute_chain_id,
        skipped_tests=SKIPPED_TESTS,
        test_dir=TEST_DIR,
        failing_tests_file=FAILING_TESTS_FILE,
    )


@pytest.mark.skip(reason='failing / slow VM tests')
@pytest.mark.parametrize(
    'test_file',
    SKIPPED_VM_TESTS,
    ids=[str(test_file.relative_to(VM_TEST_DIR)) for test_file in SKIPPED_VM_TESTS],
)
def test_rest_vm(test_file: Path, save_failing: bool) -> None:
    _test(
        test_file,
        schedule='DEFAULT',
        mode='VMTESTS',
        usegas=True,
        save_failing=save_failing,
        compute_chain_id=compute_chain_id,
        skipped_tests=SKIPPED_TESTS,
        test_dir=TEST_DIR,
        failing_tests_file=FAILING_TESTS_FILE,
    )


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
    _test(
        test_file,
        schedule='CANCUN',
        mode='NORMAL',
        usegas=True,
        save_failing=save_failing,
        compute_chain_id=compute_chain_id,
        skipped_tests=SKIPPED_TESTS,
        test_dir=TEST_DIR,
        failing_tests_file=FAILING_TESTS_FILE,
    )


@pytest.mark.skip(reason='failing / slow blockchain tests')
@pytest.mark.parametrize(
    'test_file',
    SKIPPED_BCHAIN_TESTS,
    ids=[str(test_file.relative_to(ALL_TEST_DIR)) for test_file in SKIPPED_BCHAIN_TESTS],
)
def test_rest_bchain(test_file: Path, save_failing: bool) -> None:
    _test(
        test_file,
        schedule='CANCUN',
        mode='NORMAL',
        usegas=True,
        save_failing=save_failing,
        compute_chain_id=compute_chain_id,
        skipped_tests=SKIPPED_TESTS,
        test_dir=TEST_DIR,
        failing_tests_file=FAILING_TESTS_FILE,
    )
