from __future__ import annotations

import csv
import json
import logging
from pathlib import Path
from typing import TYPE_CHECKING
import sys
import pytest
from pyk.kdist._kdist import kdist
from pyk.kore.prelude import int_dv
from pyk.kore.syntax import App, SortApp
from pyk.kore.tools import PrintOutput, kore_print

from kevm_pyk.interpreter import interpret

if TYPE_CHECKING:
    from collections.abc import Callable
    from typing import Final

    from pyk.kore.syntax import Pattern


_LOGGER: Final = logging.getLogger(__name__)


REPO_ROOT: Final = Path(__file__).parents[3].resolve(strict=True)
GOLDEN: Final = (REPO_ROOT / 'tests/templates/output-success-llvm.json').read_text().rstrip()
sys.setrecursionlimit(15000000)


def _assert_exit_code_zero(pattern: Pattern, exception_expected: bool = False) -> None:
    assert type(pattern) is App
    kevm_cell = pattern.args[0]
    assert type(kevm_cell) is App
    exit_code_cell = kevm_cell.args[1]
    assert type(exit_code_cell) is App
    print(exception_expected)

    exit_code = exit_code_cell.args[0]
    if exit_code == int_dv(0):
        return
    elif exception_expected:
        status_code_sort = _fetch_status_code_cell(kevm_cell).args[0]
        assert type(status_code_sort) is App
        if status_code_sort.sorts[0] == SortApp('SortExceptionalStatusCode'):
            return

    pretty = kore_print(pattern, definition_dir=kdist.get('evm-semantics.llvm'), output=PrintOutput.PRETTY)
    assert pretty == GOLDEN


def _fetch_status_code_cell(kevm_cell: App) -> App:
    # <statusCode> is nested under <kevm><ethereum><evm>
    ethereum_cell = kevm_cell.args[5]
    assert type(ethereum_cell) is App
    evm_cell = ethereum_cell.args[0]
    assert type(evm_cell) is App
    status_code_cell = evm_cell.args[1]
    assert type(status_code_cell) is App
    return status_code_cell


def _skipped_tests(test_dir: Path, slow_tests_file: Path, failing_tests_file: Path) -> dict[Path, list[str]]:
    try:
        slow_tests = read_csv_file(slow_tests_file)
    except FileNotFoundError as e:
        _LOGGER.warning(e)
        slow_tests = ()
    failing_tests = read_csv_file(failing_tests_file)
    skipped: dict[Path, list[str]] = {}
    for test_file, test in slow_tests + failing_tests:
        test_file = test_dir / test_file
        skipped.setdefault(test_file, []).append(test)
    return skipped


def read_csv_file(csv_file: Path) -> tuple[tuple[Path, str], ...]:
    with csv_file.open(newline='') as file:
        reader = csv.reader(file)
        return tuple((Path(row[0]), row[1]) for row in reader)


def has_exception(test_data: dict) -> tuple[bool, bool]:
    exception_expected = False
    has_big_int = False
    for block in test_data.get('blocks', []):
        exception_expected = exception_expected or 'expectException' in block
        has_big_int = has_big_int or 'hasBigInt' in block
        if exception_expected and has_big_int:
            break
    return (exception_expected, has_big_int)


def _test(
    gst_file: Path,
    *,
    schedule: str,
    mode: str,
    usegas: bool,
    save_failing: bool,
    compute_chain_id: Callable[[str], int],
    skipped_tests: dict[Path, list[str]],
    test_dir: Path,
    failing_tests_file: Path,
) -> None:
    skipped_gst_tests = skipped_tests.get(gst_file, [])
    if '*' in skipped_gst_tests:
        pytest.skip()

    failing_tests: list[str] = []
    gst_file_relative_path: Final[str] = str(gst_file.relative_to(test_dir))

    chain_id = compute_chain_id(gst_file_relative_path)

    with gst_file.open() as f:
        gst_data = json.load(f)

    for test_name, test in gst_data.items():
        if test_name in skipped_gst_tests:
            continue

        _LOGGER.info(f'Running test: {gst_file} - {test_name}')

        (exception_expected, has_big_int) = has_exception(test)
        try:
            res = interpret({test_name: test}, schedule, mode, chain_id, usegas, check=False)
        except RuntimeError:
            if has_big_int:
                continue
            else:
                failing_tests.append(test_name)
                raise
        try:
            _assert_exit_code_zero(res, exception_expected)
        except AssertionError:
            if not save_failing:
                raise
            failing_tests.append(test_name)

    if not failing_tests:
        return
    if save_failing:
        with failing_tests_file.open('a', newline='') as ff:
            writer = csv.writer(ff)
            if len(failing_tests) == len(gst_data):
                writer.writerow([gst_file_relative_path, '*'])
            else:
                for test_name in sorted(failing_tests):
                    writer.writerow([gst_file_relative_path, test_name])
    raise AssertionError(f'Found failing tests in GST file {gst_file_relative_path}: {failing_tests}')
