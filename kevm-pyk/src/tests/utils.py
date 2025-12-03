from __future__ import annotations

import csv
import json
import logging
from pathlib import Path
from typing import TYPE_CHECKING

import pytest
from pyk.kdist import kdist
from pyk.kore.prelude import int_dv, SortApp
from pyk.kore.syntax import App
from pyk.kore.tools import PrintOutput, kore_print

from kevm_pyk.interpreter import interpret

if TYPE_CHECKING:
    from collections.abc import Callable
    from typing import Final

    from pyk.kore.syntax import Pattern


_LOGGER: Final = logging.getLogger(__name__)


REPO_ROOT: Final = Path(__file__).parents[3].resolve(strict=True)
GOLDEN: Final = (REPO_ROOT / 'tests/templates/output-success-llvm.json').read_text().rstrip()


def _assert_exit_code_zero(pattern: Pattern, expectedException: str | None = None) -> None:
    assert type(pattern) is App
    kevm_cell = pattern.args[0]
    assert type(kevm_cell) is App
    exit_code_cell = kevm_cell.args[1]
    assert type(exit_code_cell) is App
    status_code_cell = kevm_cell.args[5].args[0].args[1] #source: trust me bro
    assert type(status_code_cell) is App
    status_code_sort = status_code_cell.args[0]
    # print (status_code_sort)
    exit_code = exit_code_cell.args[0]
    # print(expectedException, status_code_sort.sorts[0], status_code_sort.sorts[0] == SortApp('SortExceptionalStatusCode') )
    if exit_code == int_dv(0):
        return
    elif expectedException and status_code_sort.sorts[0] == SortApp('SortExceptionalStatusCode'):
        return
    pretty = kore_print(pattern, definition_dir=kdist.get('evm-semantics.llvm'), output=PrintOutput.PRETTY)
    # print(pretty)
    assert pretty == GOLDEN


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

    with gst_file.open() as f:
        gst_data = json.load(f)

    for test_name, test in gst_data.items():
        if test_name in skipped_gst_tests:
            continue
        _LOGGER.info(f'Running test: {gst_file} - {test_name}')
        assert type(test) is dict
        chain_id = compute_chain_id(gst_file_relative_path)
        blocks = test.get('blocks', [])
        expect_exception = False
        has_big_int = False
        for block in blocks:
            expect_exception = expect_exception or block.get('expectException')
            has_big_int = has_big_int or block.get('hasBigInt')
            if expect_exception and has_big_int:
                break

        try:
            res = interpret({test_name: test}, schedule, mode, chain_id, usegas, check=False)
        except RuntimeError:
            if has_big_int:
                continue
            else:
                raise
        try:
            _assert_exit_code_zero(res, expect_exception)
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
