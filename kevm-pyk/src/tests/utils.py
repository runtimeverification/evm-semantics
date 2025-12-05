from __future__ import annotations

import csv
import json
import logging
from pathlib import Path
from typing import TYPE_CHECKING

import pytest
from pyk.kdist import kdist
from pyk.kore.prelude import int_dv
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

    gst_file_relative_path: Final[str] = str(gst_file.relative_to(test_dir))

    with gst_file.open() as f:
        gst_data = json.load(f)

    # Filter upfront instead of checking each iteration
    tests_to_run = {k: v for k, v in gst_data.items() if k not in skipped_gst_tests}
    failing_tests: list[str] = []

    chain_id = compute_chain_id(str(gst_file.relative_to(test_dir)))

    for test_name, test in tests_to_run.items():
        _LOGGER.info(f'Running test: {gst_file} - {test_name}')

        res = interpret({test_name: test}, schedule, mode, chain_id, usegas, check=False)

        try:
            _assert_exit_code_zero(res)
        except AssertionError:
            if not save_failing:
                raise
            failing_tests.append(test_name)

    if len(failing_tests) == 0:
        return

    with failing_tests_file.open('a', newline='') as ff:
        writer = csv.writer(ff)
        if len(failing_tests) == len(gst_data):
            writer.writerow([gst_file_relative_path, '*'])
        else:
            for test_name in sorted(failing_tests):
                writer.writerow([gst_file_relative_path, test_name])
    raise AssertionError(f'Found failing tests in GST file {gst_file_relative_path}: {failing_tests}')
