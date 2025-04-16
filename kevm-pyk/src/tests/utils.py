from __future__ import annotations

import csv
import logging
from pathlib import Path
from typing import TYPE_CHECKING

from pyk.kdist import kdist
from pyk.kore.prelude import int_dv
from pyk.kore.syntax import App
from pyk.kore.tools import PrintOutput, kore_print

if TYPE_CHECKING:
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
    slow_tests = read_csv_file(slow_tests_file)
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
