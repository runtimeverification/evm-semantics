from __future__ import annotations

import json
from typing import TYPE_CHECKING

import pytest
from pyk.kdist import kdist
from pyk.kore.tools import PrintOutput, kore_print

from kevm_pyk.interpreter import interpret

from ..utils import REPO_ROOT

if TYPE_CHECKING:
    from pathlib import Path
    from typing import Final


FAILING_DIR: Final = REPO_ROOT / 'tests/failing'
TEST_DATA: Final = tuple(FAILING_DIR.glob('*.json'))
assert TEST_DATA


@pytest.mark.parametrize('gst_file', TEST_DATA, ids=[str(gst_file.relative_to(FAILING_DIR)) for gst_file in TEST_DATA])
def test_run(gst_file: Path, update_expected_output: bool) -> None:
    # Given
    expected_file = gst_file.with_suffix('.json.expected')
    expected = expected_file.read_text()

    with gst_file.open() as f:
        gst_data = json.load(f)

    # When
    pattern = interpret(gst_data, 'PRAGUE', 'NORMAL', 1, True, check=False)
    actual = kore_print(pattern, definition_dir=kdist.get('evm-semantics.llvm'), output=PrintOutput.PRETTY)

    # Then

    if update_expected_output:
        expected_file.write_text(actual)
        return

    assert actual == expected
