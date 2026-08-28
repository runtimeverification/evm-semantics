from __future__ import annotations

import json
from typing import TYPE_CHECKING

import pytest
from pyk.kore.parser import KoreParser

from kevm_pyk.interpreter import iterate_gst

from ..utils import REPO_ROOT

if TYPE_CHECKING:
    from typing import Final


TEST_DATA: Final = (
    (
        'tests/interactive/log3.json',
        'tests/interactive/log3.gst-to-kore.expected',
    ),
    (
        'tests/interactive/log3_MaxTopic_d0g0v0.json',
        'tests/interactive/log3_MaxTopic_d0g0v0.json.parse-expected',
    ),
    (
        'tests/interactive/CallRecursiveContract_d0g0v0.json',
        'tests/interactive/CallRecursiveContract_d0g0v0.json.parse-expected',
    ),
)


@pytest.mark.parametrize('gst_path,expected_path', TEST_DATA, ids=[gst_path for gst_path, _ in TEST_DATA])
def test_gst_to_kore(gst_path: str, expected_path: str, update_expected_output: bool) -> None:
    # Given
    gst_file = REPO_ROOT / gst_path
    gst_data = json.loads(gst_file.read_text())
    expected_file = REPO_ROOT / expected_path

    # When
    actuals = [kore for _, kore, _ in iterate_gst(gst_data, 'NORMAL', 1, True)]

    # Then
    if update_expected_output:
        with expected_file.open('w') as f:
            for kore in actuals:
                kore.write(f)
                f.write('\n')
        return

    expected_lines = expected_file.read_text().strip().split('\n')
    assert len(actuals) == len(expected_lines)

    for actual, expected_line in zip(actuals, expected_lines, strict=True):
        expected = KoreParser(expected_line).pattern()
        assert actual == expected
