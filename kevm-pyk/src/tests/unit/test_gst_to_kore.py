from __future__ import annotations

import json
from typing import TYPE_CHECKING

import pytest
from pyk.kore.parser import KoreParser

from kevm_pyk.gst_to_kore import gst_to_kore

from ..utils import REPO_ROOT

if TYPE_CHECKING:
    from typing import Final


TEST_DATA: Final = (
    (
        'tests/ethereum-tests/GeneralStateTests/VMTests/vmLogTest/log3.json',
        'tests/interactive/vmLogTest/log3.gst-to-kore.expected',
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
def test_gst_to_kore(gst_path: str, expected_path: str) -> None:
    # Given
    gst_file = REPO_ROOT / gst_path
    gst_data = json.loads(gst_file.read_text())

    expected_file = REPO_ROOT / expected_path
    expected = KoreParser(expected_file.read_text()).pattern()

    # When
    actual = gst_to_kore(gst_data, 'MERGE', 'NORMAL', 1)

    # Then
    assert actual == expected
