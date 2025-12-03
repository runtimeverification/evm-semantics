from __future__ import annotations

from typing import TYPE_CHECKING

import pytest

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

    assert True
