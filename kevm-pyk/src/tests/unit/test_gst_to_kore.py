import json

from pyk.kore.parser import KoreParser

from kevm_pyk.gst_to_kore import gst_to_kore

from ..utils import REPO_ROOT


def test_gst_to_kore() -> None:
    # Given
    gst_file = REPO_ROOT / 'tests/ethereum-tests/GeneralStateTests/VMTests/vmLogTest/log3.json'
    gst_data = json.loads(gst_file.read_text())

    expected_file = REPO_ROOT / 'tests/interactive/vmLogTest/log3.gst-to-kore.expected'
    expected = KoreParser(expected_file.read_text()).pattern()

    # When
    actual = gst_to_kore(gst_data, 'MERGE', 'NORMAL', 1)

    # Then
    assert actual == expected
