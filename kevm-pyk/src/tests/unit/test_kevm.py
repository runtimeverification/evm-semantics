from __future__ import annotations

from typing import TYPE_CHECKING

import pytest

if TYPE_CHECKING:
    from typing import Final
    from pyk.kast.inner import KInner

from pyk.kast.inner import KApply, KToken

from kevm_pyk.kevm import KEVM

TEST_DATA: Final = [
    ('single-ktoken', KToken('0', 'Int'), KToken('0x0', 'Int')),
    ('bytes-to-hex-empty', KApply('<k>', [KToken('b""', 'Bytes')]), KApply('<k>', KToken('0x', 'Bytes'))),
    (
        'bytes-to-hex-nonempty',
        KApply('<k>', [KToken('b"\\xa6\\xb9c\\x9d"', 'Bytes')]),
        KApply('<k>', KToken('0xa6b9639d', 'Bytes')),
    ),
    (
        'kast-to-hex',
        KApply(
            '<generatedTop>',
            KApply('<coinbase>', KToken('728815563385977040452943777879061427756277306518', 'Int')),
            KApply('<pc>', KToken('100', 'Int')),
            KApply('<output>', KToken('b"\x00\x00\x00\x3c\x60\xf5"', 'Bytes')),
            KApply('<program>', KToken('b"\xcc\xff\xff\xfac\x60\xf5"', 'Bytes')),
        ),
        KApply(
            '<generatedTop>',
            KApply('<coinbase>', KToken('0x7fa9385be102ac3eac297483dd6233d62b3e1496', 'Int')),
            KApply('<pc>', KToken('0x64', 'Int')),
            KApply('<output>', KToken('0x0000003c60f5', 'Bytes')),
            KApply('<program>', KToken('0xccfffffa6360f5', 'Bytes')),
        ),
    ),
]


@pytest.mark.parametrize(
    'test_id,input,result',
    TEST_DATA,
    ids=[test_id for test_id, *_ in TEST_DATA],
)
def test_kinner_to_hex(test_id: str, input: KInner, result: KInner) -> None:
    # When
    to_hex = KEVM.kinner_to_hex(input)
    # Then
    assert to_hex == result
