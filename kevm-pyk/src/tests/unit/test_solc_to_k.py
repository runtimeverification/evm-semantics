from __future__ import annotations

import pytest

from kevm_pyk.utils import name_escaped, name_unescaped

TEST_DATA: list[tuple[str, str, str]] = [
    ('has_underscore', 'My_contract', 'KEVMMy0x5fzcontract'),
]


@pytest.mark.parametrize('test_id,input,output', TEST_DATA, ids=[test_id for test_id, *_ in TEST_DATA])
def test_escaping(test_id: str, input: str, output: str) -> None:
    # When
    prefix = 'KEVM'
    escaped = name_escaped(input, prefix)

    # Then
    assert escaped == output

    # When
    unescaped = name_unescaped(output, prefix)

    # Then
    assert unescaped == input
