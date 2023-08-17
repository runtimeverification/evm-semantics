from __future__ import annotations

import pytest

from kontrol.solc_to_k import Contract

TEST_DATA: list[tuple[str, str, str, str]] = [
    ('has_underscore', 'S2K', 'My_contract', 'S2KMyz5fcontract'),
    ('no_change', '', 'mycontract', 'mycontract'),
    ('starts_underscore', 'S2K', '_method', 'S2Kz5fmethod'),
    ('with_escape', '', 'z_', 'z7az5f'),
    ('with_escape', 'S2K', 'zS2K_', 'S2Kz7aS2Kz5f'),
]


@pytest.mark.parametrize('test_id,prefix,input,output', TEST_DATA, ids=[test_id for test_id, *_ in TEST_DATA])
def test_escaping(test_id: str, prefix: str, input: str, output: str) -> None:
    # When
    escaped = Contract.escaped(input, prefix)

    # Then
    assert escaped == output

    # And When
    unescaped = Contract.unescaped(output, prefix)

    # Then
    assert unescaped == input
