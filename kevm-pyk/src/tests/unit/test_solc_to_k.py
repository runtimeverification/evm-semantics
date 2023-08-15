from __future__ import annotations

import pytest

from kevm_pyk.utils import name_escaped, name_unescaped

TEST_DATA: list[tuple[str, str, str]] = [
    ('has_underscore', 'My_contract', 'KEVMMyz5fcontract'),
    ('starts_lower', 'mycontract', 'KEVMmycontract'),
    ('starts_underscore', '_method', 'KEVMz5fmethod'),
    ('with_escape', 'z_', 'KEVMz7az5f'),
    ('with_escape', 'zKEVM_', 'KEVMz7aKEVMz5f'),
]


@pytest.mark.parametrize('test_id,input,output', TEST_DATA, ids=[test_id for test_id, *_ in TEST_DATA])
def test_escaping(test_id: str, input: str, output: str) -> None:
    # When
    prefix = 'KEVM'
    escaped = name_escaped(input, prefix)

    # Then
    assert escaped == output

    # And When
    unescaped = name_unescaped(output, prefix)

    # Then
    assert unescaped == input
