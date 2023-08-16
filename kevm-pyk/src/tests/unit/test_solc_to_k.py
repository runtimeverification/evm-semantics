from __future__ import annotations

import pytest

from kevm_pyk.utils import name_escaped, name_unescaped

TEST_DATA: list[tuple[str, str, str, str]] = [
    ('has_underscore', 'KEVM', 'My_contract', 'KEVMMyz5fcontract'),
    ('no_change', '', 'mycontract', 'mycontract'),
    ('starts_underscore', 'KEVM', '_method', 'KEVMz5fmethod'),
    ('with_escape', '', 'z_', 'z7az5f'),
    ('with_escape', 'KEVM', 'zKEVM_', 'KEVMz7aKEVMz5f'),
]


@pytest.mark.parametrize('test_id,prefix,input,output', TEST_DATA, ids=[test_id for test_id, *_ in TEST_DATA])
def test_escaping(test_id: str, prefix: str, input: str, output: str) -> None:
    # When
    escaped = name_escaped(input, prefix)

    # Then
    assert escaped == output

    # And When
    unescaped = name_unescaped(output, prefix)

    # Then
    assert unescaped == input
