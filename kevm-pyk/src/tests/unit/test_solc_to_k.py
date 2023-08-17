from __future__ import annotations

from typing import TYPE_CHECKING

import pytest
from pyk.kast.inner import KToken, KVariable

from kevm_pyk.kevm import KEVM
from kontrol.solc_to_k import _range_predicate

from .utils import TEST_DATA_DIR

if TYPE_CHECKING:
    from typing import Final

    from pyk.kast.inner import KInner


EXAMPLES_DIR: Final = TEST_DATA_DIR / 'examples'

PREDICATE_DATA: list[tuple[str, KInner, str, KInner | None]] = [
    ('bytes4', KVariable('V0_x'), 'bytes4', KEVM.range_bytes(KToken('4', 'Int'), KVariable('V0_x'))),
    ('int128', KVariable('V0_x'), 'int128', KEVM.range_sint(128, KVariable('V0_x'))),
    ('int24', KVariable('V0_x'), 'int24', KEVM.range_sint(24, KVariable('V0_x'))),
    ('uint24', KVariable('V0_x'), 'uint24', KEVM.range_uint(24, KVariable('V0_x'))),
]


@pytest.mark.parametrize(
    'test_id,term,type,expected',
    PREDICATE_DATA,
    ids=[test_id for test_id, *_ in PREDICATE_DATA],
)
def test_range_predicate(test_id: str, term: KInner, type: str, expected: KInner | None) -> None:
    # When
    ret = _range_predicate(term, type)

    # Then
    assert ret == expected


from kontrol.solc_to_k import Contract

ESCAPE_DATA: list[tuple[str, str, str, str]] = [
    ('has_underscore', 'S2K', 'My_contract', 'S2KMyz5fcontract'),
    ('no_change', '', 'mycontract', 'mycontract'),
    ('starts_underscore', 'S2K', '_method', 'S2Kz5fmethod'),
    ('with_escape', '', 'z_', 'z7az5f'),
    ('with_escape', 'S2K', 'zS2K_', 'S2Kz7aS2Kz5f'),
]


@pytest.mark.parametrize('test_id,prefix,input,output', ESCAPE_DATA, ids=[test_id for test_id, *_ in ESCAPE_DATA])
def test_escaping(test_id: str, prefix: str, input: str, output: str) -> None:
    # When
    escaped = Contract.escaped(input, prefix)

    # Then
    assert escaped == output

    # And When
    unescaped = Contract.unescaped(output, prefix)

    # Then
    assert unescaped == input
