from __future__ import annotations

import json
from typing import TYPE_CHECKING

import pytest
from tests.utils import REPO_ROOT

from pyk.proof import APRProof

if TYPE_CHECKING:
    from pathlib import Path
    from typing import Final

TEST_DATA = REPO_ROOT / 'kevm-pyk/src/tests/unit/test-data'

FOUNDRY_LIST_PATH: Final = TEST_DATA / 'foundry-list.expected'
APR_PROOFS: Final = tuple((TEST_DATA / 'apr_proofs').glob('*.json'))
assert APR_PROOFS

with FOUNDRY_LIST_PATH.open() as f:
    foundry_list_expected = f.read()
assert foundry_list_expected

lists = foundry_list_expected.split('\n\n')
assert len(lists) == len(APR_PROOFS)

list_ids = set([list_output.split('\n')[0].split(': ')[1] for list_output in lists])
assert len(list_ids) == len(APR_PROOFS)

@pytest.mark.parametrize('apr_proof', APR_PROOFS, ids=[str(apr_proof.relative_to(TEST_DATA)) for apr_proof in APR_PROOFS])
def test_foundry_list(apr_proof: Path) -> None:
    with apr_proof.open() as f:
        raw_proof = json.load(f)

    proof = APRProof.from_dict(raw_proof)

    assert proof.id in list_ids

    assert True
