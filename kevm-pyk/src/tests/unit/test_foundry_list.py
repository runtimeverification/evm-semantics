from __future__ import annotations

import json
from typing import TYPE_CHECKING

import pytest
from pyk.proof import APRProof

from tests.utils import REPO_ROOT

if TYPE_CHECKING:
    from pathlib import Path
    from typing import Final

TEST_DATA = REPO_ROOT / 'kevm-pyk/src/tests/unit/test-data'

FOUNDRY_LIST_PATH: Final = TEST_DATA / 'foundry-list.expected'
APR_PROOFS: Final = tuple((TEST_DATA / 'apr_proofs').glob('*.json'))
assert APR_PROOFS


class APRProofOutput:
    def from_str(self, list_out: str) -> list[str]:
        return list_out.split(':')


with FOUNDRY_LIST_PATH.open() as f:
    foundry_list_expected = f.read()
assert foundry_list_expected

lists = foundry_list_expected.split('\n\n')
assert len(lists) == len(APR_PROOFS)

list_outputs = {list_output.split('\n')[0].split(': ')[1]: list_output.rstrip('\n') for list_output in lists}


@pytest.mark.parametrize(
    'apr_proof', APR_PROOFS, ids=[str(apr_proof.relative_to(TEST_DATA)) for apr_proof in APR_PROOFS]
)
def test_foundry_list(apr_proof: Path) -> None:
    with apr_proof.open() as f:
        raw_proof = json.load(f)

    proof = APRProof.from_dict(raw_proof)
    summary = '\n'.join([comp for comp in proof.summary])  # noqa: C416

    list_out = list_outputs.get(proof.id)
    assert list_out is not None

    assert summary == list_out
