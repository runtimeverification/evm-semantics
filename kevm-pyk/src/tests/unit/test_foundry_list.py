from __future__ import annotations

import json
from functools import cached_property
from os import listdir
from pathlib import Path
from typing import TYPE_CHECKING

from kevm_pyk.foundry import foundry_list
from kevm_pyk.solc_to_k import Contract
from tests.unit.utils import TEST_DATA_DIR

# from pyk.proof.reachability import APRProof


# from unittest.mock import patch


if TYPE_CHECKING:
    from typing import Final

    from pytest_mock import MockerFixture


LIST_DATA_DIR: Final = TEST_DATA_DIR / 'foundry-list'
LIST_OUT: Final = LIST_DATA_DIR / 'out/'
LIST_APR_PROOF: Final = LIST_OUT / 'apr_proofs/'
LIST_EXPECTED: Final = LIST_DATA_DIR / 'foundry-list.expected'


class FoundryMock:
    out = LIST_OUT

    @cached_property
    def contracts(self) -> dict[str, Contract]:
        ret: dict[str, Contract] = {}
        for proof_file in listdir(LIST_APR_PROOF):
            proof_path = LIST_APR_PROOF / proof_file
            proof_dict = json.loads(Path(proof_path).read_text())
            pid = proof_dict['id']
            contract = Contract.__new__(Contract)
            full_method = pid.split(':')[0]
            method = Contract.Method.__new__(Contract.Method)
            contract.name, method.name = full_method.split('.')
            if not hasattr(contract, 'methods'):
                contract.methods = ()
            contract.methods = contract.methods + (method,)
            ret[proof_file] = contract
        return ret

    def proof_digest(self, contract: str, test: str) -> str:
        for proof_file in listdir(LIST_APR_PROOF):
            proof_path = LIST_APR_PROOF / proof_file
            proof_dict = json.loads(Path(proof_path).read_text())
            pid = proof_dict['id']
            if pid.startswith(f'{contract}.{test}'):
                return pid
        return ''


def test_foundry_list(mocker: MockerFixture, update_expected_output: bool) -> None:
    foundry_mock = mocker.patch('kevm_pyk.foundry.Foundry')
    foundry_mock.return_value = FoundryMock()

    with LIST_EXPECTED.open() as f:
        foundry_list_expected = f.read().rstrip()
    assert foundry_list_expected

    list_out = '\n'.join(foundry_list(LIST_DATA_DIR))

    if update_expected_output:
        LIST_EXPECTED.write_text(list_out)
    else:
        assert list_out == foundry_list_expected
