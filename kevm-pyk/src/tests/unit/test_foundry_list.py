from __future__ import annotations

from typing import TYPE_CHECKING

from pyk.proof.reachability import APRProof

from kevm_pyk.foundry import Foundry
from tests.unit.utils import TEST_DATA_DIR

if TYPE_CHECKING:
    from typing import Final

LIST_DATA_DIR: Final = TEST_DATA_DIR / 'foundry-list'
LIST_OUT: Final = LIST_DATA_DIR / 'out/'
LIST_APR_PROOF: Final = LIST_OUT / 'apr_proofs/'
LIST_EXPECTED: Final = LIST_DATA_DIR / 'foundry-list.expected'


def foundry_list() -> list[str]:
    foundry = Foundry(LIST_DATA_DIR)
    all_methods = [
        f'{contract.name}.{method.name}' for contract in foundry.contracts.values() for method in contract.methods
    ]

    lines: list[str] = []
    for method in sorted(all_methods):
        contract_name, test_name = method.split('.')
        proof_digest = (
            f'{contract_name}.{test_name}:{foundry.contracts[contract_name].method_by_name[test_name].digest}'
        )
        if APRProof.proof_exists(proof_digest, LIST_APR_PROOF):
            apr_proof = APRProof.read_proof(proof_digest, LIST_APR_PROOF)
            lines.append(str(apr_proof.summary))
            lines.append('')
    if len(lines) > 0:
        lines = lines[0:-1]

    return lines


def test_foundry_list(update_expected_output: bool) -> None:
    with LIST_EXPECTED.open() as f:
        foundry_list_expected = f.read().rstrip()
    assert foundry_list_expected

    list_out = '\n'.join(foundry_list())

    if update_expected_output:
        LIST_EXPECTED.write_text(list_out)
    else:
        assert list_out == foundry_list_expected
