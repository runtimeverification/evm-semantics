from __future__ import annotations

import json
from pathlib import Path
from typing import TYPE_CHECKING

from pyk.proof.reachability import APRProof

from kevm_pyk.solc_to_k import Contract
from tests.unit.utils import TEST_DATA_DIR

if TYPE_CHECKING:
    from typing import Final

LIST_DATA_DIR: Final = TEST_DATA_DIR / 'foundry-list'
LIST_OUT: Final = LIST_DATA_DIR / 'out/'
LIST_APR_PROOF: Final = LIST_OUT / 'apr_proofs/'
LIST_EXPECTED: Final = LIST_DATA_DIR / 'foundry-list.expected'


def contracts() -> dict[str, Contract]:
    pattern = '*.sol/*.json'
    paths = LIST_OUT.glob(pattern)
    json_paths = [str(path) for path in paths]
    json_paths = [json_path for json_path in json_paths if not json_path.endswith('.metadata.json')]
    json_paths = sorted(json_paths)  # Must sort to get consistent output order on different platforms
    _contracts = {}
    for json_path in json_paths:
        contract_name = json_path.split('/')[-1]
        contract_json = json.loads(Path(json_path).read_text())
        contract_name = contract_name[0:-5] if contract_name.endswith('.json') else contract_name
        _contracts[contract_name] = Contract(contract_name, contract_json, foundry=True)
    return _contracts


def foundry_list() -> list[str]:
    all_methods = [f'{contract.name}.{method.name}' for contract in contracts().values() for method in contract.methods]

    lines: list[str] = []
    for method in sorted(all_methods):
        contract_name, test_name = method.split('.')
        proof_digest = f'{contract_name}.{test_name}:{contracts()[contract_name].method_by_name[test_name].digest}'
        if APRProof.proof_exists(proof_digest, LIST_APR_PROOF):
            apr_proof = APRProof.read_proof(proof_digest, LIST_APR_PROOF)
            lines.extend(str(apr_proof.summary))
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
