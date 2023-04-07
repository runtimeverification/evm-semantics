import json

from pyk.kast.inner import KSort

from kevm_pyk.hello import hello
from kevm_pyk.solc_to_k import Contract


def test_hello() -> None:
    assert hello('World') == 'Hello, World!'


contract_json = """
{
  "abi": [
    {
      "inputs": [
        {
          "components": [
            {
              "internalType": "address",
              "name": "target",
              "type": "address"
            },
            {
              "internalType": "bytes",
              "name": "callData",
              "type": "bytes"
            }
          ],
          "internalType": "struct IMulticall3.Call[]",
          "name": "calls",
          "type": "tuple[]"
        }
      ],
      "name": "aggregate",
      "outputs": [
        {
          "internalType": "uint256",
          "name": "blockNumber",
          "type": "uint256"
        },
        {
          "internalType": "bytes[]",
          "name": "returnData",
          "type": "bytes[]"
        }
      ],
      "stateMutability": "payable",
      "type": "function"
    }
  ],
  "deployedBytecode": {
    "object": "0x",
    "sourceMap": "",
    "linkReferences": {}
  },
  "methodIdentifiers": {
    "aggregate((address,bytes)[])": "252dba42"
  },
  "ast": {
    "absolutePath": "lib/forge-std/src/interfaces/IMulticall3.sol"
  },
  "id": 17
}
"""


def test_contract_creation() -> None:
    contract = Contract('TestContract', json.loads(contract_json), foundry=True)
    assert len(contract.methods) == 1
    method = contract.methods[0]
    assert method.sort == KSort('TestContractMethod')
    assert method.id == int('252dba42', 16)
    assert method.arg_types == ('tuple[]',)
    assert method.contract_name == 'TestContract'
    assert method.payable
