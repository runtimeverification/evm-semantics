from __future__ import annotations

import json
from typing import TYPE_CHECKING

import pytest

if TYPE_CHECKING:
    from typing import Final

from pyk.kast.inner import KApply, KSort, KToken

from kevm_pyk.hello import hello
from kevm_pyk.kevm import KEVM
from kevm_pyk.solc_to_k import Contract, method_sig_from_abi


def test_hello() -> None:
    assert hello('World') == 'Hello, World!'


test1_abi = """
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
  "name": "test1",
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
"""

test2_abi = """
{
  "inputs": [],
  "name": "test2",
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
"""


test3_abi = """
{
  "inputs": [
    {
      "internalType": "uint32",
      "name": "blockNumber1",
      "type": "uint32"
    },
    {
      "internalType": "uint256",
      "name": "blockNumber2",
      "type": "uint256"
    }
  ],
  "name": "test3",
  "outputs": [
    {
      "internalType": "bytes32",
      "name": "blockHash",
      "type": "bytes32"
    }
  ],
  "stateMutability": "view",
  "type": "function"
}
"""

test4_abi = """
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
          "type": "tuple[3]"
        }
      ],
      "internalType": "struct IMulticall3.Call[]",
      "name": "calls",
      "type": "tuple[5]"
    }
  ],
  "name": "test4",
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
"""


def test_method_sig_from_abi() -> None:
    assert method_sig_from_abi(json.loads(test1_abi)) == 'test1((address,bytes)[])'
    assert method_sig_from_abi(json.loads(test2_abi)) == 'test2()'
    assert method_sig_from_abi(json.loads(test3_abi)) == 'test3(uint32,uint256)'
    assert method_sig_from_abi(json.loads(test4_abi)) == 'test4((address,(address,bytes)[3])[5])'


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
  "storageLayout": [],
  "ast": {
    "absolutePath": "lib/forge-std/src/interfaces/IMulticall3.sol",
    "nodes": [
      {
        "nodeType": "ContractDefinition",
        "name": "TestContract",
        "nodes": []
      }
    ]
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


TEST_DATA: Final = [
    ('too-low-int', KApply('<k>', [KToken('100', 'Int')]), KApply('<k>', KToken('100', 'Int'))),
    ('int-to-hex', KApply('<k>', [KToken('1234', 'Int')]), KApply('<k>', KToken('0x4d2', 'Int'))),
    ('bytes-to-hex-empty', KApply('<k>', [KToken('b""', 'Bytes')]), KApply('<k>', KToken('0x', 'Bytes'))),
    (
        'bytes-to-hex-nonempty',
        KApply('<k>', [KToken('b"\\xa6\\xb9c\\x9d"', 'Bytes')]),
        KApply('<k>', KToken('0xa6b9639d', 'Bytes')),
    ),
    (
        'kast-to-hex',
        KApply(
            '<generatedTop>',
            KApply('<coinbase>', KToken('728815563385977040452943777879061427756277306518', 'Int')),
            KApply('<pc>', KToken('100', 'Int')),
            KApply('<output>', KToken('b"\x00\x00\x00\x3c\x60\xf5"', 'Bytes')),
            KApply('<program>', KToken('b"\xcc\xff\xff\xfac\x60\xf5"', 'Bytes')),
        ),
        KApply(
            '<generatedTop>',
            KApply('<coinbase>', KToken('0x7fa9385be102ac3eac297483dd6233d62b3e1496', 'Int')),
            KApply('<pc>', KToken('100', 'Int')),
            KApply('<output>', KToken('0x0000003c60f5', 'Bytes')),
            KApply('<program>', KToken('0xccfffffa6360f5', 'Bytes')),
        ),
    ),
]


@pytest.mark.parametrize(
    'test_id,input,result',
    TEST_DATA,
    ids=[test_id for test_id, *_ in TEST_DATA],
)
def test_int_to_hex(test_id: str, input: KApply, result: KApply) -> None:
    to_hex = KEVM._int_token_to_hex(input)
    assert type(to_hex) is KApply
    assert to_hex == result
