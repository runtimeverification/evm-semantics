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
    },
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
              "internalType": "bool",
              "name": "allowFailure",
              "type": "bool"
            },
            {
              "internalType": "bytes",
              "name": "callData",
              "type": "bytes"
            }
          ],
          "internalType": "struct IMulticall3.Call3[]",
          "name": "calls",
          "type": "tuple[]"
        }
      ],
      "name": "aggregate3",
      "outputs": [
        {
          "components": [
            {
              "internalType": "bool",
              "name": "success",
              "type": "bool"
            },
            {
              "internalType": "bytes",
              "name": "returnData",
              "type": "bytes"
            }
          ],
          "internalType": "struct IMulticall3.Result[]",
          "name": "returnData",
          "type": "tuple[]"
        }
      ],
      "stateMutability": "payable",
      "type": "function"
    },
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
              "internalType": "bool",
              "name": "allowFailure",
              "type": "bool"
            },
            {
              "internalType": "uint256",
              "name": "value",
              "type": "uint256"
            },
            {
              "internalType": "bytes",
              "name": "callData",
              "type": "bytes"
            }
          ],
          "internalType": "struct IMulticall3.Call3Value[]",
          "name": "calls",
          "type": "tuple[]"
        }
      ],
      "name": "aggregate3Value",
      "outputs": [
        {
          "components": [
            {
              "internalType": "bool",
              "name": "success",
              "type": "bool"
            },
            {
              "internalType": "bytes",
              "name": "returnData",
              "type": "bytes"
            }
          ],
          "internalType": "struct IMulticall3.Result[]",
          "name": "returnData",
          "type": "tuple[]"
        }
      ],
      "stateMutability": "payable",
      "type": "function"
    },
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
      "name": "blockAndAggregate",
      "outputs": [
        {
          "internalType": "uint256",
          "name": "blockNumber",
          "type": "uint256"
        },
        {
          "internalType": "bytes32",
          "name": "blockHash",
          "type": "bytes32"
        },
        {
          "components": [
            {
              "internalType": "bool",
              "name": "success",
              "type": "bool"
            },
            {
              "internalType": "bytes",
              "name": "returnData",
              "type": "bytes"
            }
          ],
          "internalType": "struct IMulticall3.Result[]",
          "name": "returnData",
          "type": "tuple[]"
        }
      ],
      "stateMutability": "payable",
      "type": "function"
    },
    {
      "inputs": [],
      "name": "getBasefee",
      "outputs": [
        {
          "internalType": "uint256",
          "name": "basefee",
          "type": "uint256"
        }
      ],
      "stateMutability": "view",
      "type": "function"
    },
    {
      "inputs": [
        {
          "internalType": "uint256",
          "name": "blockNumber",
          "type": "uint256"
        }
      ],
      "name": "getBlockHash",
      "outputs": [
        {
          "internalType": "bytes32",
          "name": "blockHash",
          "type": "bytes32"
        }
      ],
      "stateMutability": "view",
      "type": "function"
    },
    {
      "inputs": [],
      "name": "getBlockNumber",
      "outputs": [
        {
          "internalType": "uint256",
          "name": "blockNumber",
          "type": "uint256"
        }
      ],
      "stateMutability": "view",
      "type": "function"
    },
    {
      "inputs": [],
      "name": "getChainId",
      "outputs": [
        {
          "internalType": "uint256",
          "name": "chainid",
          "type": "uint256"
        }
      ],
      "stateMutability": "view",
      "type": "function"
    },
    {
      "inputs": [],
      "name": "getCurrentBlockCoinbase",
      "outputs": [
        {
          "internalType": "address",
          "name": "coinbase",
          "type": "address"
        }
      ],
      "stateMutability": "view",
      "type": "function"
    },
    {
      "inputs": [],
      "name": "getCurrentBlockDifficulty",
      "outputs": [
        {
          "internalType": "uint256",
          "name": "difficulty",
          "type": "uint256"
        }
      ],
      "stateMutability": "view",
      "type": "function"
    },
    {
      "inputs": [],
      "name": "getCurrentBlockGasLimit",
      "outputs": [
        {
          "internalType": "uint256",
          "name": "gaslimit",
          "type": "uint256"
        }
      ],
      "stateMutability": "view",
      "type": "function"
    },
    {
      "inputs": [],
      "name": "getCurrentBlockTimestamp",
      "outputs": [
        {
          "internalType": "uint256",
          "name": "timestamp",
          "type": "uint256"
        }
      ],
      "stateMutability": "view",
      "type": "function"
    },
    {
      "inputs": [
        {
          "internalType": "address",
          "name": "addr",
          "type": "address"
        }
      ],
      "name": "getEthBalance",
      "outputs": [
        {
          "internalType": "uint256",
          "name": "balance",
          "type": "uint256"
        }
      ],
      "stateMutability": "view",
      "type": "function"
    },
    {
      "inputs": [],
      "name": "getLastBlockHash",
      "outputs": [
        {
          "internalType": "bytes32",
          "name": "blockHash",
          "type": "bytes32"
        }
      ],
      "stateMutability": "view",
      "type": "function"
    },
    {
      "inputs": [
        {
          "internalType": "bool",
          "name": "requireSuccess",
          "type": "bool"
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
          "type": "tuple[]"
        }
      ],
      "name": "tryAggregate",
      "outputs": [
        {
          "components": [
            {
              "internalType": "bool",
              "name": "success",
              "type": "bool"
            },
            {
              "internalType": "bytes",
              "name": "returnData",
              "type": "bytes"
            }
          ],
          "internalType": "struct IMulticall3.Result[]",
          "name": "returnData",
          "type": "tuple[]"
        }
      ],
      "stateMutability": "payable",
      "type": "function"
    },
    {
      "inputs": [
        {
          "internalType": "bool",
          "name": "requireSuccess",
          "type": "bool"
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
          "type": "tuple[]"
        }
      ],
      "name": "tryBlockAndAggregate",
      "outputs": [
        {
          "internalType": "uint256",
          "name": "blockNumber",
          "type": "uint256"
        },
        {
          "internalType": "bytes32",
          "name": "blockHash",
          "type": "bytes32"
        },
        {
          "components": [
            {
              "internalType": "bool",
              "name": "success",
              "type": "bool"
            },
            {
              "internalType": "bytes",
              "name": "returnData",
              "type": "bytes"
            }
          ],
          "internalType": "struct IMulticall3.Result[]",
          "name": "returnData",
          "type": "tuple[]"
        }
      ],
      "stateMutability": "payable",
      "type": "function"
    }
  ],
  "bytecode": {
    "object": "0x",
    "sourceMap": "",
    "linkReferences": {}
  },
  "deployedBytecode": {
    "object": "0x",
    "sourceMap": "",
    "linkReferences": {}
  },
  "methodIdentifiers": {
    "aggregate((address,bytes)[])": "252dba42",
    "aggregate3((address,bool,bytes)[])": "82ad56cb",
    "aggregate3Value((address,bool,uint256,bytes)[])": "174dea71",
    "blockAndAggregate((address,bytes)[])": "c3077fa9",
    "getBasefee()": "3e64a696",
    "getBlockHash(uint256)": "ee82ac5e",
    "getBlockNumber()": "42cbb15c",
    "getChainId()": "3408e470",
    "getCurrentBlockCoinbase()": "a8b0574e",
    "getCurrentBlockDifficulty()": "72425d9d",
    "getCurrentBlockGasLimit()": "86d516e8",
    "getCurrentBlockTimestamp()": "0f28c97d",
    "getEthBalance(address)": "4d2301cc",
    "getLastBlockHash()": "27e86d6e",
    "tryAggregate(bool,(address,bytes)[])": "bce38bd7",
    "tryBlockAndAggregate(bool,(address,bytes)[])": "399542e9"
  },
  "metadata": {
    "compiler": {
      "version": "0.8.13+commit.abaa5c0e"
    },
    "language": "Solidity",
    "output": {
      "abi": [
        {
          "inputs": [
            {
              "internalType": "struct IMulticall3.Call[]",
              "name": "calls",
              "type": "tuple[]",
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
              ]
            }
          ],
          "stateMutability": "payable",
          "type": "function",
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
          ]
        },
        {
          "inputs": [
            {
              "internalType": "struct IMulticall3.Call3[]",
              "name": "calls",
              "type": "tuple[]",
              "components": [
                {
                  "internalType": "address",
                  "name": "target",
                  "type": "address"
                },
                {
                  "internalType": "bool",
                  "name": "allowFailure",
                  "type": "bool"
                },
                {
                  "internalType": "bytes",
                  "name": "callData",
                  "type": "bytes"
                }
              ]
            }
          ],
          "stateMutability": "payable",
          "type": "function",
          "name": "aggregate3",
          "outputs": [
            {
              "internalType": "struct IMulticall3.Result[]",
              "name": "returnData",
              "type": "tuple[]",
              "components": [
                {
                  "internalType": "bool",
                  "name": "success",
                  "type": "bool"
                },
                {
                  "internalType": "bytes",
                  "name": "returnData",
                  "type": "bytes"
                }
              ]
            }
          ]
        },
        {
          "inputs": [
            {
              "internalType": "struct IMulticall3.Call3Value[]",
              "name": "calls",
              "type": "tuple[]",
              "components": [
                {
                  "internalType": "address",
                  "name": "target",
                  "type": "address"
                },
                {
                  "internalType": "bool",
                  "name": "allowFailure",
                  "type": "bool"
                },
                {
                  "internalType": "uint256",
                  "name": "value",
                  "type": "uint256"
                },
                {
                  "internalType": "bytes",
                  "name": "callData",
                  "type": "bytes"
                }
              ]
            }
          ],
          "stateMutability": "payable",
          "type": "function",
          "name": "aggregate3Value",
          "outputs": [
            {
              "internalType": "struct IMulticall3.Result[]",
              "name": "returnData",
              "type": "tuple[]",
              "components": [
                {
                  "internalType": "bool",
                  "name": "success",
                  "type": "bool"
                },
                {
                  "internalType": "bytes",
                  "name": "returnData",
                  "type": "bytes"
                }
              ]
            }
          ]
        },
        {
          "inputs": [
            {
              "internalType": "struct IMulticall3.Call[]",
              "name": "calls",
              "type": "tuple[]",
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
              ]
            }
          ],
          "stateMutability": "payable",
          "type": "function",
          "name": "blockAndAggregate",
          "outputs": [
            {
              "internalType": "uint256",
              "name": "blockNumber",
              "type": "uint256"
            },
            {
              "internalType": "bytes32",
              "name": "blockHash",
              "type": "bytes32"
            },
            {
              "internalType": "struct IMulticall3.Result[]",
              "name": "returnData",
              "type": "tuple[]",
              "components": [
                {
                  "internalType": "bool",
                  "name": "success",
                  "type": "bool"
                },
                {
                  "internalType": "bytes",
                  "name": "returnData",
                  "type": "bytes"
                }
              ]
            }
          ]
        },
        {
          "inputs": [],
          "stateMutability": "view",
          "type": "function",
          "name": "getBasefee",
          "outputs": [
            {
              "internalType": "uint256",
              "name": "basefee",
              "type": "uint256"
            }
          ]
        },
        {
          "inputs": [
            {
              "internalType": "uint256",
              "name": "blockNumber",
              "type": "uint256"
            }
          ],
          "stateMutability": "view",
          "type": "function",
          "name": "getBlockHash",
          "outputs": [
            {
              "internalType": "bytes32",
              "name": "blockHash",
              "type": "bytes32"
            }
          ]
        },
        {
          "inputs": [],
          "stateMutability": "view",
          "type": "function",
          "name": "getBlockNumber",
          "outputs": [
            {
              "internalType": "uint256",
              "name": "blockNumber",
              "type": "uint256"
            }
          ]
        },
        {
          "inputs": [],
          "stateMutability": "view",
          "type": "function",
          "name": "getChainId",
          "outputs": [
            {
              "internalType": "uint256",
              "name": "chainid",
              "type": "uint256"
            }
          ]
        },
        {
          "inputs": [],
          "stateMutability": "view",
          "type": "function",
          "name": "getCurrentBlockCoinbase",
          "outputs": [
            {
              "internalType": "address",
              "name": "coinbase",
              "type": "address"
            }
          ]
        },
        {
          "inputs": [],
          "stateMutability": "view",
          "type": "function",
          "name": "getCurrentBlockDifficulty",
          "outputs": [
            {
              "internalType": "uint256",
              "name": "difficulty",
              "type": "uint256"
            }
          ]
        },
        {
          "inputs": [],
          "stateMutability": "view",
          "type": "function",
          "name": "getCurrentBlockGasLimit",
          "outputs": [
            {
              "internalType": "uint256",
              "name": "gaslimit",
              "type": "uint256"
            }
          ]
        },
        {
          "inputs": [],
          "stateMutability": "view",
          "type": "function",
          "name": "getCurrentBlockTimestamp",
          "outputs": [
            {
              "internalType": "uint256",
              "name": "timestamp",
              "type": "uint256"
            }
          ]
        },
        {
          "inputs": [
            {
              "internalType": "address",
              "name": "addr",
              "type": "address"
            }
          ],
          "stateMutability": "view",
          "type": "function",
          "name": "getEthBalance",
          "outputs": [
            {
              "internalType": "uint256",
              "name": "balance",
              "type": "uint256"
            }
          ]
        },
        {
          "inputs": [],
          "stateMutability": "view",
          "type": "function",
          "name": "getLastBlockHash",
          "outputs": [
            {
              "internalType": "bytes32",
              "name": "blockHash",
              "type": "bytes32"
            }
          ]
        },
        {
          "inputs": [
            {
              "internalType": "bool",
              "name": "requireSuccess",
              "type": "bool"
            },
            {
              "internalType": "struct IMulticall3.Call[]",
              "name": "calls",
              "type": "tuple[]",
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
              ]
            }
          ],
          "stateMutability": "payable",
          "type": "function",
          "name": "tryAggregate",
          "outputs": [
            {
              "internalType": "struct IMulticall3.Result[]",
              "name": "returnData",
              "type": "tuple[]",
              "components": [
                {
                  "internalType": "bool",
                  "name": "success",
                  "type": "bool"
                },
                {
                  "internalType": "bytes",
                  "name": "returnData",
                  "type": "bytes"
                }
              ]
            }
          ]
        },
        {
          "inputs": [
            {
              "internalType": "bool",
              "name": "requireSuccess",
              "type": "bool"
            },
            {
              "internalType": "struct IMulticall3.Call[]",
              "name": "calls",
              "type": "tuple[]",
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
              ]
            }
          ],
          "stateMutability": "payable",
          "type": "function",
          "name": "tryBlockAndAggregate",
          "outputs": [
            {
              "internalType": "uint256",
              "name": "blockNumber",
              "type": "uint256"
            },
            {
              "internalType": "bytes32",
              "name": "blockHash",
              "type": "bytes32"
            },
            {
              "internalType": "struct IMulticall3.Result[]",
              "name": "returnData",
              "type": "tuple[]",
              "components": [
                {
                  "internalType": "bool",
                  "name": "success",
                  "type": "bool"
                },
                {
                  "internalType": "bytes",
                  "name": "returnData",
                  "type": "bytes"
                }
              ]
            }
          ]
        }
      ],
      "devdoc": {
        "kind": "dev",
        "methods": {},
        "version": 1
      },
      "userdoc": {
        "kind": "user",
        "methods": {},
        "version": 1
      }
    },
    "settings": {
      "remappings": [
        ":ds-test/=lib/forge-std/lib/ds-test/src/",
        ":forge-std/=lib/forge-std/src/"
      ],
      "optimizer": {
        "enabled": true,
        "runs": 200
      },
      "metadata": {
        "bytecodeHash": "ipfs"
      },
      "compilationTarget": {
        "lib/forge-std/src/interfaces/IMulticall3.sol": "IMulticall3"
      },
      "libraries": {}
    },
    "sources": {
      "lib/forge-std/src/interfaces/IMulticall3.sol": {
        "keccak256": "0x7aac1389150499a922d1f9ef5749c908cef127cb2075b92fa17e9cb611263d0a",
        "urls": [
          "bzz-raw://d95ebb7c7c463e08ebc12dab639945752fb2480acfc6e86da32f72732a7fd0c0",
          "dweb:/ipfs/QmNXK8P8oPWwajsQHvAHw3JPyQidPLCGQN3hWu1Lk6PBL2"
        ],
        "license": "MIT"
      }
    },
    "version": 1
  },
  "ast": {
    "absolutePath": "lib/forge-std/src/interfaces/IMulticall3.sol",
    "id": 28426,
    "exportedSymbols": {
      "IMulticall3": [
        28425
      ]
    },
    "nodeType": "SourceUnit",
    "src": "32:2153:17",
    "nodes": [
      {
        "id": 28264,
        "nodeType": "PragmaDirective",
        "src": "32:31:17",
        "nodes": [],
        "literals": [
          "solidity",
          ">=",
          "0.6",
          ".2",
          "<",
          "0.9",
          ".0"
        ]
      },
      {
        "id": 28265,
        "nodeType": "PragmaDirective",
        "src": "65:33:17",
        "nodes": [],
        "literals": [
          "experimental",
          "ABIEncoderV2"
        ]
      },
      {
        "id": 28425,
        "nodeType": "ContractDefinition",
        "src": "100:2084:17",
        "nodes": [
          {
            "id": 28270,
            "nodeType": "StructDefinition",
            "src": "128:67:17",
            "nodes": [],
            "canonicalName": "IMulticall3.Call",
            "members": [
              {
                "constant": false,
                "id": 28267,
                "mutability": "mutable",
                "name": "target",
                "nameLocation": "158:6:17",
                "nodeType": "VariableDeclaration",
                "scope": 28270,
                "src": "150:14:17",
                "stateVariable": false,
                "storageLocation": "default",
                "typeDescriptions": {
                  "typeIdentifier": "t_address",
                  "typeString": "address"
                },
                "typeName": {
                  "id": 28266,
                  "name": "address",
                  "nodeType": "ElementaryTypeName",
                  "src": "150:7:17",
                  "stateMutability": "nonpayable",
                  "typeDescriptions": {
                    "typeIdentifier": "t_address",
                    "typeString": "address"
                  }
                },
                "visibility": "internal"
              },
              {
                "constant": false,
                "id": 28269,
                "mutability": "mutable",
                "name": "callData",
                "nameLocation": "180:8:17",
                "nodeType": "VariableDeclaration",
                "scope": 28270,
                "src": "174:14:17",
                "stateVariable": false,
                "storageLocation": "default",
                "typeDescriptions": {
                  "typeIdentifier": "t_bytes_storage_ptr",
                  "typeString": "bytes"
                },
                "typeName": {
                  "id": 28268,
                  "name": "bytes",
                  "nodeType": "ElementaryTypeName",
                  "src": "174:5:17",
                  "typeDescriptions": {
                    "typeIdentifier": "t_bytes_storage_ptr",
                    "typeString": "bytes"
                  }
                },
                "visibility": "internal"
              }
            ],
            "name": "Call",
            "nameLocation": "135:4:17",
            "scope": 28425,
            "visibility": "public"
          },
          {
            "id": 28277,
            "nodeType": "StructDefinition",
            "src": "201:95:17",
            "nodes": [],
            "canonicalName": "IMulticall3.Call3",
            "members": [
              {
                "constant": false,
                "id": 28272,
                "mutability": "mutable",
                "name": "target",
                "nameLocation": "232:6:17",
                "nodeType": "VariableDeclaration",
                "scope": 28277,
                "src": "224:14:17",
                "stateVariable": false,
                "storageLocation": "default",
                "typeDescriptions": {
                  "typeIdentifier": "t_address",
                  "typeString": "address"
                },
                "typeName": {
                  "id": 28271,
                  "name": "address",
                  "nodeType": "ElementaryTypeName",
                  "src": "224:7:17",
                  "stateMutability": "nonpayable",
                  "typeDescriptions": {
                    "typeIdentifier": "t_address",
                    "typeString": "address"
                  }
                },
                "visibility": "internal"
              },
              {
                "constant": false,
                "id": 28274,
                "mutability": "mutable",
                "name": "allowFailure",
                "nameLocation": "253:12:17",
                "nodeType": "VariableDeclaration",
                "scope": 28277,
                "src": "248:17:17",
                "stateVariable": false,
                "storageLocation": "default",
                "typeDescriptions": {
                  "typeIdentifier": "t_bool",
                  "typeString": "bool"
                },
                "typeName": {
                  "id": 28273,
                  "name": "bool",
                  "nodeType": "ElementaryTypeName",
                  "src": "248:4:17",
                  "typeDescriptions": {
                    "typeIdentifier": "t_bool",
                    "typeString": "bool"
                  }
                },
                "visibility": "internal"
              },
              {
                "constant": false,
                "id": 28276,
                "mutability": "mutable",
                "name": "callData",
                "nameLocation": "281:8:17",
                "nodeType": "VariableDeclaration",
                "scope": 28277,
                "src": "275:14:17",
                "stateVariable": false,
                "storageLocation": "default",
                "typeDescriptions": {
                  "typeIdentifier": "t_bytes_storage_ptr",
                  "typeString": "bytes"
                },
                "typeName": {
                  "id": 28275,
                  "name": "bytes",
                  "nodeType": "ElementaryTypeName",
                  "src": "275:5:17",
                  "typeDescriptions": {
                    "typeIdentifier": "t_bytes_storage_ptr",
                    "typeString": "bytes"
                  }
                },
                "visibility": "internal"
              }
            ],
            "name": "Call3",
            "nameLocation": "208:5:17",
            "scope": 28425,
            "visibility": "public"
          },
          {
            "id": 28286,
            "nodeType": "StructDefinition",
            "src": "302:123:17",
            "nodes": [],
            "canonicalName": "IMulticall3.Call3Value",
            "members": [
              {
                "constant": false,
                "id": 28279,
                "mutability": "mutable",
                "name": "target",
                "nameLocation": "338:6:17",
                "nodeType": "VariableDeclaration",
                "scope": 28286,
                "src": "330:14:17",
                "stateVariable": false,
                "storageLocation": "default",
                "typeDescriptions": {
                  "typeIdentifier": "t_address",
                  "typeString": "address"
                },
                "typeName": {
                  "id": 28278,
                  "name": "address",
                  "nodeType": "ElementaryTypeName",
                  "src": "330:7:17",
                  "stateMutability": "nonpayable",
                  "typeDescriptions": {
                    "typeIdentifier": "t_address",
                    "typeString": "address"
                  }
                },
                "visibility": "internal"
              },
              {
                "constant": false,
                "id": 28281,
                "mutability": "mutable",
                "name": "allowFailure",
                "nameLocation": "359:12:17",
                "nodeType": "VariableDeclaration",
                "scope": 28286,
                "src": "354:17:17",
                "stateVariable": false,
                "storageLocation": "default",
                "typeDescriptions": {
                  "typeIdentifier": "t_bool",
                  "typeString": "bool"
                },
                "typeName": {
                  "id": 28280,
                  "name": "bool",
                  "nodeType": "ElementaryTypeName",
                  "src": "354:4:17",
                  "typeDescriptions": {
                    "typeIdentifier": "t_bool",
                    "typeString": "bool"
                  }
                },
                "visibility": "internal"
              },
              {
                "constant": false,
                "id": 28283,
                "mutability": "mutable",
                "name": "value",
                "nameLocation": "389:5:17",
                "nodeType": "VariableDeclaration",
                "scope": 28286,
                "src": "381:13:17",
                "stateVariable": false,
                "storageLocation": "default",
                "typeDescriptions": {
                  "typeIdentifier": "t_uint256",
                  "typeString": "uint256"
                },
                "typeName": {
                  "id": 28282,
                  "name": "uint256",
                  "nodeType": "ElementaryTypeName",
                  "src": "381:7:17",
                  "typeDescriptions": {
                    "typeIdentifier": "t_uint256",
                    "typeString": "uint256"
                  }
                },
                "visibility": "internal"
              },
              {
                "constant": false,
                "id": 28285,
                "mutability": "mutable",
                "name": "callData",
                "nameLocation": "410:8:17",
                "nodeType": "VariableDeclaration",
                "scope": 28286,
                "src": "404:14:17",
                "stateVariable": false,
                "storageLocation": "default",
                "typeDescriptions": {
                  "typeIdentifier": "t_bytes_storage_ptr",
                  "typeString": "bytes"
                },
                "typeName": {
                  "id": 28284,
                  "name": "bytes",
                  "nodeType": "ElementaryTypeName",
                  "src": "404:5:17",
                  "typeDescriptions": {
                    "typeIdentifier": "t_bytes_storage_ptr",
                    "typeString": "bytes"
                  }
                },
                "visibility": "internal"
              }
            ],
            "name": "Call3Value",
            "nameLocation": "309:10:17",
            "scope": 28425,
            "visibility": "public"
          },
          {
            "id": 28291,
            "nodeType": "StructDefinition",
            "src": "431:69:17",
            "nodes": [],
            "canonicalName": "IMulticall3.Result",
            "members": [
              {
                "constant": false,
                "id": 28288,
                "mutability": "mutable",
                "name": "success",
                "nameLocation": "460:7:17",
                "nodeType": "VariableDeclaration",
                "scope": 28291,
                "src": "455:12:17",
                "stateVariable": false,
                "storageLocation": "default",
                "typeDescriptions": {
                  "typeIdentifier": "t_bool",
                  "typeString": "bool"
                },
                "typeName": {
                  "id": 28287,
                  "name": "bool",
                  "nodeType": "ElementaryTypeName",
                  "src": "455:4:17",
                  "typeDescriptions": {
                    "typeIdentifier": "t_bool",
                    "typeString": "bool"
                  }
                },
                "visibility": "internal"
              },
              {
                "constant": false,
                "id": 28290,
                "mutability": "mutable",
                "name": "returnData",
                "nameLocation": "483:10:17",
                "nodeType": "VariableDeclaration",
                "scope": 28291,
                "src": "477:16:17",
                "stateVariable": false,
                "storageLocation": "default",
                "typeDescriptions": {
                  "typeIdentifier": "t_bytes_storage_ptr",
                  "typeString": "bytes"
                },
                "typeName": {
                  "id": 28289,
                  "name": "bytes",
                  "nodeType": "ElementaryTypeName",
                  "src": "477:5:17",
                  "typeDescriptions": {
                    "typeIdentifier": "t_bytes_storage_ptr",
                    "typeString": "bytes"
                  }
                },
                "visibility": "internal"
              }
            ],
            "name": "Result",
            "nameLocation": "438:6:17",
            "scope": 28425,
            "visibility": "public"
          },
          {
            "id": 28303,
            "nodeType": "FunctionDefinition",
            "src": "506:140:17",
            "nodes": [],
            "functionSelector": "252dba42",
            "implemented": false,
            "kind": "function",
            "modifiers": [],
            "name": "aggregate",
            "nameLocation": "515:9:17",
            "parameters": {
              "id": 28296,
              "nodeType": "ParameterList",
              "parameters": [
                {
                  "constant": false,
                  "id": 28295,
                  "mutability": "mutable",
                  "name": "calls",
                  "nameLocation": "541:5:17",
                  "nodeType": "VariableDeclaration",
                  "scope": 28303,
                  "src": "525:21:17",
                  "stateVariable": false,
                  "storageLocation": "calldata",
                  "typeDescriptions": {
                    "typeIdentifier": "t_array$_t_struct$_Call_$28270_calldata_ptr_$dyn_calldata_ptr",
                    "typeString": "struct IMulticall3.Call[]"
                  },
                  "typeName": {
                    "baseType": {
                      "id": 28293,
                      "nodeType": "UserDefinedTypeName",
                      "pathNode": {
                        "id": 28292,
                        "name": "Call",
                        "nodeType": "IdentifierPath",
                        "referencedDeclaration": 28270,
                        "src": "525:4:17"
                      },
                      "referencedDeclaration": 28270,
                      "src": "525:4:17",
                      "typeDescriptions": {
                        "typeIdentifier": "t_struct$_Call_$28270_storage_ptr",
                        "typeString": "struct IMulticall3.Call"
                      }
                    },
                    "id": 28294,
                    "nodeType": "ArrayTypeName",
                    "src": "525:6:17",
                    "typeDescriptions": {
                      "typeIdentifier": "t_array$_t_struct$_Call_$28270_storage_$dyn_storage_ptr",
                      "typeString": "struct IMulticall3.Call[]"
                    }
                  },
                  "visibility": "internal"
                }
              ],
              "src": "524:23:17"
            },
            "returnParameters": {
              "id": 28302,
              "nodeType": "ParameterList",
              "parameters": [
                {
                  "constant": false,
                  "id": 28298,
                  "mutability": "mutable",
                  "name": "blockNumber",
                  "nameLocation": "606:11:17",
                  "nodeType": "VariableDeclaration",
                  "scope": 28303,
                  "src": "598:19:17",
                  "stateVariable": false,
                  "storageLocation": "default",
                  "typeDescriptions": {
                    "typeIdentifier": "t_uint256",
                    "typeString": "uint256"
                  },
                  "typeName": {
                    "id": 28297,
                    "name": "uint256",
                    "nodeType": "ElementaryTypeName",
                    "src": "598:7:17",
                    "typeDescriptions": {
                      "typeIdentifier": "t_uint256",
                      "typeString": "uint256"
                    }
                  },
                  "visibility": "internal"
                },
                {
                  "constant": false,
                  "id": 28301,
                  "mutability": "mutable",
                  "name": "returnData",
                  "nameLocation": "634:10:17",
                  "nodeType": "VariableDeclaration",
                  "scope": 28303,
                  "src": "619:25:17",
                  "stateVariable": false,
                  "storageLocation": "memory",
                  "typeDescriptions": {
                    "typeIdentifier": "t_array$_t_bytes_memory_ptr_$dyn_memory_ptr",
                    "typeString": "bytes[]"
                  },
                  "typeName": {
                    "baseType": {
                      "id": 28299,
                      "name": "bytes",
                      "nodeType": "ElementaryTypeName",
                      "src": "619:5:17",
                      "typeDescriptions": {
                        "typeIdentifier": "t_bytes_storage_ptr",
                        "typeString": "bytes"
                      }
                    },
                    "id": 28300,
                    "nodeType": "ArrayTypeName",
                    "src": "619:7:17",
                    "typeDescriptions": {
                      "typeIdentifier": "t_array$_t_bytes_storage_$dyn_storage_ptr",
                      "typeString": "bytes[]"
                    }
                  },
                  "visibility": "internal"
                }
              ],
              "src": "597:48:17"
            },
            "scope": 28425,
            "stateMutability": "payable",
            "virtual": false,
            "visibility": "external"
          },
          {
            "id": 28314,
            "nodeType": "FunctionDefinition",
            "src": "652:98:17",
            "nodes": [],
            "functionSelector": "82ad56cb",
            "implemented": false,
            "kind": "function",
            "modifiers": [],
            "name": "aggregate3",
            "nameLocation": "661:10:17",
            "parameters": {
              "id": 28308,
              "nodeType": "ParameterList",
              "parameters": [
                {
                  "constant": false,
                  "id": 28307,
                  "mutability": "mutable",
                  "name": "calls",
                  "nameLocation": "689:5:17",
                  "nodeType": "VariableDeclaration",
                  "scope": 28314,
                  "src": "672:22:17",
                  "stateVariable": false,
                  "storageLocation": "calldata",
                  "typeDescriptions": {
                    "typeIdentifier": "t_array$_t_struct$_Call3_$28277_calldata_ptr_$dyn_calldata_ptr",
                    "typeString": "struct IMulticall3.Call3[]"
                  },
                  "typeName": {
                    "baseType": {
                      "id": 28305,
                      "nodeType": "UserDefinedTypeName",
                      "pathNode": {
                        "id": 28304,
                        "name": "Call3",
                        "nodeType": "IdentifierPath",
                        "referencedDeclaration": 28277,
                        "src": "672:5:17"
                      },
                      "referencedDeclaration": 28277,
                      "src": "672:5:17",
                      "typeDescriptions": {
                        "typeIdentifier": "t_struct$_Call3_$28277_storage_ptr",
                        "typeString": "struct IMulticall3.Call3"
                      }
                    },
                    "id": 28306,
                    "nodeType": "ArrayTypeName",
                    "src": "672:7:17",
                    "typeDescriptions": {
                      "typeIdentifier": "t_array$_t_struct$_Call3_$28277_storage_$dyn_storage_ptr",
                      "typeString": "struct IMulticall3.Call3[]"
                    }
                  },
                  "visibility": "internal"
                }
              ],
              "src": "671:24:17"
            },
            "returnParameters": {
              "id": 28313,
              "nodeType": "ParameterList",
              "parameters": [
                {
                  "constant": false,
                  "id": 28312,
                  "mutability": "mutable",
                  "name": "returnData",
                  "nameLocation": "738:10:17",
                  "nodeType": "VariableDeclaration",
                  "scope": 28314,
                  "src": "722:26:17",
                  "stateVariable": false,
                  "storageLocation": "memory",
                  "typeDescriptions": {
                    "typeIdentifier": "t_array$_t_struct$_Result_$28291_memory_ptr_$dyn_memory_ptr",
                    "typeString": "struct IMulticall3.Result[]"
                  },
                  "typeName": {
                    "baseType": {
                      "id": 28310,
                      "nodeType": "UserDefinedTypeName",
                      "pathNode": {
                        "id": 28309,
                        "name": "Result",
                        "nodeType": "IdentifierPath",
                        "referencedDeclaration": 28291,
                        "src": "722:6:17"
                      },
                      "referencedDeclaration": 28291,
                      "src": "722:6:17",
                      "typeDescriptions": {
                        "typeIdentifier": "t_struct$_Result_$28291_storage_ptr",
                        "typeString": "struct IMulticall3.Result"
                      }
                    },
                    "id": 28311,
                    "nodeType": "ArrayTypeName",
                    "src": "722:8:17",
                    "typeDescriptions": {
                      "typeIdentifier": "t_array$_t_struct$_Result_$28291_storage_$dyn_storage_ptr",
                      "typeString": "struct IMulticall3.Result[]"
                    }
                  },
                  "visibility": "internal"
                }
              ],
              "src": "721:28:17"
            },
            "scope": 28425,
            "stateMutability": "payable",
            "virtual": false,
            "visibility": "external"
          },
          {
            "id": 28325,
            "nodeType": "FunctionDefinition",
            "src": "756:108:17",
            "nodes": [],
            "functionSelector": "174dea71",
            "implemented": false,
            "kind": "function",
            "modifiers": [],
            "name": "aggregate3Value",
            "nameLocation": "765:15:17",
            "parameters": {
              "id": 28319,
              "nodeType": "ParameterList",
              "parameters": [
                {
                  "constant": false,
                  "id": 28318,
                  "mutability": "mutable",
                  "name": "calls",
                  "nameLocation": "803:5:17",
                  "nodeType": "VariableDeclaration",
                  "scope": 28325,
                  "src": "781:27:17",
                  "stateVariable": false,
                  "storageLocation": "calldata",
                  "typeDescriptions": {
                    "typeIdentifier": "t_array$_t_struct$_Call3Value_$28286_calldata_ptr_$dyn_calldata_ptr",
                    "typeString": "struct IMulticall3.Call3Value[]"
                  },
                  "typeName": {
                    "baseType": {
                      "id": 28316,
                      "nodeType": "UserDefinedTypeName",
                      "pathNode": {
                        "id": 28315,
                        "name": "Call3Value",
                        "nodeType": "IdentifierPath",
                        "referencedDeclaration": 28286,
                        "src": "781:10:17"
                      },
                      "referencedDeclaration": 28286,
                      "src": "781:10:17",
                      "typeDescriptions": {
                        "typeIdentifier": "t_struct$_Call3Value_$28286_storage_ptr",
                        "typeString": "struct IMulticall3.Call3Value"
                      }
                    },
                    "id": 28317,
                    "nodeType": "ArrayTypeName",
                    "src": "781:12:17",
                    "typeDescriptions": {
                      "typeIdentifier": "t_array$_t_struct$_Call3Value_$28286_storage_$dyn_storage_ptr",
                      "typeString": "struct IMulticall3.Call3Value[]"
                    }
                  },
                  "visibility": "internal"
                }
              ],
              "src": "780:29:17"
            },
            "returnParameters": {
              "id": 28324,
              "nodeType": "ParameterList",
              "parameters": [
                {
                  "constant": false,
                  "id": 28323,
                  "mutability": "mutable",
                  "name": "returnData",
                  "nameLocation": "852:10:17",
                  "nodeType": "VariableDeclaration",
                  "scope": 28325,
                  "src": "836:26:17",
                  "stateVariable": false,
                  "storageLocation": "memory",
                  "typeDescriptions": {
                    "typeIdentifier": "t_array$_t_struct$_Result_$28291_memory_ptr_$dyn_memory_ptr",
                    "typeString": "struct IMulticall3.Result[]"
                  },
                  "typeName": {
                    "baseType": {
                      "id": 28321,
                      "nodeType": "UserDefinedTypeName",
                      "pathNode": {
                        "id": 28320,
                        "name": "Result",
                        "nodeType": "IdentifierPath",
                        "referencedDeclaration": 28291,
                        "src": "836:6:17"
                      },
                      "referencedDeclaration": 28291,
                      "src": "836:6:17",
                      "typeDescriptions": {
                        "typeIdentifier": "t_struct$_Result_$28291_storage_ptr",
                        "typeString": "struct IMulticall3.Result"
                      }
                    },
                    "id": 28322,
                    "nodeType": "ArrayTypeName",
                    "src": "836:8:17",
                    "typeDescriptions": {
                      "typeIdentifier": "t_array$_t_struct$_Result_$28291_storage_$dyn_storage_ptr",
                      "typeString": "struct IMulticall3.Result[]"
                    }
                  },
                  "visibility": "internal"
                }
              ],
              "src": "835:28:17"
            },
            "scope": 28425,
            "stateMutability": "payable",
            "virtual": false,
            "visibility": "external"
          },
          {
            "id": 28340,
            "nodeType": "FunctionDefinition",
            "src": "870:168:17",
            "nodes": [],
            "functionSelector": "c3077fa9",
            "implemented": false,
            "kind": "function",
            "modifiers": [],
            "name": "blockAndAggregate",
            "nameLocation": "879:17:17",
            "parameters": {
              "id": 28330,
              "nodeType": "ParameterList",
              "parameters": [
                {
                  "constant": false,
                  "id": 28329,
                  "mutability": "mutable",
                  "name": "calls",
                  "nameLocation": "913:5:17",
                  "nodeType": "VariableDeclaration",
                  "scope": 28340,
                  "src": "897:21:17",
                  "stateVariable": false,
                  "storageLocation": "calldata",
                  "typeDescriptions": {
                    "typeIdentifier": "t_array$_t_struct$_Call_$28270_calldata_ptr_$dyn_calldata_ptr",
                    "typeString": "struct IMulticall3.Call[]"
                  },
                  "typeName": {
                    "baseType": {
                      "id": 28327,
                      "nodeType": "UserDefinedTypeName",
                      "pathNode": {
                        "id": 28326,
                        "name": "Call",
                        "nodeType": "IdentifierPath",
                        "referencedDeclaration": 28270,
                        "src": "897:4:17"
                      },
                      "referencedDeclaration": 28270,
                      "src": "897:4:17",
                      "typeDescriptions": {
                        "typeIdentifier": "t_struct$_Call_$28270_storage_ptr",
                        "typeString": "struct IMulticall3.Call"
                      }
                    },
                    "id": 28328,
                    "nodeType": "ArrayTypeName",
                    "src": "897:6:17",
                    "typeDescriptions": {
                      "typeIdentifier": "t_array$_t_struct$_Call_$28270_storage_$dyn_storage_ptr",
                      "typeString": "struct IMulticall3.Call[]"
                    }
                  },
                  "visibility": "internal"
                }
              ],
              "src": "896:23:17"
            },
            "returnParameters": {
              "id": 28339,
              "nodeType": "ParameterList",
              "parameters": [
                {
                  "constant": false,
                  "id": 28332,
                  "mutability": "mutable",
                  "name": "blockNumber",
                  "nameLocation": "978:11:17",
                  "nodeType": "VariableDeclaration",
                  "scope": 28340,
                  "src": "970:19:17",
                  "stateVariable": false,
                  "storageLocation": "default",
                  "typeDescriptions": {
                    "typeIdentifier": "t_uint256",
                    "typeString": "uint256"
                  },
                  "typeName": {
                    "id": 28331,
                    "name": "uint256",
                    "nodeType": "ElementaryTypeName",
                    "src": "970:7:17",
                    "typeDescriptions": {
                      "typeIdentifier": "t_uint256",
                      "typeString": "uint256"
                    }
                  },
                  "visibility": "internal"
                },
                {
                  "constant": false,
                  "id": 28334,
                  "mutability": "mutable",
                  "name": "blockHash",
                  "nameLocation": "999:9:17",
                  "nodeType": "VariableDeclaration",
                  "scope": 28340,
                  "src": "991:17:17",
                  "stateVariable": false,
                  "storageLocation": "default",
                  "typeDescriptions": {
                    "typeIdentifier": "t_bytes32",
                    "typeString": "bytes32"
                  },
                  "typeName": {
                    "id": 28333,
                    "name": "bytes32",
                    "nodeType": "ElementaryTypeName",
                    "src": "991:7:17",
                    "typeDescriptions": {
                      "typeIdentifier": "t_bytes32",
                      "typeString": "bytes32"
                    }
                  },
                  "visibility": "internal"
                },
                {
                  "constant": false,
                  "id": 28338,
                  "mutability": "mutable",
                  "name": "returnData",
                  "nameLocation": "1026:10:17",
                  "nodeType": "VariableDeclaration",
                  "scope": 28340,
                  "src": "1010:26:17",
                  "stateVariable": false,
                  "storageLocation": "memory",
                  "typeDescriptions": {
                    "typeIdentifier": "t_array$_t_struct$_Result_$28291_memory_ptr_$dyn_memory_ptr",
                    "typeString": "struct IMulticall3.Result[]"
                  },
                  "typeName": {
                    "baseType": {
                      "id": 28336,
                      "nodeType": "UserDefinedTypeName",
                      "pathNode": {
                        "id": 28335,
                        "name": "Result",
                        "nodeType": "IdentifierPath",
                        "referencedDeclaration": 28291,
                        "src": "1010:6:17"
                      },
                      "referencedDeclaration": 28291,
                      "src": "1010:6:17",
                      "typeDescriptions": {
                        "typeIdentifier": "t_struct$_Result_$28291_storage_ptr",
                        "typeString": "struct IMulticall3.Result"
                      }
                    },
                    "id": 28337,
                    "nodeType": "ArrayTypeName",
                    "src": "1010:8:17",
                    "typeDescriptions": {
                      "typeIdentifier": "t_array$_t_struct$_Result_$28291_storage_$dyn_storage_ptr",
                      "typeString": "struct IMulticall3.Result[]"
                    }
                  },
                  "visibility": "internal"
                }
              ],
              "src": "969:68:17"
            },
            "scope": 28425,
            "stateMutability": "payable",
            "virtual": false,
            "visibility": "external"
          },
          {
            "id": 28345,
            "nodeType": "FunctionDefinition",
            "src": "1044:62:17",
            "nodes": [],
            "functionSelector": "3e64a696",
            "implemented": false,
            "kind": "function",
            "modifiers": [],
            "name": "getBasefee",
            "nameLocation": "1053:10:17",
            "parameters": {
              "id": 28341,
              "nodeType": "ParameterList",
              "parameters": [],
              "src": "1063:2:17"
            },
            "returnParameters": {
              "id": 28344,
              "nodeType": "ParameterList",
              "parameters": [
                {
                  "constant": false,
                  "id": 28343,
                  "mutability": "mutable",
                  "name": "basefee",
                  "nameLocation": "1097:7:17",
                  "nodeType": "VariableDeclaration",
                  "scope": 28345,
                  "src": "1089:15:17",
                  "stateVariable": false,
                  "storageLocation": "default",
                  "typeDescriptions": {
                    "typeIdentifier": "t_uint256",
                    "typeString": "uint256"
                  },
                  "typeName": {
                    "id": 28342,
                    "name": "uint256",
                    "nodeType": "ElementaryTypeName",
                    "src": "1089:7:17",
                    "typeDescriptions": {
                      "typeIdentifier": "t_uint256",
                      "typeString": "uint256"
                    }
                  },
                  "visibility": "internal"
                }
              ],
              "src": "1088:17:17"
            },
            "scope": 28425,
            "stateMutability": "view",
            "virtual": false,
            "visibility": "external"
          },
          {
            "id": 28352,
            "nodeType": "FunctionDefinition",
            "src": "1112:85:17",
            "nodes": [],
            "functionSelector": "ee82ac5e",
            "implemented": false,
            "kind": "function",
            "modifiers": [],
            "name": "getBlockHash",
            "nameLocation": "1121:12:17",
            "parameters": {
              "id": 28348,
              "nodeType": "ParameterList",
              "parameters": [
                {
                  "constant": false,
                  "id": 28347,
                  "mutability": "mutable",
                  "name": "blockNumber",
                  "nameLocation": "1142:11:17",
                  "nodeType": "VariableDeclaration",
                  "scope": 28352,
                  "src": "1134:19:17",
                  "stateVariable": false,
                  "storageLocation": "default",
                  "typeDescriptions": {
                    "typeIdentifier": "t_uint256",
                    "typeString": "uint256"
                  },
                  "typeName": {
                    "id": 28346,
                    "name": "uint256",
                    "nodeType": "ElementaryTypeName",
                    "src": "1134:7:17",
                    "typeDescriptions": {
                      "typeIdentifier": "t_uint256",
                      "typeString": "uint256"
                    }
                  },
                  "visibility": "internal"
                }
              ],
              "src": "1133:21:17"
            },
            "returnParameters": {
              "id": 28351,
              "nodeType": "ParameterList",
              "parameters": [
                {
                  "constant": false,
                  "id": 28350,
                  "mutability": "mutable",
                  "name": "blockHash",
                  "nameLocation": "1186:9:17",
                  "nodeType": "VariableDeclaration",
                  "scope": 28352,
                  "src": "1178:17:17",
                  "stateVariable": false,
                  "storageLocation": "default",
                  "typeDescriptions": {
                    "typeIdentifier": "t_bytes32",
                    "typeString": "bytes32"
                  },
                  "typeName": {
                    "id": 28349,
                    "name": "bytes32",
                    "nodeType": "ElementaryTypeName",
                    "src": "1178:7:17",
                    "typeDescriptions": {
                      "typeIdentifier": "t_bytes32",
                      "typeString": "bytes32"
                    }
                  },
                  "visibility": "internal"
                }
              ],
              "src": "1177:19:17"
            },
            "scope": 28425,
            "stateMutability": "view",
            "virtual": false,
            "visibility": "external"
          },
          {
            "id": 28357,
            "nodeType": "FunctionDefinition",
            "src": "1203:70:17",
            "nodes": [],
            "functionSelector": "42cbb15c",
            "implemented": false,
            "kind": "function",
            "modifiers": [],
            "name": "getBlockNumber",
            "nameLocation": "1212:14:17",
            "parameters": {
              "id": 28353,
              "nodeType": "ParameterList",
              "parameters": [],
              "src": "1226:2:17"
            },
            "returnParameters": {
              "id": 28356,
              "nodeType": "ParameterList",
              "parameters": [
                {
                  "constant": false,
                  "id": 28355,
                  "mutability": "mutable",
                  "name": "blockNumber",
                  "nameLocation": "1260:11:17",
                  "nodeType": "VariableDeclaration",
                  "scope": 28357,
                  "src": "1252:19:17",
                  "stateVariable": false,
                  "storageLocation": "default",
                  "typeDescriptions": {
                    "typeIdentifier": "t_uint256",
                    "typeString": "uint256"
                  },
                  "typeName": {
                    "id": 28354,
                    "name": "uint256",
                    "nodeType": "ElementaryTypeName",
                    "src": "1252:7:17",
                    "typeDescriptions": {
                      "typeIdentifier": "t_uint256",
                      "typeString": "uint256"
                    }
                  },
                  "visibility": "internal"
                }
              ],
              "src": "1251:21:17"
            },
            "scope": 28425,
            "stateMutability": "view",
            "virtual": false,
            "visibility": "external"
          },
          {
            "id": 28362,
            "nodeType": "FunctionDefinition",
            "src": "1279:62:17",
            "nodes": [],
            "functionSelector": "3408e470",
            "implemented": false,
            "kind": "function",
            "modifiers": [],
            "name": "getChainId",
            "nameLocation": "1288:10:17",
            "parameters": {
              "id": 28358,
              "nodeType": "ParameterList",
              "parameters": [],
              "src": "1298:2:17"
            },
            "returnParameters": {
              "id": 28361,
              "nodeType": "ParameterList",
              "parameters": [
                {
                  "constant": false,
                  "id": 28360,
                  "mutability": "mutable",
                  "name": "chainid",
                  "nameLocation": "1332:7:17",
                  "nodeType": "VariableDeclaration",
                  "scope": 28362,
                  "src": "1324:15:17",
                  "stateVariable": false,
                  "storageLocation": "default",
                  "typeDescriptions": {
                    "typeIdentifier": "t_uint256",
                    "typeString": "uint256"
                  },
                  "typeName": {
                    "id": 28359,
                    "name": "uint256",
                    "nodeType": "ElementaryTypeName",
                    "src": "1324:7:17",
                    "typeDescriptions": {
                      "typeIdentifier": "t_uint256",
                      "typeString": "uint256"
                    }
                  },
                  "visibility": "internal"
                }
              ],
              "src": "1323:17:17"
            },
            "scope": 28425,
            "stateMutability": "view",
            "virtual": false,
            "visibility": "external"
          },
          {
            "id": 28367,
            "nodeType": "FunctionDefinition",
            "src": "1347:76:17",
            "nodes": [],
            "functionSelector": "a8b0574e",
            "implemented": false,
            "kind": "function",
            "modifiers": [],
            "name": "getCurrentBlockCoinbase",
            "nameLocation": "1356:23:17",
            "parameters": {
              "id": 28363,
              "nodeType": "ParameterList",
              "parameters": [],
              "src": "1379:2:17"
            },
            "returnParameters": {
              "id": 28366,
              "nodeType": "ParameterList",
              "parameters": [
                {
                  "constant": false,
                  "id": 28365,
                  "mutability": "mutable",
                  "name": "coinbase",
                  "nameLocation": "1413:8:17",
                  "nodeType": "VariableDeclaration",
                  "scope": 28367,
                  "src": "1405:16:17",
                  "stateVariable": false,
                  "storageLocation": "default",
                  "typeDescriptions": {
                    "typeIdentifier": "t_address",
                    "typeString": "address"
                  },
                  "typeName": {
                    "id": 28364,
                    "name": "address",
                    "nodeType": "ElementaryTypeName",
                    "src": "1405:7:17",
                    "stateMutability": "nonpayable",
                    "typeDescriptions": {
                      "typeIdentifier": "t_address",
                      "typeString": "address"
                    }
                  },
                  "visibility": "internal"
                }
              ],
              "src": "1404:18:17"
            },
            "scope": 28425,
            "stateMutability": "view",
            "virtual": false,
            "visibility": "external"
          },
          {
            "id": 28372,
            "nodeType": "FunctionDefinition",
            "src": "1429:80:17",
            "nodes": [],
            "functionSelector": "72425d9d",
            "implemented": false,
            "kind": "function",
            "modifiers": [],
            "name": "getCurrentBlockDifficulty",
            "nameLocation": "1438:25:17",
            "parameters": {
              "id": 28368,
              "nodeType": "ParameterList",
              "parameters": [],
              "src": "1463:2:17"
            },
            "returnParameters": {
              "id": 28371,
              "nodeType": "ParameterList",
              "parameters": [
                {
                  "constant": false,
                  "id": 28370,
                  "mutability": "mutable",
                  "name": "difficulty",
                  "nameLocation": "1497:10:17",
                  "nodeType": "VariableDeclaration",
                  "scope": 28372,
                  "src": "1489:18:17",
                  "stateVariable": false,
                  "storageLocation": "default",
                  "typeDescriptions": {
                    "typeIdentifier": "t_uint256",
                    "typeString": "uint256"
                  },
                  "typeName": {
                    "id": 28369,
                    "name": "uint256",
                    "nodeType": "ElementaryTypeName",
                    "src": "1489:7:17",
                    "typeDescriptions": {
                      "typeIdentifier": "t_uint256",
                      "typeString": "uint256"
                    }
                  },
                  "visibility": "internal"
                }
              ],
              "src": "1488:20:17"
            },
            "scope": 28425,
            "stateMutability": "view",
            "virtual": false,
            "visibility": "external"
          },
          {
            "id": 28377,
            "nodeType": "FunctionDefinition",
            "src": "1515:76:17",
            "nodes": [],
            "functionSelector": "86d516e8",
            "implemented": false,
            "kind": "function",
            "modifiers": [],
            "name": "getCurrentBlockGasLimit",
            "nameLocation": "1524:23:17",
            "parameters": {
              "id": 28373,
              "nodeType": "ParameterList",
              "parameters": [],
              "src": "1547:2:17"
            },
            "returnParameters": {
              "id": 28376,
              "nodeType": "ParameterList",
              "parameters": [
                {
                  "constant": false,
                  "id": 28375,
                  "mutability": "mutable",
                  "name": "gaslimit",
                  "nameLocation": "1581:8:17",
                  "nodeType": "VariableDeclaration",
                  "scope": 28377,
                  "src": "1573:16:17",
                  "stateVariable": false,
                  "storageLocation": "default",
                  "typeDescriptions": {
                    "typeIdentifier": "t_uint256",
                    "typeString": "uint256"
                  },
                  "typeName": {
                    "id": 28374,
                    "name": "uint256",
                    "nodeType": "ElementaryTypeName",
                    "src": "1573:7:17",
                    "typeDescriptions": {
                      "typeIdentifier": "t_uint256",
                      "typeString": "uint256"
                    }
                  },
                  "visibility": "internal"
                }
              ],
              "src": "1572:18:17"
            },
            "scope": 28425,
            "stateMutability": "view",
            "virtual": false,
            "visibility": "external"
          },
          {
            "id": 28382,
            "nodeType": "FunctionDefinition",
            "src": "1597:78:17",
            "nodes": [],
            "functionSelector": "0f28c97d",
            "implemented": false,
            "kind": "function",
            "modifiers": [],
            "name": "getCurrentBlockTimestamp",
            "nameLocation": "1606:24:17",
            "parameters": {
              "id": 28378,
              "nodeType": "ParameterList",
              "parameters": [],
              "src": "1630:2:17"
            },
            "returnParameters": {
              "id": 28381,
              "nodeType": "ParameterList",
              "parameters": [
                {
                  "constant": false,
                  "id": 28380,
                  "mutability": "mutable",
                  "name": "timestamp",
                  "nameLocation": "1664:9:17",
                  "nodeType": "VariableDeclaration",
                  "scope": 28382,
                  "src": "1656:17:17",
                  "stateVariable": false,
                  "storageLocation": "default",
                  "typeDescriptions": {
                    "typeIdentifier": "t_uint256",
                    "typeString": "uint256"
                  },
                  "typeName": {
                    "id": 28379,
                    "name": "uint256",
                    "nodeType": "ElementaryTypeName",
                    "src": "1656:7:17",
                    "typeDescriptions": {
                      "typeIdentifier": "t_uint256",
                      "typeString": "uint256"
                    }
                  },
                  "visibility": "internal"
                }
              ],
              "src": "1655:19:17"
            },
            "scope": 28425,
            "stateMutability": "view",
            "virtual": false,
            "visibility": "external"
          },
          {
            "id": 28389,
            "nodeType": "FunctionDefinition",
            "src": "1681:77:17",
            "nodes": [],
            "functionSelector": "4d2301cc",
            "implemented": false,
            "kind": "function",
            "modifiers": [],
            "name": "getEthBalance",
            "nameLocation": "1690:13:17",
            "parameters": {
              "id": 28385,
              "nodeType": "ParameterList",
              "parameters": [
                {
                  "constant": false,
                  "id": 28384,
                  "mutability": "mutable",
                  "name": "addr",
                  "nameLocation": "1712:4:17",
                  "nodeType": "VariableDeclaration",
                  "scope": 28389,
                  "src": "1704:12:17",
                  "stateVariable": false,
                  "storageLocation": "default",
                  "typeDescriptions": {
                    "typeIdentifier": "t_address",
                    "typeString": "address"
                  },
                  "typeName": {
                    "id": 28383,
                    "name": "address",
                    "nodeType": "ElementaryTypeName",
                    "src": "1704:7:17",
                    "stateMutability": "nonpayable",
                    "typeDescriptions": {
                      "typeIdentifier": "t_address",
                      "typeString": "address"
                    }
                  },
                  "visibility": "internal"
                }
              ],
              "src": "1703:14:17"
            },
            "returnParameters": {
              "id": 28388,
              "nodeType": "ParameterList",
              "parameters": [
                {
                  "constant": false,
                  "id": 28387,
                  "mutability": "mutable",
                  "name": "balance",
                  "nameLocation": "1749:7:17",
                  "nodeType": "VariableDeclaration",
                  "scope": 28389,
                  "src": "1741:15:17",
                  "stateVariable": false,
                  "storageLocation": "default",
                  "typeDescriptions": {
                    "typeIdentifier": "t_uint256",
                    "typeString": "uint256"
                  },
                  "typeName": {
                    "id": 28386,
                    "name": "uint256",
                    "nodeType": "ElementaryTypeName",
                    "src": "1741:7:17",
                    "typeDescriptions": {
                      "typeIdentifier": "t_uint256",
                      "typeString": "uint256"
                    }
                  },
                  "visibility": "internal"
                }
              ],
              "src": "1740:17:17"
            },
            "scope": 28425,
            "stateMutability": "view",
            "virtual": false,
            "visibility": "external"
          },
          {
            "id": 28394,
            "nodeType": "FunctionDefinition",
            "src": "1764:70:17",
            "nodes": [],
            "functionSelector": "27e86d6e",
            "implemented": false,
            "kind": "function",
            "modifiers": [],
            "name": "getLastBlockHash",
            "nameLocation": "1773:16:17",
            "parameters": {
              "id": 28390,
              "nodeType": "ParameterList",
              "parameters": [],
              "src": "1789:2:17"
            },
            "returnParameters": {
              "id": 28393,
              "nodeType": "ParameterList",
              "parameters": [
                {
                  "constant": false,
                  "id": 28392,
                  "mutability": "mutable",
                  "name": "blockHash",
                  "nameLocation": "1823:9:17",
                  "nodeType": "VariableDeclaration",
                  "scope": 28394,
                  "src": "1815:17:17",
                  "stateVariable": false,
                  "storageLocation": "default",
                  "typeDescriptions": {
                    "typeIdentifier": "t_bytes32",
                    "typeString": "bytes32"
                  },
                  "typeName": {
                    "id": 28391,
                    "name": "bytes32",
                    "nodeType": "ElementaryTypeName",
                    "src": "1815:7:17",
                    "typeDescriptions": {
                      "typeIdentifier": "t_bytes32",
                      "typeString": "bytes32"
                    }
                  },
                  "visibility": "internal"
                }
              ],
              "src": "1814:19:17"
            },
            "scope": 28425,
            "stateMutability": "view",
            "virtual": false,
            "visibility": "external"
          },
          {
            "id": 28407,
            "nodeType": "FunctionDefinition",
            "src": "1840:144:17",
            "nodes": [],
            "functionSelector": "bce38bd7",
            "implemented": false,
            "kind": "function",
            "modifiers": [],
            "name": "tryAggregate",
            "nameLocation": "1849:12:17",
            "parameters": {
              "id": 28401,
              "nodeType": "ParameterList",
              "parameters": [
                {
                  "constant": false,
                  "id": 28396,
                  "mutability": "mutable",
                  "name": "requireSuccess",
                  "nameLocation": "1867:14:17",
                  "nodeType": "VariableDeclaration",
                  "scope": 28407,
                  "src": "1862:19:17",
                  "stateVariable": false,
                  "storageLocation": "default",
                  "typeDescriptions": {
                    "typeIdentifier": "t_bool",
                    "typeString": "bool"
                  },
                  "typeName": {
                    "id": 28395,
                    "name": "bool",
                    "nodeType": "ElementaryTypeName",
                    "src": "1862:4:17",
                    "typeDescriptions": {
                      "typeIdentifier": "t_bool",
                      "typeString": "bool"
                    }
                  },
                  "visibility": "internal"
                },
                {
                  "constant": false,
                  "id": 28400,
                  "mutability": "mutable",
                  "name": "calls",
                  "nameLocation": "1899:5:17",
                  "nodeType": "VariableDeclaration",
                  "scope": 28407,
                  "src": "1883:21:17",
                  "stateVariable": false,
                  "storageLocation": "calldata",
                  "typeDescriptions": {
                    "typeIdentifier": "t_array$_t_struct$_Call_$28270_calldata_ptr_$dyn_calldata_ptr",
                    "typeString": "struct IMulticall3.Call[]"
                  },
                  "typeName": {
                    "baseType": {
                      "id": 28398,
                      "nodeType": "UserDefinedTypeName",
                      "pathNode": {
                        "id": 28397,
                        "name": "Call",
                        "nodeType": "IdentifierPath",
                        "referencedDeclaration": 28270,
                        "src": "1883:4:17"
                      },
                      "referencedDeclaration": 28270,
                      "src": "1883:4:17",
                      "typeDescriptions": {
                        "typeIdentifier": "t_struct$_Call_$28270_storage_ptr",
                        "typeString": "struct IMulticall3.Call"
                      }
                    },
                    "id": 28399,
                    "nodeType": "ArrayTypeName",
                    "src": "1883:6:17",
                    "typeDescriptions": {
                      "typeIdentifier": "t_array$_t_struct$_Call_$28270_storage_$dyn_storage_ptr",
                      "typeString": "struct IMulticall3.Call[]"
                    }
                  },
                  "visibility": "internal"
                }
              ],
              "src": "1861:44:17"
            },
            "returnParameters": {
              "id": 28406,
              "nodeType": "ParameterList",
              "parameters": [
                {
                  "constant": false,
                  "id": 28405,
                  "mutability": "mutable",
                  "name": "returnData",
                  "nameLocation": "1972:10:17",
                  "nodeType": "VariableDeclaration",
                  "scope": 28407,
                  "src": "1956:26:17",
                  "stateVariable": false,
                  "storageLocation": "memory",
                  "typeDescriptions": {
                    "typeIdentifier": "t_array$_t_struct$_Result_$28291_memory_ptr_$dyn_memory_ptr",
                    "typeString": "struct IMulticall3.Result[]"
                  },
                  "typeName": {
                    "baseType": {
                      "id": 28403,
                      "nodeType": "UserDefinedTypeName",
                      "pathNode": {
                        "id": 28402,
                        "name": "Result",
                        "nodeType": "IdentifierPath",
                        "referencedDeclaration": 28291,
                        "src": "1956:6:17"
                      },
                      "referencedDeclaration": 28291,
                      "src": "1956:6:17",
                      "typeDescriptions": {
                        "typeIdentifier": "t_struct$_Result_$28291_storage_ptr",
                        "typeString": "struct IMulticall3.Result"
                      }
                    },
                    "id": 28404,
                    "nodeType": "ArrayTypeName",
                    "src": "1956:8:17",
                    "typeDescriptions": {
                      "typeIdentifier": "t_array$_t_struct$_Result_$28291_storage_$dyn_storage_ptr",
                      "typeString": "struct IMulticall3.Result[]"
                    }
                  },
                  "visibility": "internal"
                }
              ],
              "src": "1955:28:17"
            },
            "scope": 28425,
            "stateMutability": "payable",
            "virtual": false,
            "visibility": "external"
          },
          {
            "id": 28424,
            "nodeType": "FunctionDefinition",
            "src": "1990:192:17",
            "nodes": [],
            "functionSelector": "399542e9",
            "implemented": false,
            "kind": "function",
            "modifiers": [],
            "name": "tryBlockAndAggregate",
            "nameLocation": "1999:20:17",
            "parameters": {
              "id": 28414,
              "nodeType": "ParameterList",
              "parameters": [
                {
                  "constant": false,
                  "id": 28409,
                  "mutability": "mutable",
                  "name": "requireSuccess",
                  "nameLocation": "2025:14:17",
                  "nodeType": "VariableDeclaration",
                  "scope": 28424,
                  "src": "2020:19:17",
                  "stateVariable": false,
                  "storageLocation": "default",
                  "typeDescriptions": {
                    "typeIdentifier": "t_bool",
                    "typeString": "bool"
                  },
                  "typeName": {
                    "id": 28408,
                    "name": "bool",
                    "nodeType": "ElementaryTypeName",
                    "src": "2020:4:17",
                    "typeDescriptions": {
                      "typeIdentifier": "t_bool",
                      "typeString": "bool"
                    }
                  },
                  "visibility": "internal"
                },
                {
                  "constant": false,
                  "id": 28413,
                  "mutability": "mutable",
                  "name": "calls",
                  "nameLocation": "2057:5:17",
                  "nodeType": "VariableDeclaration",
                  "scope": 28424,
                  "src": "2041:21:17",
                  "stateVariable": false,
                  "storageLocation": "calldata",
                  "typeDescriptions": {
                    "typeIdentifier": "t_array$_t_struct$_Call_$28270_calldata_ptr_$dyn_calldata_ptr",
                    "typeString": "struct IMulticall3.Call[]"
                  },
                  "typeName": {
                    "baseType": {
                      "id": 28411,
                      "nodeType": "UserDefinedTypeName",
                      "pathNode": {
                        "id": 28410,
                        "name": "Call",
                        "nodeType": "IdentifierPath",
                        "referencedDeclaration": 28270,
                        "src": "2041:4:17"
                      },
                      "referencedDeclaration": 28270,
                      "src": "2041:4:17",
                      "typeDescriptions": {
                        "typeIdentifier": "t_struct$_Call_$28270_storage_ptr",
                        "typeString": "struct IMulticall3.Call"
                      }
                    },
                    "id": 28412,
                    "nodeType": "ArrayTypeName",
                    "src": "2041:6:17",
                    "typeDescriptions": {
                      "typeIdentifier": "t_array$_t_struct$_Call_$28270_storage_$dyn_storage_ptr",
                      "typeString": "struct IMulticall3.Call[]"
                    }
                  },
                  "visibility": "internal"
                }
              ],
              "src": "2019:44:17"
            },
            "returnParameters": {
              "id": 28423,
              "nodeType": "ParameterList",
              "parameters": [
                {
                  "constant": false,
                  "id": 28416,
                  "mutability": "mutable",
                  "name": "blockNumber",
                  "nameLocation": "2122:11:17",
                  "nodeType": "VariableDeclaration",
                  "scope": 28424,
                  "src": "2114:19:17",
                  "stateVariable": false,
                  "storageLocation": "default",
                  "typeDescriptions": {
                    "typeIdentifier": "t_uint256",
                    "typeString": "uint256"
                  },
                  "typeName": {
                    "id": 28415,
                    "name": "uint256",
                    "nodeType": "ElementaryTypeName",
                    "src": "2114:7:17",
                    "typeDescriptions": {
                      "typeIdentifier": "t_uint256",
                      "typeString": "uint256"
                    }
                  },
                  "visibility": "internal"
                },
                {
                  "constant": false,
                  "id": 28418,
                  "mutability": "mutable",
                  "name": "blockHash",
                  "nameLocation": "2143:9:17",
                  "nodeType": "VariableDeclaration",
                  "scope": 28424,
                  "src": "2135:17:17",
                  "stateVariable": false,
                  "storageLocation": "default",
                  "typeDescriptions": {
                    "typeIdentifier": "t_bytes32",
                    "typeString": "bytes32"
                  },
                  "typeName": {
                    "id": 28417,
                    "name": "bytes32",
                    "nodeType": "ElementaryTypeName",
                    "src": "2135:7:17",
                    "typeDescriptions": {
                      "typeIdentifier": "t_bytes32",
                      "typeString": "bytes32"
                    }
                  },
                  "visibility": "internal"
                },
                {
                  "constant": false,
                  "id": 28422,
                  "mutability": "mutable",
                  "name": "returnData",
                  "nameLocation": "2170:10:17",
                  "nodeType": "VariableDeclaration",
                  "scope": 28424,
                  "src": "2154:26:17",
                  "stateVariable": false,
                  "storageLocation": "memory",
                  "typeDescriptions": {
                    "typeIdentifier": "t_array$_t_struct$_Result_$28291_memory_ptr_$dyn_memory_ptr",
                    "typeString": "struct IMulticall3.Result[]"
                  },
                  "typeName": {
                    "baseType": {
                      "id": 28420,
                      "nodeType": "UserDefinedTypeName",
                      "pathNode": {
                        "id": 28419,
                        "name": "Result",
                        "nodeType": "IdentifierPath",
                        "referencedDeclaration": 28291,
                        "src": "2154:6:17"
                      },
                      "referencedDeclaration": 28291,
                      "src": "2154:6:17",
                      "typeDescriptions": {
                        "typeIdentifier": "t_struct$_Result_$28291_storage_ptr",
                        "typeString": "struct IMulticall3.Result"
                      }
                    },
                    "id": 28421,
                    "nodeType": "ArrayTypeName",
                    "src": "2154:8:17",
                    "typeDescriptions": {
                      "typeIdentifier": "t_array$_t_struct$_Result_$28291_storage_$dyn_storage_ptr",
                      "typeString": "struct IMulticall3.Result[]"
                    }
                  },
                  "visibility": "internal"
                }
              ],
              "src": "2113:68:17"
            },
            "scope": 28425,
            "stateMutability": "payable",
            "virtual": false,
            "visibility": "external"
          }
        ],
        "abstract": false,
        "baseContracts": [],
        "canonicalName": "IMulticall3",
        "contractDependencies": [],
        "contractKind": "interface",
        "fullyImplemented": false,
        "linearizedBaseContracts": [
          28425
        ],
        "name": "IMulticall3",
        "nameLocation": "110:11:17",
        "scope": 28426,
        "usedErrors": []
      }
    ],
    "license": "MIT"
  },
  "id": 17
}
"""


def test_contract_creation() -> None:
    contract = Contract('TestContract', json.loads(contract_json), foundry=True)
    assert len(contract.methods) == 16
    for method in contract.methods:
        if method.name == 'aggregate':
            assert method.sort == KSort('TestContractMethod')
            assert method.id == '252dba42'
            assert method.arg_types == ('tuple[]',)
            assert method.contract_name == 'TestContract'
            assert method.payable
