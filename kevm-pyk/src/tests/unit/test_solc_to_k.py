from __future__ import annotations

from typing import TYPE_CHECKING

import pytest
from pyk.kast.inner import KToken, KVariable

from kevm_pyk.kevm import KEVM
from kontrolx.solc_to_k import Contract, _range_predicate, find_function_calls

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


ESCAPE_DATA: list[tuple[str, str, str, str]] = [
    ('has_underscore', 'S2K', 'My_contract', 'S2KMyZUndcontract'),
    ('no_change', '', 'mycontract', 'mycontract'),
    ('starts_underscore', 'S2K', '_method', 'S2KZUndmethod'),
    ('with_escape', '', 'Z_', 'ZZZUnd'),
    ('lower_z', '', 'z_', 'zZUnd'),
    ('with_escape_no_prefix', 'S2K', 'zS2K_', 'S2KzS2KZUnd'),
    ('doll', 'S2K', '$name', 'S2KZDlrname'),
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


_ast: Final[dict] = {
    'id': 44657,
    'nodeType': 'FunctionDefinition',
    'src': '475:162:22',
    'nodes': [],
    'body': {
        'id': 44656,
        'nodeType': 'Block',
        'src': '529:108:22',
        'nodes': [],
        'statements': [
            {
                'expression': {
                    'arguments': [],
                    'expression': {
                        'argumentTypes': [],
                        'expression': {
                            'id': 44637,
                            'name': 'kevm',
                            'nodeType': 'Identifier',
                            'overloadedDeclarations': [],
                            'referencedDeclaration': 44573,
                            'src': '538:4:22',
                            'typeDescriptions': {
                                'typeIdentifier': 't_contract$_KEVMCheatsBase_$43504',
                                'typeString': 'contract KEVMCheatsBase',
                            },
                        },
                        'id': 44639,
                        'isConstant': False,
                        'isLValue': False,
                        'isPure': False,
                        'lValueRequested': False,
                        'memberLocation': '543:11:22',
                        'memberName': 'infiniteGas',
                        'nodeType': 'MemberAccess',
                        'referencedDeclaration': 43491,
                        'src': '538:16:22',
                        'typeDescriptions': {
                            'typeIdentifier': 't_function_external_nonpayable$__$returns$__$',
                            'typeString': 'function () external',
                        },
                    },
                    'id': 44640,
                    'isConstant': False,
                    'isLValue': False,
                    'isPure': False,
                    'kind': 'functionCall',
                    'lValueRequested': False,
                    'nameLocations': [],
                    'names': [],
                    'nodeType': 'FunctionCall',
                    'src': '538:18:22',
                    'tryCall': False,
                    'typeDescriptions': {'typeIdentifier': 't_tuple$__$', 'typeString': 'tuple()'},
                },
                'id': 44641,
                'nodeType': 'ExpressionStatement',
                'src': '538:18:22',
            },
            {
                'expression': {
                    'arguments': [
                        {
                            'id': 44645,
                            'name': 'x',
                            'nodeType': 'Identifier',
                            'overloadedDeclarations': [],
                            'referencedDeclaration': 44632,
                            'src': '583:1:22',
                            'typeDescriptions': {'typeIdentifier': 't_uint256', 'typeString': 'uint256'},
                        },
                        {
                            'id': 44646,
                            'name': 'inLuck',
                            'nodeType': 'Identifier',
                            'overloadedDeclarations': [],
                            'referencedDeclaration': 44634,
                            'src': '586:6:22',
                            'typeDescriptions': {'typeIdentifier': 't_bool', 'typeString': 'bool'},
                        },
                    ],
                    'expression': {
                        'argumentTypes': [
                            {'typeIdentifier': 't_uint256', 'typeString': 'uint256'},
                            {'typeIdentifier': 't_bool', 'typeString': 'bool'},
                        ],
                        'expression': {
                            'id': 44642,
                            'name': 'counter',
                            'nodeType': 'Identifier',
                            'overloadedDeclarations': [],
                            'referencedDeclaration': 44591,
                            'src': '565:7:22',
                            'typeDescriptions': {
                                'typeIdentifier': 't_contract$_Counter_$43417',
                                'typeString': 'contract Counter',
                            },
                        },
                        'id': 44644,
                        'isConstant': False,
                        'isLValue': False,
                        'isPure': False,
                        'lValueRequested': False,
                        'memberLocation': '573:9:22',
                        'memberName': 'setNumber',
                        'nodeType': 'MemberAccess',
                        'referencedDeclaration': 43409,
                        'src': '565:17:22',
                        'typeDescriptions': {
                            'typeIdentifier': 't_function_external_nonpayable$_t_uint256_$_t_bool_$returns$__$',
                            'typeString': 'function (uint256,bool) external',
                        },
                    },
                    'id': 44647,
                    'isConstant': False,
                    'isLValue': False,
                    'isPure': False,
                    'kind': 'functionCall',
                    'lValueRequested': False,
                    'nameLocations': [],
                    'names': [],
                    'nodeType': 'FunctionCall',
                    'src': '565:28:22',
                    'tryCall': False,
                    'typeDescriptions': {'typeIdentifier': 't_tuple$__$', 'typeString': 'tuple()'},
                },
                'id': 44648,
                'nodeType': 'ExpressionStatement',
                'src': '565:28:22',
            },
            {
                'expression': {
                    'arguments': [
                        {
                            'arguments': [],
                            'expression': {
                                'argumentTypes': [],
                                'expression': {
                                    'id': 44650,
                                    'name': 'counter',
                                    'nodeType': 'Identifier',
                                    'overloadedDeclarations': [],
                                    'referencedDeclaration': 44591,
                                    'src': '611:7:22',
                                    'typeDescriptions': {
                                        'typeIdentifier': 't_contract$_Counter_$43417',
                                        'typeString': 'contract Counter',
                                    },
                                },
                                'id': 44651,
                                'isConstant': False,
                                'isLValue': False,
                                'isPure': False,
                                'lValueRequested': False,
                                'memberLocation': '619:6:22',
                                'memberName': 'number',
                                'nodeType': 'MemberAccess',
                                'referencedDeclaration': 43385,
                                'src': '611:14:22',
                                'typeDescriptions': {
                                    'typeIdentifier': 't_function_external_view$__$returns$_t_uint256_$',
                                    'typeString': 'function () view external returns (uint256)',
                                },
                            },
                            'id': 44652,
                            'isConstant': False,
                            'isLValue': False,
                            'isPure': False,
                            'kind': 'functionCall',
                            'lValueRequested': False,
                            'nameLocations': [],
                            'names': [],
                            'nodeType': 'FunctionCall',
                            'src': '611:16:22',
                            'tryCall': False,
                            'typeDescriptions': {'typeIdentifier': 't_uint256', 'typeString': 'uint256'},
                        },
                        {
                            'id': 44653,
                            'name': 'x',
                            'nodeType': 'Identifier',
                            'overloadedDeclarations': [],
                            'referencedDeclaration': 44632,
                            'src': '629:1:22',
                            'typeDescriptions': {'typeIdentifier': 't_uint256', 'typeString': 'uint256'},
                        },
                    ],
                    'expression': {
                        'argumentTypes': [
                            {'typeIdentifier': 't_uint256', 'typeString': 'uint256'},
                            {'typeIdentifier': 't_uint256', 'typeString': 'uint256'},
                        ],
                        'id': 44649,
                        'name': 'assertEq',
                        'nodeType': 'Identifier',
                        'overloadedDeclarations': [
                            2524,
                            2549,
                            2562,
                            2578,
                            2620,
                            2662,
                            2704,
                            2741,
                            2778,
                            2815,
                            320,
                            345,
                            375,
                            400,
                            459,
                            484,
                            514,
                            539,
                            2012,
                            2047,
                        ],
                        'referencedDeclaration': 514,
                        'src': '602:8:22',
                        'typeDescriptions': {
                            'typeIdentifier': 't_function_internal_nonpayable$_t_uint256_$_t_uint256_$returns$__$',
                            'typeString': 'function (uint256,uint256)',
                        },
                    },
                    'id': 44654,
                    'isConstant': False,
                    'isLValue': False,
                    'isPure': False,
                    'kind': 'functionCall',
                    'lValueRequested': False,
                    'nameLocations': [],
                    'names': [],
                    'nodeType': 'FunctionCall',
                    'src': '602:29:22',
                    'tryCall': False,
                    'typeDescriptions': {'typeIdentifier': 't_tuple$__$', 'typeString': 'tuple()'},
                },
                'id': 44655,
                'nodeType': 'ExpressionStatement',
                'src': '602:29:22',
            },
        ],
    },
    'functionSelector': '36f15a92',
    'implemented': True,
    'kind': 'function',
    'modifiers': [],
    'name': 'testSetNumber',
    'nameLocation': '484:13:22',
    'parameters': {
        'id': 44635,
        'nodeType': 'ParameterList',
        'parameters': [
            {
                'constant': False,
                'id': 44632,
                'mutability': 'mutable',
                'name': 'x',
                'nameLocation': '506:1:22',
                'nodeType': 'VariableDeclaration',
                'scope': 44657,
                'src': '498:9:22',
                'stateVariable': False,
                'storageLocation': 'default',
                'typeDescriptions': {'typeIdentifier': 't_uint256', 'typeString': 'uint256'},
                'typeName': {
                    'id': 44631,
                    'name': 'uint256',
                    'nodeType': 'ElementaryTypeName',
                    'src': '498:7:22',
                    'typeDescriptions': {'typeIdentifier': 't_uint256', 'typeString': 'uint256'},
                },
                'visibility': 'internal',
            },
            {
                'constant': False,
                'id': 44634,
                'mutability': 'mutable',
                'name': 'inLuck',
                'nameLocation': '514:6:22',
                'nodeType': 'VariableDeclaration',
                'scope': 44657,
                'src': '509:11:22',
                'stateVariable': False,
                'storageLocation': 'default',
                'typeDescriptions': {'typeIdentifier': 't_bool', 'typeString': 'bool'},
                'typeName': {
                    'id': 44633,
                    'name': 'bool',
                    'nodeType': 'ElementaryTypeName',
                    'src': '509:4:22',
                    'typeDescriptions': {'typeIdentifier': 't_bool', 'typeString': 'bool'},
                },
                'visibility': 'internal',
            },
        ],
        'src': '497:24:22',
    },
    'returnParameters': {'id': 44636, 'nodeType': 'ParameterList', 'parameters': [], 'src': '529:0:22'},
    'scope': 44658,
    'stateMutability': 'nonpayable',
    'virtual': False,
    'visibility': 'public',
}


def test_find_in_dict() -> None:
    assert find_function_calls(_ast) == [
        ('KEVMCheatsBase', 'infiniteGas'),
        ('Counter', 'setNumber'),
        ('Counter', 'number'),
    ]
