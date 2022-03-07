import functools
import json

from pyk.kast import (
    KApply,
    KAtt,
    KDefinition,
    KFlatModule,
    KImport,
    KNonTerminal,
    KProduction,
    KRequire,
    KRewrite,
    KRule,
    KSort,
    KTerminal,
    KToken,
    KVariable,
    paren,
)
from pyk.ktool import KPrint

from .utils import intersperse


def solc_to_k(*, command: str, kompiled_directory: str, contract_file: str, contract_name: str, solc_output, generate_storage: bool):
    assert command == 'solc-to-k'
    kevm = KPrint(kompiled_directory)
    kevm.symbolTable = kevmSymbolTable(kevm.symbolTable)

    contract_json = json.loads(solc_output.read())['contracts'][contract_file + ':' + contract_name]
    storage_layout = contract_json['storage-layout']
    abi = contract_json['abi']
    hashes = contract_json['hashes']
    bin_runtime = '0x' + contract_json['bin-runtime']

    # TODO: add check to kevm:
    # solc version should be >=0.8.0 due to:
    # https://github.com/ethereum/solidity/issues/10276

    contract_sort = KSort(f'{contract_name}Contract')

    storage_sentences = generate_storage_sentences(contract_name, contract_sort, storage_layout) if generate_storage else []
    function_sentences = generate_function_sentences(contract_name, contract_sort, abi)
    function_selector_alias_sentences = generate_function_selector_alias_sentences(contract_name, contract_sort, hashes)

    binRuntimeProduction = KProduction(KSort('ByteArray'), [KTerminal('#binRuntime'), KTerminal('('), KNonTerminal(contract_sort), KTerminal(')')], att=KAtt({'klabel': 'binRuntime', 'alias': ''}))

    contractProduction = KProduction(contract_sort, [KTerminal(contract_name)], att=KAtt({'klabel': f'contract_{contract_name}'}))
    contractMacro = KRule(KRewrite(KApply('binRuntime', [KApply(contract_name)]), _parseByteStack(_stringToken(bin_runtime))))

    binRuntimeModuleName = contract_name.upper() + '-BIN-RUNTIME'
    binRuntimeModule = KFlatModule( binRuntimeModuleName 
                                  ,   [contractProduction]
                                    + storage_sentences
                                    + function_sentences
                                    + [binRuntimeProduction, contractMacro]
                                    + function_selector_alias_sentences
                                  , [KImport('EDSL', True)]
                                  )
    binRuntimeDefinition = KDefinition(binRuntimeModuleName, [binRuntimeModule], requires=[KRequire('edsl.md')])

    kevm.symbolTable['hashedLocation'] = lambda lang, base, offset: '#hashedLocation(' + lang + ', ' + base + ', ' + offset + ')'
    kevm.symbolTable['abiCallData']    = lambda fname, *args: '#abiCallData(' + fname + "".join(", " + arg for arg in args) + ')'
    kevm.symbolTable['address']        = _typed_arg_unparser('address')
    kevm.symbolTable['bool']           = _typed_arg_unparser('bool')
    kevm.symbolTable['bytes']          = _typed_arg_unparser('bytes')
    kevm.symbolTable['bytes4']         = _typed_arg_unparser('bytes4')
    kevm.symbolTable['bytes32']        = _typed_arg_unparser('bytes32')
    kevm.symbolTable['int256']         = _typed_arg_unparser('int256')
    kevm.symbolTable['uint256']        = _typed_arg_unparser('uint256')
    kevm.symbolTable['rangeAddress']   = lambda t: '#rangeAddress(' + t + ')'
    kevm.symbolTable['rangeBool']      = lambda t: '#rangeBool(' + t + ')'
    kevm.symbolTable['rangeBytes']     = lambda n, t: '#rangeBytes(' + n + ', ' + t + ')'
    kevm.symbolTable['rangeUInt']      = lambda n, t: '#rangeUInt(' + n + ', ' + t + ')'
    kevm.symbolTable['rangeSInt']      = lambda n, t: '#rangeSInt(' + n + ', ' + t + ')'
    kevm.symbolTable['binRuntime']     = lambda s: '#binRuntime(' + s + ')'
    kevm.symbolTable[contract_name]    = lambda: contract_name

    return kevm.prettyPrint(binRuntimeDefinition) + '\n'


# KEVM instantiation of pyk

def kevmSymbolTable(symbolTable):
    symbolTable['_orBool_']                                                  = paren(symbolTable['_orBool_'])
    symbolTable['_andBool_']                                                 = paren(symbolTable['_andBool_'])
    symbolTable['notBool_']                                                  = paren(symbolTable['notBool_'])
    symbolTable['_/Int_']                                                    = paren(symbolTable['_/Int_'])
    symbolTable['#Or']                                                       = paren(symbolTable['#Or'])
    symbolTable['#And']                                                      = paren(symbolTable['#And'])
    symbolTable['_Set_']                                                     = paren(symbolTable['_Set_'])
    symbolTable['_|->_']                                                     = paren(symbolTable['_|->_'])
    symbolTable['_Map_']                                                     = paren(lambda m1, m2: m1 + '\n' + m2)
    symbolTable['_AccountCellMap_']                                          = paren(lambda a1, a2: a1 + '\n' + a2)
    symbolTable['AccountCellMapItem']                                        = lambda k, v: v
    symbolTable['_[_:=_]_EVM-TYPES_Memory_Memory_Int_ByteArray']             = lambda m, k, v: m + ' [ '  + k + ' := (' + v + '):ByteArray ]'
    symbolTable['_[_.._]_EVM-TYPES_ByteArray_ByteArray_Int_Int']             = lambda m, s, w: '(' + m + ' [ ' + s + ' .. ' + w + ' ]):ByteArray'
    symbolTable['_<Word__EVM-TYPES_Int_Int_Int']                             = paren(lambda a1, a2: '(' + a1 + ') <Word ('  + a2 + ')')
    symbolTable['_>Word__EVM-TYPES_Int_Int_Int']                             = paren(lambda a1, a2: '(' + a1 + ') >Word ('  + a2 + ')')
    symbolTable['_<=Word__EVM-TYPES_Int_Int_Int']                            = paren(lambda a1, a2: '(' + a1 + ') <=Word (' + a2 + ')')
    symbolTable['_>=Word__EVM-TYPES_Int_Int_Int']                            = paren(lambda a1, a2: '(' + a1 + ') >=Word (' + a2 + ')')
    symbolTable['_==Word__EVM-TYPES_Int_Int_Int']                            = paren(lambda a1, a2: '(' + a1 + ') ==Word (' + a2 + ')')
    symbolTable['_s<Word__EVM-TYPES_Int_Int_Int']                            = paren(lambda a1, a2: '(' + a1 + ') s<Word (' + a2 + ')')
    symbolTable['EVMC_UNDEFINED_INSTRUCTION_NETWORK_ExceptionalStatusCode']  = lambda: 'EVMC_UNDEFINED_INSTRUCTION'
    symbolTable['EVMC_SUCCESS_NETWORK_EndStatusCode']                        = lambda: 'EVMC_SUCCESS'
    symbolTable['EVMC_STATIC_MODE_VIOLATION_NETWORK_ExceptionalStatusCode']  = lambda: 'EVMC_STATIC_MODE_VIOLATION'
    symbolTable['EVMC_STACK_UNDERFLOW_NETWORK_ExceptionalStatusCode']        = lambda: 'EVMC_STACK_UNDERFLOW'
    symbolTable['EVMC_STACK_OVERFLOW_NETWORK_ExceptionalStatusCode']         = lambda: 'EVMC_STACK_OVERFLOW'
    symbolTable['EVMC_REVERT_NETWORK_EndStatusCode']                         = lambda: 'EVMC_REVERT'
    symbolTable['EVMC_REJECTED_NETWORK_StatusCode']                          = lambda: 'EVMC_REJECTED'
    symbolTable['EVMC_PRECOMPILE_FAILURE_NETWORK_ExceptionalStatusCode']     = lambda: 'EVMC_PRECOMPILE_FAILURE'
    symbolTable['EVMC_OUT_OF_GAS_NETWORK_ExceptionalStatusCode']             = lambda: 'EVMC_OUT_OF_GAS'
    symbolTable['EVMC_INVALID_MEMORY_ACCESS_NETWORK_ExceptionalStatusCode']  = lambda: 'EVMC_INVALID_MEMORY_ACCESS'
    symbolTable['EVMC_INVALID_INSTRUCTION_NETWORK_ExceptionalStatusCode']    = lambda: 'EVMC_INVALID_INSTRUCTION'
    symbolTable['EVMC_INTERNAL_ERROR_NETWORK_StatusCode']                    = lambda: 'EVMC_INTERNAL_ERROR'
    symbolTable['EVMC_FAILURE_NETWORK_ExceptionalStatusCode']                = lambda: 'EVMC_FAILURE'
    symbolTable['EVMC_CALL_DEPTH_EXCEEDED_NETWORK_ExceptionalStatusCode']    = lambda: 'EVMC_CALL_DEPTH_EXCEEDED'
    symbolTable['EVMC_BALANCE_UNDERFLOW_NETWORK_ExceptionalStatusCode']      = lambda: 'EVMC_BALANCE_UNDERFLOW'
    symbolTable['EVMC_BAD_JUMP_DESTINATION_NETWORK_ExceptionalStatusCode']   = lambda: 'EVMC_BAD_JUMP_DESTINATION'
    symbolTable['EVMC_ACCOUNT_ALREADY_EXISTS_NETWORK_ExceptionalStatusCode'] = lambda: 'EVMC_ACCOUNT_ALREADY_EXISTS'
    return symbolTable


# Helpers

def generate_storage_sentences(contract_name, contract_sort, storage_layout):
    storage_sort = KSort(f'{contract_name}Storage')
    storage_sentence_pairs = _extract_storage_sentences(contract_name, storage_sort, storage_layout)

    if not storage_sentence_pairs:
        return []

    storage_productions, storage_rules = map(list, zip(*storage_sentence_pairs))
    storage_location_production = KProduction(KSort('Int'), [KNonTerminal(contract_sort), KTerminal('.'), KNonTerminal(storage_sort)], att=KAtt({'klabel': f'storage_{contract_name}', 'alias': ''}))
    return storage_productions + [storage_location_production] + storage_rules


def _extract_storage_sentences(contract_name, storage_sort, storage_layout):
    types = storage_layout.get('types', [])  # 'types' is missing from storage_layout if storage_layout['storage'] == []

    def recur(syntax, lhs, rhs, var_idx, type_name):
        type_dict = types[type_name]
        encoding = type_dict['encoding']

        if encoding == 'inplace':
            members = type_dict.get('members')
            if members:
                return recur_struct(syntax, lhs, rhs, var_idx, members)

            type_label = type_dict['label']
            return recur_value(syntax, lhs, rhs, type_label)

        if encoding == 'mapping':
            key_type_name = type_dict['key']
            value_type_name = type_dict['value']
            return recur_mapping(syntax, lhs, rhs, var_idx, key_type_name, value_type_name)

        if encoding == 'bytes':
            type_label = type_dict['label']
            assert type_label in {'bytes', 'string'}
            return recur_value(syntax, lhs, rhs, type_label)

        raise ValueError(f'Unsupported encoding: {encoding}')

    def recur_value(syntax, lhs, rhs, type_label):
        _check_supported_value_type(type_label)

        # TODO: add structure to LHS:
        # generate (uncurried) unparser, function name, and list of arguments

        # TODO: simplify RHS:
        # #hashedLocation(L, #hashedLocation(L, B, X), Y) => #hashedLocation(L, B, X Y)
        # 0 +Int X => X
        # X +Int 0 => X
        return [(KProduction(storage_sort, syntax),
                 KRule(KRewrite(KToken(lhs, None), rhs)))]

    def recur_struct(syntax, lhs, rhs, var_idx, members, gen_dot=True):
        res = []
        for member in members:
            member_label = member['label']
            member_slot = member['slot']
            member_offset = member['offset']
            member_type_name = member['type']

            if member_offset != 0:
                raise ValueError(f'Unsupported nonzero offset for variable: {label}')

            new_syntax = syntax + [KTerminal(f'{"." if gen_dot else ""}{member_label}')]
            new_lhs = f'{lhs}.{member_label}'
            new_rhs = KApply('_+Int_', [rhs, _intToken(member_slot)])
            res += recur(new_syntax, new_lhs, new_rhs, var_idx, member_type_name)
        return res

    def recur_mapping(syntax, lhs, rhs, var_idx, key_type_name, value_type_name):
        key_type_dict = types[key_type_name]
        key_type_label = key_type_dict['label']

        _check_supported_key_type(key_type_label)
        key_sort = _evm_base_sort(key_type_label)

        new_syntax = syntax + [KTerminal('['), KNonTerminal(key_sort), KTerminal(']')]
        new_lhs = f'{lhs}[V{var_idx}]'
        new_rhs = KApply('hashedLocation', [_stringToken('Solidity'), rhs, KVariable(f'V{var_idx}')])
        new_type_name = value_type_name
        return recur(new_syntax, new_lhs, new_rhs, var_idx + 1, new_type_name)

    storage = storage_layout['storage']
    return recur_struct([], f'{contract_name}', _intToken('0'), 0, storage, gen_dot=False)


def generate_function_sentences(contract_name, contract_sort, abi):
    function_sort = KSort(f'{contract_name}Function')
    function_call_data_production = KProduction(KSort('ByteArray'), [KNonTerminal(contract_sort), KTerminal('.'), KNonTerminal(function_sort)], att=KAtt({'klabel': f'function_{contract_name}', 'function': ''}))
    function_sentence_pairs = _extract_function_sentences(contract_name, function_sort, abi)

    if not function_sentence_pairs:
        return []

    function_productions, function_rules = map(list, zip(*function_sentence_pairs))
    return [function_call_data_production] + function_productions + function_rules


def generate_function_selector_alias_sentences(contract_name, contract_sort, hashes):
    abi_function_selector_production = KProduction(KSort('Int'), [KTerminal('selector'), KTerminal('('), KNonTerminal(KSort('String')), KTerminal(')')], att=KAtt({'klabel': 'abi_selector', 'alias': ''}))
    abi_function_selector_rules = []
    for h in hashes:
        f_name   = h.split('(')[0]
        hash_int = int(hashes[h], 16)
        abi_function_selector_rewrite = KRewrite(KToken(f'selector("{f_name}")', 'Int'), KToken(str(hash_int), 'Int'))
        abi_function_selector_rules.append(KRule(abi_function_selector_rewrite))
    return [abi_function_selector_production] + abi_function_selector_rules


def _extract_function_sentences(contract_name, function_sort, abi):
    def extract_production(name, inputs):
        input_types = [input_dict['type'] for input_dict in inputs]

        items = []
        items.append(KTerminal(name))
        items.append(KTerminal('('))

        input_nonterminals = (KNonTerminal(_evm_base_sort(input_type)) for input_type in input_types)
        items += intersperse(input_nonterminals, KTerminal(','))

        items.append(KTerminal(')'))
        return KProduction(function_sort, items)

    def extract_rule(name, inputs):
        input_names = normalize_input_names([input_dict['name'] for input_dict in inputs])
        input_types = [input_dict['type'] for input_dict in inputs]
        lhs = extract_lhs(name, input_names)
        rhs = extract_rhs(name, input_names, input_types)
        ensures = extract_ensures(input_names, input_types)
        return KRule(KRewrite(lhs, rhs), ensures=ensures)

    def extract_lhs(name, input_names):
        # TODO: add structure to LHS:
        # generate (uncurried) unparser, function name, and list of arguments
        return KToken(f'{contract_name}.{name}(' + ', '.join(input_names) + ')', 'ByteArray')

    def extract_rhs(name, input_names, input_types):
        args = [KApply(input_type, [KVariable(input_name)]) for input_name, input_type in zip(input_names, input_types)] or [KToken('.TypedArgs', 'TypedArgs')]
        return KApply('abiCallData', [_stringToken(name)] + args)

    def extract_ensures(input_names, input_types):
        opt_conjuncts = [_range_predicate(KVariable(input_name), input_type) for input_name, input_type in zip(input_names, input_types)]
        conjuncts = [opt_conjunct for opt_conjunct in opt_conjuncts if opt_conjunct is not None]
        if len(conjuncts) == 0:
            return None

        return functools.reduce(lambda x, y: KApply('_andBool_', [x, y]), conjuncts)

    def normalize_input_names(input_names):
        if not input_names:
            return []

        head, *_ = input_names

        if head == '':
            assert all(input_name == '' for input_name in input_names)
            return [f'V{i}' for i, _ in enumerate(input_names)]

        assert all(input_name != '' for input_name in input_names)

        res = [input_dict['name'].lstrip('_').upper() for input_dict in inputs]
        if len(res) != len(set(res)):
            raise RuntimeError(f"Some arguments only differ in capitalization or a '_' prefix for: {name}")
        return res

    res = []
    for func_dict in abi:
        if func_dict['type'] != 'function':
            continue

        name = func_dict['name']
        inputs = func_dict['inputs']
        res.append((extract_production(name, inputs), extract_rule(name, inputs)))
    return res


def _parseByteStack(s: str):
    return KApply('#parseByteStack(_)_SERIALIZATION_ByteArray_String', [s])


def _stringToken(s: str):
    return KToken('"' + s + '"', 'String')


def _intToken(s: str):
    return KToken(s, 'Int')


def _typed_arg_unparser(type_label: str):
    return lambda x: '#' + type_label + '(' + x + ')'


def _check_supported_value_type(type_label: str) -> None:
    supported_value_types = {'address', 'bool', 'bytes32', 'uint8', 'int256', 'string', 'uint256'}
    if type_label not in supported_value_types:
        raise ValueError(f'Unsupported value type: {type_label}')


def _check_supported_key_type(type_label: str) -> None:
    supported_key_types = {'address', 'bytes32', 'int256', 'uint256'}
    if type_label not in supported_key_types:
        raise ValueError(f'Unsupported key type: {type_label}')


def _evm_base_sort(type_label: str):
    if type_label in {'address', 'bool', 'bytes4', 'bytes32', 'int256', 'uint256'}:
        return KSort('Int')

    if type_label == 'bytes':
        return KSort('ByteArray')

    raise ValueError(f'EVM base sort unknown for: {type_label}')


def _range_predicate(term, type_label: str):
    if type_label == 'address':
        return KApply('rangeAddress', [term])
    if type_label == 'bool':
        return KApply('rangeBool', [term])
    if type_label == 'bytes4':
        return KApply('rangeBytes', [_intToken('4'), term])
    if type_label in {'bytes32', 'uint256'}:
        return KApply('rangeUInt', [_intToken('256'), term])
    if type_label == 'int256':
        return KApply('rangeSInt', [_intToken('256'), term])
    if type_label == 'bytes':
        return None

    raise ValueError(f'Range predicate unknown for: {type_label}')
