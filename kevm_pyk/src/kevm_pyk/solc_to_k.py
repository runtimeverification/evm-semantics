import functools
import json
import subprocess
from pathlib import Path
from typing import Any, Dict

from pyk.cli_utils import fatal
from pyk.kast import (
    TRUE,
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
    KSequence,
    KSort,
    KTerminal,
    KToken,
    KVariable,
)
from pyk.kastManip import buildRule, substitute
from pyk.ktool import KPrint, paren
from pyk.prelude import intToken
from pyk.utils import intersperse

from .utils import (
    abstract_cell_vars,
    build_empty_configuration_cell,
    infGas,
    kevmAccountCell,
)


def solc_compile(contract_file: Path) -> Dict[str, Any]:
    subprocess_res = subprocess.run([
        'solc', '--combined-json', 'abi,bin-runtime,storage-layout,hashes', str(contract_file),
    ], capture_output=True)

    if subprocess_res.returncode != 0:
        fatal(f'solc error:\n{subprocess_res.stderr.decode()}')

    return json.loads(subprocess_res.stdout)


def gen_claims_for_contract(kevm: KPrint, contract_name: str) -> str:
    empty_config = build_empty_configuration_cell(kevm.definition, KSort('KevmCell'))
    program = KApply('binRuntime', [KApply('contract_' + contract_name)])
    account_cell = kevmAccountCell(KVariable('ACCT_ID'), KVariable('ACCT_BALANCE'), program, KVariable('ACCT_STORAGE'), KVariable('ACCT_ORIGSTORAGE'), KVariable('ACCT_NONCE'))
    init_subst = { 'MODE_CELL': KToken('NORMAL', 'Mode'),
                   'SCHEDULE_CELL': KApply('LONDON_EVM'),
                   'CALLSTACK_CELL': KApply('.List'),
                   'CALLDEPTH_CELL': intToken(0),
                   'PROGRAM_CELL': program,
                   'JUMPDESTS_CELL': KApply('#computeValidJumpDests', [program]),
                   'ORIGIN_CELL': KVariable('ORIGIN_ID'),
                   'ID_CELL': KVariable('ACCT_ID'),
                   'CALLER_CELL': KVariable('CALLER_ID'),
                   'LOCALMEM_CELL': KApply('.Memory_EVM-TYPES_Memory'),
                   'MEMORYUSED_CELL': intToken(0),
                   'WORDSTACK_CELL': KApply('.WordStack_EVM-TYPES_WordStack'),
                   'PC_CELL': intToken(0),
                   'GAS_CELL': infGas(KVariable('VGAS')),
                   'K_CELL': KSequence([KApply('#execute_EVM_KItem'), KVariable('CONTINUATION')]),
                   'ACCOUNTS_CELL': KApply('_AccountCellMap_', [account_cell, KVariable('ACCOUNTS')]),
                 }
    final_subst = {'K_CELL': KSequence([KApply('#halt_EVM_KItem'), KVariable('CONTINUATION')])}
    init_term = substitute(empty_config, init_subst)
    final_term = abstract_cell_vars(substitute(empty_config, final_subst))
    claim, _ = buildRule(contract_name.lower() + '-spec', init_term, final_term, claim=True)
    return [claim]


def gen_spec_modules(kompiled_directory: Path, spec_module_name: str) -> str:
    kevm = KPrint(str(kompiled_directory))
    kevm.symbolTable = kevmSymbolTable(kevm.symbolTable)
    production_labels = [prod.klabel for module in kevm.definition for prod in module.productions if prod.klabel is not None]
    contract_names = [prod_label[9:] for prod_label in production_labels if prod_label.startswith('contract_')]
    contract_function_labels = ['function_' + contract_name for contract_name in contract_names]
    top_level_rules = [rule for module in kevm.definition for rule in module.rules if type(rule.body) is KRewrite]
    contract_function_signatures = [rule.body.lhs for rule in top_level_rules if type(rule.body.lhs) is KApply and rule.body.lhs.label in contract_function_labels]
    modules = []
    for contract_name in contract_names:
        claims = gen_claims_for_contract(kevm, contract_name)
        spec_module = KFlatModule(contract_name.upper() + '-SPEC', claims, [KImport(kevm.definition.main_module_name)])
        modules.append(spec_module)
    spec_module = KFlatModule(spec_module_name, [], [KImport(module.name) for module in modules])
    spec_defn = KDefinition(spec_module_name, modules + [spec_module], [KRequire('verification.k')])
    return kevm.prettyPrint(spec_defn)


def solc_to_k(kompiled_directory: Path, contract_file: Path, contract_name: str, generate_storage: bool):
    kevm = KPrint(str(kompiled_directory))
    kevm.symbolTable = kevmSymbolTable(kevm.symbolTable)

    solc_json = solc_compile(contract_file)
    contract_json = solc_json['contracts'][f'{contract_file}:{contract_name}']
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

    contract_subsort = KProduction(KSort('Contract'), [KNonTerminal(contract_sort)])
    contract_production = KProduction(contract_sort, [KTerminal(contract_name)], att=KAtt({'klabel': f'contract_{contract_name}', 'symbol': ''}))
    contract_macro = KRule(KRewrite(KApply('binRuntime', [KApply(contract_name)]), _parseByteStack(_stringToken(bin_runtime))))

    binRuntimeModuleName = contract_name.upper() + '-BIN-RUNTIME'
    binRuntimeModule = KFlatModule(
        binRuntimeModuleName,
        [contract_subsort, contract_production] + storage_sentences + function_sentences + [contract_macro] + function_selector_alias_sentences,
        [KImport('BIN-RUNTIME', True)],
    )
    binRuntimeDefinition = KDefinition(binRuntimeModuleName, [binRuntimeModule], requires=[KRequire('edsl.md')])

    kevm.symbolTable['hashedLocation'] = lambda lang, base, offset: '#hashedLocation(' + lang + ', ' + base + ', ' + offset + ')'  # noqa
    kevm.symbolTable['abiCallData']    = lambda fname, *args: '#abiCallData(' + fname + "".join(", " + arg for arg in args) + ')'  # noqa
    kevm.symbolTable['address']        = _typed_arg_unparser('address')                                                            # noqa
    kevm.symbolTable['bool']           = _typed_arg_unparser('bool')                                                               # noqa
    kevm.symbolTable['bytes']          = _typed_arg_unparser('bytes')                                                              # noqa
    kevm.symbolTable['bytes4']         = _typed_arg_unparser('bytes4')                                                             # noqa
    kevm.symbolTable['bytes32']        = _typed_arg_unparser('bytes32')                                                            # noqa
    kevm.symbolTable['int256']         = _typed_arg_unparser('int256')                                                             # noqa
    kevm.symbolTable['uint256']        = _typed_arg_unparser('uint256')                                                            # noqa
    kevm.symbolTable['rangeAddress']   = lambda t: '#rangeAddress(' + t + ')'                                                      # noqa
    kevm.symbolTable['rangeBool']      = lambda t: '#rangeBool(' + t + ')'                                                         # noqa
    kevm.symbolTable['rangeBytes']     = lambda n, t: '#rangeBytes(' + n + ', ' + t + ')'                                          # noqa
    kevm.symbolTable['rangeUInt']      = lambda n, t: '#rangeUInt(' + n + ', ' + t + ')'                                           # noqa
    kevm.symbolTable['rangeSInt']      = lambda n, t: '#rangeSInt(' + n + ', ' + t + ')'                                           # noqa
    kevm.symbolTable['binRuntime']     = lambda s: '#binRuntime(' + s + ')'                                                        # noqa
    kevm.symbolTable[contract_name]    = lambda: contract_name                                                                     # noqa

    return kevm.prettyPrint(binRuntimeDefinition) + '\n'


# KEVM instantiation of pyk

def kevmSymbolTable(symbolTable):
    symbolTable['_orBool_']                                                  = paren(symbolTable['_orBool_'])                                      # noqa
    symbolTable['_andBool_']                                                 = paren(symbolTable['_andBool_'])                                     # noqa
    symbolTable['notBool_']                                                  = paren(symbolTable['notBool_'])                                      # noqa
    symbolTable['_/Int_']                                                    = paren(symbolTable['_/Int_'])                                        # noqa
    symbolTable['#Or']                                                       = paren(symbolTable['#Or'])                                           # noqa
    symbolTable['#And']                                                      = paren(symbolTable['#And'])                                          # noqa
    symbolTable['_Set_']                                                     = paren(symbolTable['_Set_'])                                         # noqa
    symbolTable['_|->_']                                                     = paren(symbolTable['_|->_'])                                         # noqa
    symbolTable['_Map_']                                                     = paren(lambda m1, m2: m1 + '\n' + m2)                                # noqa
    symbolTable['_AccountCellMap_']                                          = paren(lambda a1, a2: a1 + '\n' + a2)                                # noqa
    symbolTable['AccountCellMapItem']                                        = lambda k, v: v                                                      # noqa
    symbolTable['_[_:=_]_EVM-TYPES_Memory_Memory_Int_ByteArray']             = lambda m, k, v: m + ' [ '  + k + ' := (' + v + '):ByteArray ]'      # noqa
    symbolTable['_[_.._]_EVM-TYPES_ByteArray_ByteArray_Int_Int']             = lambda m, s, w: '(' + m + ' [ ' + s + ' .. ' + w + ' ]):ByteArray'  # noqa
    symbolTable['_<Word__EVM-TYPES_Int_Int_Int']                             = paren(lambda a1, a2: '(' + a1 + ') <Word ('  + a2 + ')')            # noqa
    symbolTable['_>Word__EVM-TYPES_Int_Int_Int']                             = paren(lambda a1, a2: '(' + a1 + ') >Word ('  + a2 + ')')            # noqa
    symbolTable['_<=Word__EVM-TYPES_Int_Int_Int']                            = paren(lambda a1, a2: '(' + a1 + ') <=Word (' + a2 + ')')            # noqa
    symbolTable['_>=Word__EVM-TYPES_Int_Int_Int']                            = paren(lambda a1, a2: '(' + a1 + ') >=Word (' + a2 + ')')            # noqa
    symbolTable['_==Word__EVM-TYPES_Int_Int_Int']                            = paren(lambda a1, a2: '(' + a1 + ') ==Word (' + a2 + ')')            # noqa
    symbolTable['_s<Word__EVM-TYPES_Int_Int_Int']                            = paren(lambda a1, a2: '(' + a1 + ') s<Word (' + a2 + ')')            # noqa
    symbolTable['EVMC_UNDEFINED_INSTRUCTION_NETWORK_ExceptionalStatusCode']  = lambda: 'EVMC_UNDEFINED_INSTRUCTION'                                # noqa
    symbolTable['EVMC_SUCCESS_NETWORK_EndStatusCode']                        = lambda: 'EVMC_SUCCESS'                                              # noqa
    symbolTable['EVMC_STATIC_MODE_VIOLATION_NETWORK_ExceptionalStatusCode']  = lambda: 'EVMC_STATIC_MODE_VIOLATION'                                # noqa
    symbolTable['EVMC_STACK_UNDERFLOW_NETWORK_ExceptionalStatusCode']        = lambda: 'EVMC_STACK_UNDERFLOW'                                      # noqa
    symbolTable['EVMC_STACK_OVERFLOW_NETWORK_ExceptionalStatusCode']         = lambda: 'EVMC_STACK_OVERFLOW'                                       # noqa
    symbolTable['EVMC_REVERT_NETWORK_EndStatusCode']                         = lambda: 'EVMC_REVERT'                                               # noqa
    symbolTable['EVMC_REJECTED_NETWORK_StatusCode']                          = lambda: 'EVMC_REJECTED'                                             # noqa
    symbolTable['EVMC_PRECOMPILE_FAILURE_NETWORK_ExceptionalStatusCode']     = lambda: 'EVMC_PRECOMPILE_FAILURE'                                   # noqa
    symbolTable['EVMC_OUT_OF_GAS_NETWORK_ExceptionalStatusCode']             = lambda: 'EVMC_OUT_OF_GAS'                                           # noqa
    symbolTable['EVMC_INVALID_MEMORY_ACCESS_NETWORK_ExceptionalStatusCode']  = lambda: 'EVMC_INVALID_MEMORY_ACCESS'                                # noqa
    symbolTable['EVMC_INVALID_INSTRUCTION_NETWORK_ExceptionalStatusCode']    = lambda: 'EVMC_INVALID_INSTRUCTION'                                  # noqa
    symbolTable['EVMC_INTERNAL_ERROR_NETWORK_StatusCode']                    = lambda: 'EVMC_INTERNAL_ERROR'                                       # noqa
    symbolTable['EVMC_FAILURE_NETWORK_ExceptionalStatusCode']                = lambda: 'EVMC_FAILURE'                                              # noqa
    symbolTable['EVMC_CALL_DEPTH_EXCEEDED_NETWORK_ExceptionalStatusCode']    = lambda: 'EVMC_CALL_DEPTH_EXCEEDED'                                  # noqa
    symbolTable['EVMC_BALANCE_UNDERFLOW_NETWORK_ExceptionalStatusCode']      = lambda: 'EVMC_BALANCE_UNDERFLOW'                                    # noqa
    symbolTable['EVMC_BAD_JUMP_DESTINATION_NETWORK_ExceptionalStatusCode']   = lambda: 'EVMC_BAD_JUMP_DESTINATION'                                 # noqa
    symbolTable['EVMC_ACCOUNT_ALREADY_EXISTS_NETWORK_ExceptionalStatusCode'] = lambda: 'EVMC_ACCOUNT_ALREADY_EXISTS'                               # noqa
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
                raise ValueError(f'Unsupported nonzero offset for variable: {member_label}')

            new_syntax = syntax + ([KTerminal('.')] if gen_dot else []) + [KTerminal(member_label)]
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
    function_call_data_production = KProduction(KSort('ByteArray'), [KNonTerminal(contract_sort), KTerminal('.'), KNonTerminal(function_sort)], att=KAtt({'klabel': f'function_{contract_name}', 'symbol': '', 'function': ''}))
    function_sentence_pairs = _extract_function_sentences(contract_name, function_sort, abi)

    if not function_sentence_pairs:
        return []

    function_productions, function_rules = map(list, zip(*function_sentence_pairs))
    return [function_call_data_production] + function_productions + function_rules


def generate_function_selector_alias_sentences(contract_name, contract_sort, hashes):
    abi_function_selector_production = KProduction(KSort('Int'), [KTerminal('selector'), KTerminal('('), KNonTerminal(KSort('String')), KTerminal(')')], att=KAtt({'klabel': 'abi_selector', 'alias': ''}))
    abi_function_selector_rules = []
    for h in hashes:
        f_name = h.split('(')[0]
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
        args = [KApply('abi_type_' + input_type, [KVariable(input_name)]) for input_name, input_type in zip(input_names, input_types)] or [KToken('.TypedArgs', 'TypedArgs')]
        return KApply('abiCallData', [_stringToken(name)] + args)

    def extract_ensures(input_names, input_types):
        opt_conjuncts = [_range_predicate(KVariable(input_name), input_type) for input_name, input_type in zip(input_names, input_types)]
        conjuncts = [opt_conjunct for opt_conjunct in opt_conjuncts if opt_conjunct is not None]
        if len(conjuncts) == 0:
            return TRUE

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
    return KApply('#parseByteStack(_)_SERIALIZATION_ByteArray_String', [s])  # type: ignore


def _stringToken(s: str):
    return KToken('"' + s + '"', 'String')


def _intToken(s: str):
    return KToken(s, 'Int')


def _typed_arg_unparser(type_label: str):
    return lambda x: '#' + type_label + '(' + x + ')'


def _check_supported_value_type(type_label: str) -> None:
    supported_value_types = {'address', 'bool', 'bytes32', 'uint8', 'int256', 'string', 'uint256'}
    if type_label not in supported_value_types and not type_label.startswith('contract '):
        raise ValueError(f'Unsupported value type: {type_label}')


def _check_supported_key_type(type_label: str) -> None:
    supported_key_types = {'address', 'bytes32', 'int256', 'uint256'}
    if type_label not in supported_key_types:
        raise ValueError(f'Unsupported key type: {type_label}')


def _evm_base_sort(type_label: str):
    if type_label in {'address', 'bool', 'bytes4', 'bytes32', 'int256', 'uint256', 'uint8'}:
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
    if type_label == 'uint8':
        return KApply('rangeUInt', [_intToken('8'), term])
    if type_label == 'bytes':
        return None

    raise ValueError(f'Range predicate unknown for: {type_label}')
