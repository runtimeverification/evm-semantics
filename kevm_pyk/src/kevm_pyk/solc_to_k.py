import functools
import json
import logging
from pathlib import Path
from subprocess import CalledProcessError
from typing import Any, Dict, Final, List, Tuple

from pyk.cli_utils import run_process
from pyk.kast import (
    TRUE,
    KApply,
    KAtt,
    KClaim,
    KDefinition,
    KFlatModule,
    KImport,
    KInner,
    KLabel,
    KNonTerminal,
    KProduction,
    KRequire,
    KRewrite,
    KRule,
    KSentence,
    KSequence,
    KSort,
    KTerminal,
    KToken,
    KVariable,
)
from pyk.kastManip import buildRule, substitute
from pyk.prelude import Sorts, intToken, stringToken
from pyk.utils import intersperse

from .kevm import KEVM
from .utils import KDefinition_empty_config, abstract_cell_vars

_LOGGER: Final = logging.getLogger(__name__)


def solc_compile(contract_file: Path) -> Dict[str, Any]:

    # TODO: add check to kevm:
    # solc version should be >=0.8.0 due to:
    # https://github.com/ethereum/solidity/issues/10276

    args = {
        'language': 'Solidity',
        'sources': {
            contract_file.name: {
                'urls': [
                    str(contract_file),
                ],
            },
        },
        'settings': {
            'outputSelection': {
                '*': {
                    '*': [
                        'abi',
                        'storageLayout',
                        'evm.methodIdentifiers',
                        'evm.deployedBytecode.object',
                    ],
                },
            },
        },
    }

    try:
        process_res = run_process(['solc', '--standard-json'], _LOGGER, input=json.dumps(args))
    except CalledProcessError as err:
        raise RuntimeError('solc error', err.stdout, err.stderr)

    return json.loads(process_res.stdout)


def gen_claims_for_contract(empty_config: KInner, contract_name: str) -> List[KClaim]:
    program = KApply('binRuntime', [KApply('contract_' + contract_name)])
    account_cell = KEVM.account_cell(KVariable('ACCT_ID'), KVariable('ACCT_BALANCE'), program, KVariable('ACCT_STORAGE'), KVariable('ACCT_ORIGSTORAGE'), KVariable('ACCT_NONCE'))
    init_subst = {
        'MODE_CELL': KToken('NORMAL', 'Mode'),
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
        'GAS_CELL': KEVM.inf_gas(KVariable('VGAS')),
        'K_CELL': KSequence([KApply('#execute_EVM_KItem'), KVariable('CONTINUATION')]),
        'ACCOUNTS_CELL': KApply('_AccountCellMap_', [account_cell, KVariable('ACCOUNTS')]),
    }
    final_subst = {'K_CELL': KSequence([KApply('#halt_EVM_KItem'), KVariable('CONTINUATION')])}
    init_term = substitute(empty_config, init_subst)
    final_term = abstract_cell_vars(substitute(empty_config, final_subst))
    claim, _ = buildRule(contract_name.lower(), init_term, final_term, claim=True)
    assert isinstance(claim, KClaim)
    return [claim]


def gen_spec_modules(kevm: KEVM, spec_module_name: str) -> str:
    production_labels = [prod.klabel for module in kevm.definition for prod in module.productions if prod.klabel is not None]
    contract_names = [prod_label.name[9:] for prod_label in production_labels if prod_label.name.startswith('contract_')]
    empty_config = KDefinition_empty_config(kevm.definition, Sorts.GENERATED_TOP_CELL)
    claims = [claim for name in contract_names for claim in gen_claims_for_contract(empty_config, name)]
    spec_module = KFlatModule(spec_module_name, claims, [KImport(kevm.definition.main_module_name)])
    spec_defn = KDefinition(spec_module_name, [spec_module], [KRequire('verification.k')])
    return kevm.pretty_print(spec_defn)


def contract_to_k(contract_json: Dict, contract_name: str, generate_storage: bool, empty_config: KInner, foundry: bool = False) -> KFlatModule:

    abi = contract_json['abi']
    hashes = contract_json['evm']['methodIdentifiers'] if not foundry else contract_json['methodIdentifiers']
    bin_runtime = '0x' + (contract_json['evm']['deployedBytecode']['object'] if not foundry else contract_json['deployedBytecode']['object'])

    contract_sort = KSort(f'{contract_name}Contract')

    storage_sentences = []
    if generate_storage:
        storage_layout = contract_json['storageLayout']
        storage_sentences = generate_storage_sentences(contract_name, contract_sort, storage_layout)
    function_call_data_production, function_productions, function_rules = generate_function_sentences(contract_name, contract_sort, abi)
    function_sentences = [function_call_data_production] + function_productions + function_rules
    function_selector_alias_sentences = generate_function_selector_alias_sentences(contract_name, contract_sort, hashes)

    contract_klabel = KLabel(f'contract_{contract_name}')
    contract_subsort = KProduction(KSort('Contract'), [KNonTerminal(contract_sort)])
    contract_production = KProduction(contract_sort, [KTerminal(contract_name)], klabel=contract_klabel)
    contract_macro = KRule(KRewrite(KApply('binRuntime', [KApply(contract_klabel)]), KEVM.parse_bytestack(stringToken(bin_runtime))))

    module_name = contract_name.upper() + '-BIN-RUNTIME'
    module = KFlatModule(
        module_name,
        [contract_subsort, contract_production] + storage_sentences + function_sentences + [contract_macro] + function_selector_alias_sentences,
        [KImport('BIN-RUNTIME', True)],
    )

    return module


# Helpers

def generate_storage_sentences(contract_name, contract_sort, storage_layout):
    storage_sort = KSort(f'{contract_name}Storage')
    storage_sentence_pairs = _extract_storage_sentences(contract_name, storage_sort, storage_layout)

    if not storage_sentence_pairs:
        return []

    storage_productions, storage_rules = map(list, zip(*storage_sentence_pairs))
    storage_location_production = KProduction(KSort('Int'), [KNonTerminal(contract_sort), KTerminal('.'), KNonTerminal(storage_sort)], att=KAtt({'klabel': f'storage_{contract_name}', 'macro': ''}))
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
            new_rhs = KApply('_+Int_', [rhs, intToken(member_slot)])
            res += recur(new_syntax, new_lhs, new_rhs, var_idx, member_type_name)
        return res

    def recur_mapping(syntax, lhs, rhs, var_idx, key_type_name, value_type_name):
        key_type_dict = types[key_type_name]
        key_type_label = key_type_dict['label']

        _check_supported_key_type(key_type_label)
        key_sort = _evm_base_sort(key_type_label)

        new_syntax = syntax + [KTerminal('['), KNonTerminal(key_sort), KTerminal(']')]
        new_lhs = f'{lhs}[V{var_idx}]'
        new_rhs = KApply('hashedLocation', [stringToken('Solidity'), rhs, KVariable(f'V{var_idx}')])
        new_type_name = value_type_name
        return recur(new_syntax, new_lhs, new_rhs, var_idx + 1, new_type_name)

    storage = storage_layout['storage']
    return recur_struct([], f'{contract_name}', intToken('0'), 0, storage, gen_dot=False)


def generate_function_sentences(contract_name: str, contract_sort: KSort, abi):
    function_sort = KSort(f'{contract_name}Function')
    function_call_data_production: KSentence = KProduction(KSort('ByteArray'), [KNonTerminal(contract_sort), KTerminal('.'), KNonTerminal(function_sort)], klabel=KLabel(f'function_{contract_name}'), att=KAtt({'function': ''}))
    function_sentence_pairs = _extract_function_sentences(contract_name, function_sort, abi)

    function_productions: List[KSentence] = []
    function_rules: List[KSentence] = []
    for f_prod, f_rule in function_sentence_pairs:
        function_productions.append(f_prod)
        function_rules.append(f_rule)

    function_sentences = function_productions + function_rules
    return [function_call_data_production] + function_sentences if function_sentences else []


def generate_function_selector_alias_sentences(contract_name, contract_sort, hashes):
    abi_function_selector_rules = []
    for h in hashes:
        f_name = h.split('(')[0]
        hash_int = int(hashes[h], 16)
        abi_function_selector_rewrite = KRewrite(KApply('abi_selector', [stringToken(f'{f_name}')]), intToken(hash_int))
        abi_function_selector_rules.append(KRule(abi_function_selector_rewrite))
    return abi_function_selector_rules


def _extract_function_sentences(contract_name, function_sort, abi) -> List[Tuple[KProduction, KRule]]:
    def extract_production(name, inputs):
        input_types = [input_dict['type'] for input_dict in inputs]

        items = []
        items.append(KTerminal(name))
        items.append(KTerminal('('))

        input_nonterminals = (KNonTerminal(_evm_base_sort(input_type)) for input_type in input_types)
        items += intersperse(input_nonterminals, KTerminal(','))

        items.append(KTerminal(')'))
        return KProduction(function_sort, items, klabel=KLabel(f'{contract_name}_function_{name}'))

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
        return KEVM.abi_calldata(name, args)

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
        return KApply('rangeBytes', [intToken(4), term])
    if type_label in {'bytes32', 'uint256'}:
        return KApply('rangeUInt', [intToken(256), term])
    if type_label == 'int256':
        return KApply('rangeSInt', [intToken(256), term])
    if type_label == 'uint8':
        return KApply('rangeUInt', [intToken(8), term])
    if type_label == 'bytes':
        return None

    raise ValueError(f'Range predicate unknown for: {type_label}')
