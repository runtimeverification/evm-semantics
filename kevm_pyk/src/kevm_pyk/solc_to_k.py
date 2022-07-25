import functools
import json
import logging
from dataclasses import dataclass
from pathlib import Path
from subprocess import CalledProcessError
from typing import Any, Container, Dict, Final, List, Optional, Tuple

from pyk.cli_utils import run_process
from pyk.cterm import CTerm
from pyk.kast import (
    TRUE,
    KApply,
    KAtt,
    KClaim,
    KFlatModule,
    KImport,
    KInner,
    KLabel,
    KNonTerminal,
    KProduction,
    KProductionItem,
    KRewrite,
    KRule,
    KSentence,
    KSequence,
    KSort,
    KTerminal,
    KToken,
    KVariable,
)
from pyk.kastManip import abstract_term_safely, substitute
from pyk.prelude import intToken, stringToken
from pyk.utils import intersperse

from .kevm import KEVM
from .utils import abstract_cell_vars, build_claim

_LOGGER: Final = logging.getLogger(__name__)


class Contract(Container['Contract.Method']):

    @dataclass
    class Method:
        name: str
        id: int
        signature: str
        abi: Dict

        def __init__(self, name: str, id: int, signature: str, abi: Dict) -> None:
            self.name = name
            self.id = id
            self.signature = signature
            self.abi = abi

        def production(self, contract_name: str, method_sort: KSort) -> KProduction:
            input_types = [_input['type'] for _input in self.abi['inputs']]
            input_nonterminals = (KNonTerminal(_evm_base_sort(input_type)) for input_type in input_types)
            items_before: List[KProductionItem] = [KTerminal(self.name), KTerminal('(')]
            items_args: List[KProductionItem] = list(intersperse(input_nonterminals, KTerminal(',')))
            items_after: List[KProductionItem] = [KTerminal(')')]
            return KProduction(method_sort, items_before + items_args + items_after, klabel=KLabel(f'{contract_name}_function_{self.name}'))

    name: str
    storage: Dict
    method_identifiers: Dict
    bytecode: str
    methods: List[Method]

    def __init__(self, contract_name: str, contract_json: Dict, foundry: bool = False) -> None:

        def _get_method_abi(_mname: str) -> Dict:
            for _method in contract_json['abi']:
                if _method['type'] == 'function' and _method['name'] == _mname:
                    return _method
            raise ValueError(f'Method not found in abi: {_mname}')

        self.name = contract_name
        self.storage = contract_json['storageLayout']
        self.method_identifiers = contract_json['evm']['methodIdentifiers'] if not foundry else contract_json['methodIdentifiers']
        self.bytecode = (contract_json['evm']['deployedBytecode']['object'] if not foundry else contract_json['deployedBytecode']['object'])
        self.methods = []
        for msig in self.method_identifiers:
            mname = msig.split('(')[0]
            mid = int(self.method_identifiers[msig], 16)
            self.methods.append(Contract.Method(mname, mid, msig, _get_method_abi(mname)))

    @property
    def sort(self) -> KSort:
        return KSort(f'{self.name}Contract')

    @property
    def sort_storage(self) -> KSort:
        return KSort(f'{self.name}Storage')

    @property
    def sort_method(self) -> KSort:
        return KSort(f'{self.name}Method')

    @property
    def klabel(self) -> KLabel:
        return KLabel(f'contract_{self.name}')

    @property
    def klabel_method(self) -> KLabel:
        return KLabel(f'method_{self.name}')


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


def gen_claims_for_contract(empty_config: KInner, contract_name: str, calldata_cells: List[KInner] = None) -> List[KClaim]:
    program = KEVM.bin_runtime(KApply(f'contract_{contract_name}'))
    account_cell = KEVM.account_cell(KVariable('ACCT_ID'), KVariable('ACCT_BALANCE'), program, KVariable('ACCT_STORAGE'), KVariable('ACCT_ORIGSTORAGE'), KVariable('ACCT_NONCE'))
    init_subst = {
        'MODE_CELL': KToken('NORMAL', 'Mode'),
        'SCHEDULE_CELL': KApply('LONDON_EVM'),
        'CALLSTACK_CELL': KApply('.List'),
        'CALLDEPTH_CELL': intToken(0),
        'PROGRAM_CELL': program,
        'JUMPDESTS_CELL': KEVM.compute_valid_jumpdests(program),
        'ORIGIN_CELL': KVariable('ORIGIN_ID'),
        'ID_CELL': KVariable('ACCT_ID'),
        'CALLER_CELL': KVariable('CALLER_ID'),
        'LOCALMEM_CELL': KApply('.Memory_EVM-TYPES_Memory'),
        'MEMORYUSED_CELL': intToken(0),
        'WORDSTACK_CELL': KApply('.WordStack_EVM-TYPES_WordStack'),
        'PC_CELL': intToken(0),
        'GAS_CELL': KEVM.inf_gas(KVariable('VGAS')),
        'K_CELL': KSequence([KEVM.execute(), KVariable('CONTINUATION')]),
        'ACCOUNTS_CELL': KApply('_AccountCellMap_', [account_cell, KVariable('ACCOUNTS')]),
    }
    final_subst = {'K_CELL': KSequence([KEVM.halt(), KVariable('CONTINUATION')])}
    init_term = substitute(empty_config, init_subst)
    if calldata_cells:
        init_terms = [(f'{contract_name.lower()}-{i}', substitute(init_term, {'CALLDATA_CELL': cd})) for i, cd in enumerate(calldata_cells)]
    else:
        init_terms = [(contract_name.lower(), init_term)]
    final_term = abstract_cell_vars(substitute(empty_config, final_subst))
    claims: List[KClaim] = []
    for claim_id, i_term in init_terms:
        claim, _ = build_claim(claim_id, CTerm(i_term), CTerm(final_term))
        claims.append(claim)
    return claims


def contract_to_k(contract: Contract, empty_config: KInner, foundry: bool = False) -> Tuple[KFlatModule, Optional[KFlatModule]]:

    contract_name = contract.name
    bin_runtime = contract.bytecode

    storage_sentences = generate_storage_sentences(contract)
    function_sentences = generate_function_sentences(contract)

    function_selector_alias_sentences = generate_function_selector_alias_sentences(contract)

    contract_klabel = contract.klabel
    contract_subsort: KSentence = KProduction(KSort('Contract'), [KNonTerminal(contract.sort)])
    contract_production: KSentence = KProduction(contract.sort, [KTerminal(contract_name)], klabel=contract_klabel)
    contract_macro: KSentence = KRule(KRewrite(KEVM.bin_runtime(KApply(contract_klabel)), KEVM.parse_bytestack(stringToken(bin_runtime))))

    module_name = contract_name.upper() + '-BIN-RUNTIME'
    sentences = [contract_subsort, contract_production] + storage_sentences + function_sentences + [contract_macro] + function_selector_alias_sentences
    module = KFlatModule(module_name, sentences, [KImport('EDSL')])

    claims_module: Optional[KFlatModule] = None
    function_test_productions = [prod for prod in module.syntax_productions if prod.sort == KSort(f'{contract_name}Method')]
    contract_function_application_label = contract.klabel_method
    function_test_calldatas = []
    for ftp in function_test_productions:
        klabel = ftp.klabel
        assert klabel is not None
        if klabel.name.startswith(f'{contract_name}_function_test'):
            args = [abstract_term_safely(KVariable('_###SOLIDITY_ARG_VAR###_'), base_name='V') for pi in ftp.items if type(pi) is KNonTerminal]
            calldata: KInner = KApply(contract_function_application_label, [KApply(contract_klabel), KApply(klabel, args)])
            function_test_calldatas.append(calldata)
    if function_test_calldatas:
        claims = gen_claims_for_contract(empty_config, contract_name, calldata_cells=function_test_calldatas)
        claims_module = KFlatModule(module_name + '-SPEC', claims, [KImport(module_name)])

    return module, claims_module


# Helpers

def generate_storage_sentences(contract: Contract) -> List[KSentence]:
    contract_name = contract.name
    storage_sort = contract.sort_storage

    storage_sentence_pairs = _extract_storage_sentences(contract)

    if not storage_sentence_pairs:
        return []

    storage_productions, storage_rules = map(list, zip(*storage_sentence_pairs))
    storage_location_production = KProduction(KSort('Int'), [KNonTerminal(contract.sort), KTerminal('.'), KNonTerminal(storage_sort)], att=KAtt({'klabel': f'storage_{contract_name}', 'macro': ''}))
    fin_list = []
    for sp in storage_productions:
        assert isinstance(sp, KSentence)
        fin_list.append(sp)
    assert isinstance(storage_location_production, KSentence)
    fin_list.append(storage_location_production)
    for sr in storage_rules:
        assert isinstance(sr, KSentence)
        fin_list.append(sr)
    return fin_list


def _extract_storage_sentences(contract: Contract):
    contract_name = contract.name
    storage_sort = contract.sort_storage
    storage_layout = contract.storage

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
            # TODO: Make less hacky once this is addressed: https://github.com/foundry-rs/foundry/issues/2462
            type_contents = '('.join(type_name.split('(')[1:])[0:-1]
            key_type_name, *rest = type_contents.split(',')
            value_type_name = ','.join(rest)
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
        return [(KProduction(storage_sort, syntax), KRule(KRewrite(KToken(lhs, None), rhs)))]

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
        new_rhs = KEVM.hashed_location('Solidity', rhs, KVariable(f'V{var_idx}'))
        new_type_name = value_type_name
        return recur(new_syntax, new_lhs, new_rhs, var_idx + 1, new_type_name)

    storage = storage_layout['storage']
    return recur_struct([], f'{contract_name}', intToken(0), 0, storage, gen_dot=False)


def generate_function_sentences(contract: Contract) -> List[KSentence]:

    function_call_data_production: KSentence = KProduction(KSort('ByteArray'), [KNonTerminal(contract.sort), KTerminal('.'), KNonTerminal(contract.sort_method)], klabel=contract.klabel_method, att=KAtt({'function': ''}))
    function_sentence_pairs = _extract_function_sentences(contract)

    function_productions: List[KSentence] = []
    function_rules: List[KSentence] = []
    for f_prod, f_rule in function_sentence_pairs:
        function_productions.append(f_prod)
        function_rules.append(f_rule)

    function_sentences = function_productions + function_rules
    return [function_call_data_production] + function_sentences if function_sentences else []


def generate_function_selector_alias_sentences(contract: Contract):
    abi_function_selector_rules = []
    for method in contract.methods:
        abi_function_selector_rewrite = KRewrite(KEVM.abi_selector(method.name), intToken(method.id))
        abi_function_selector_rules.append(KRule(abi_function_selector_rewrite))
    return abi_function_selector_rules


def _extract_function_sentences(contract: Contract) -> List[Tuple[KProduction, KRule]]:
    contract_name = contract.name

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
        args = [KEVM.abi_type(input_type, KVariable(input_name)) for input_name, input_type in zip(input_names, input_types)] or [KToken('.TypedArgs', 'TypedArgs')]
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
    for method in contract.methods:
        name = method.name
        inputs = method.abi['inputs']
        res.append((method.production(contract.name, contract.sort_method), extract_rule(name, inputs)))
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
        return KEVM.range_address(term)
    if type_label == 'bool':
        return KEVM.range_bool(term)
    if type_label == 'bytes4':
        return KEVM.range_bytes(intToken(4), term)
    if type_label in {'bytes32', 'uint256'}:
        return KEVM.range_uint256(term)
    if type_label == 'int256':
        return KEVM.range_sint256(term)
    if type_label == 'uint8':
        return KEVM.range_uint8(term)
    if type_label == 'bytes':
        return None

    raise ValueError(f'Range predicate unknown for: {type_label}')
