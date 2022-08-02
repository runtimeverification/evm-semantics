import functools
import json
import logging
from dataclasses import dataclass
from pathlib import Path
from subprocess import CalledProcessError
from typing import Any, Dict, Final, List, Optional, Tuple

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
from pyk.kastManip import abstract_term_safely, build_claim, substitute
from pyk.prelude import Sorts, intToken, stringToken
from pyk.utils import FrozenDict, intersperse

from .kevm import KEVM
from .utils import abstract_cell_vars

_LOGGER: Final = logging.getLogger(__name__)


@dataclass
class Contract():

    @dataclass
    class Method:
        name: str
        id: int
        sort: KSort
        arg_names: Tuple[str, ...]
        arg_types: Tuple[str, ...]
        contract_name: str

        def __init__(self, name: str, id: int, abi: Dict, contract_name: str, sort: KSort) -> None:
            self.name = name
            self.id = id
            self.arg_names = tuple([f'V{i}_{input["name"].replace("-", "_")}' for i, input in enumerate(abi['inputs'])])
            self.arg_types = tuple([input['type'] for input in abi['inputs']])
            self.contract_name = contract_name
            self.sort = sort

        @property
        def selector_alias_rule(self) -> KRule:
            return KRule(KRewrite(KEVM.abi_selector(self.name), intToken(self.id)))

        @property
        def production(self) -> KProduction:
            input_nonterminals = (KNonTerminal(_evm_base_sort(input_type)) for input_type in self.arg_types)
            items_before: List[KProductionItem] = [KTerminal(self.name), KTerminal('(')]
            items_args: List[KProductionItem] = list(intersperse(input_nonterminals, KTerminal(',')))
            items_after: List[KProductionItem] = [KTerminal(')')]
            return KProduction(self.sort, items_before + items_args + items_after, klabel=KLabel(f'method_{self.contract_name}_{self.name}'))

        def rule(self, contract: KInner, application_label: KLabel, contract_name: str) -> KRule:
            arg_vars = [KVariable(aname) for aname in self.arg_names]
            prod_klabel = self.production.klabel
            assert prod_klabel is not None
            lhs = KApply(application_label, [contract, KApply(prod_klabel, arg_vars)])
            args: List[KInner] = [KEVM.abi_type(input_type, KVariable(input_name)) for input_type, input_name in zip(self.arg_types, self.arg_names)]
            rhs = KEVM.abi_calldata(self.name, args)
            opt_conjuncts = [_range_predicate(KVariable(input_name), input_type) for input_name, input_type in zip(self.arg_names, self.arg_types)]
            conjuncts = [opt_conjunct for opt_conjunct in opt_conjuncts if opt_conjunct is not None]
            if not conjuncts:
                ensures = TRUE
            else:
                ensures = functools.reduce(lambda x, y: KApply('_andBool_', [x, y]), conjuncts)
            return KRule(KRewrite(lhs, rhs), ensures=ensures)

    @dataclass
    class Field:
        name: str
        slot: int
        type: str
        sort: KSort
        klabel: KLabel
        types: FrozenDict

        def __init__(self, name: str, slot: int, type: str, contract_name: str, field_sort: KSort, types: Dict) -> None:
            self.name = name
            self.slot = slot
            self.type = type
            self.sort = field_sort
            self.klabel = KLabel(f'field_{contract_name}_{self.name}')
            self.types = FrozenDict(types)

        def _direct_placement(self, type: str) -> bool:
            return self.types[type]['encoding'] in {'inplace', 'bytes'} and int(self.types[type]['numberOfBytes']) <= 32

        @property
        def productions(self) -> List[KProduction]:
            prods: List[KProduction] = []
            syntax: List[KProductionItem] = [KTerminal(self.name)]
            curr_type = self.type
            while True:
                if self._direct_placement(curr_type):
                    prods.append(KProduction(self.sort, syntax, klabel=self.klabel))
                    break
                elif self.types[curr_type]['encoding'] == 'inplace' and curr_type.startswith('t_struct'):
                    for _m in self.types[curr_type]['members']:
                        if not self._direct_placement(_m['type']):
                            raise ValueError(f'Unsupported type as struct member in field {self.sort}: {_m["type"]}')
                        prods.append(KProduction(self.sort, syntax + [KTerminal('.'), KTerminal(_m["label"])], klabel=KLabel(f'{self.klabel.name}_{_m["label"]}')))
                    break
                elif self.types[curr_type]['encoding'] == 'mapping':
                    key_type = self.types[curr_type]['key']
                    curr_type = self.types[curr_type]['value']
                    if not self._direct_placement(key_type):
                        raise ValueError(f'Unsupported key type for mapping in field {self.sort}: {key_type}')
                    syntax.extend([KTerminal('['), KNonTerminal(Sorts.INT), KTerminal(']')])
                else:
                    raise ValueError(f'Unsupported type for encoding in field {self.sort}: {curr_type}')
            return prods

        def rules(self, contract: KInner, application_label: KLabel) -> List[KRule]:
            rules: List[KRule] = []
            for mid, prod in enumerate(self.productions):
                non_terminal_prods = [pitem for pitem in prod.items if type(pitem) is KNonTerminal]
                var_names: List[KInner] = [KVariable(f'V{i}') for i, _ in enumerate(non_terminal_prods)]
                prod_klabel = prod.klabel
                assert prod_klabel is not None
                lhs = KApply(application_label, [contract, KApply(prod_klabel, var_names)])
                rhs = KEVM.hashed_location('Solidity', intToken(self.slot), KEVM.intlist(var_names), member_offset=mid)
                rules.append(KRule(KRewrite(lhs, rhs)))
            return rules

    name: str
    bytecode: str
    methods: Tuple[Method, ...]
    fields: Tuple[Field, ...]

    def __init__(self, contract_name: str, contract_json: Dict, foundry: bool = False) -> None:

        def _get_method_abi(_mname: str) -> Dict:
            for _method in contract_json['abi']:
                if _method['type'] == 'function' and _method['name'] == _mname:
                    return _method
            raise ValueError(f'Method not found in abi: {_mname}')

        self.name = contract_name
        self.bytecode = (contract_json['evm']['deployedBytecode']['object'] if not foundry else contract_json['deployedBytecode']['object'])
        method_identifiers = contract_json['evm']['methodIdentifiers'] if not foundry else contract_json['methodIdentifiers']
        _methods = []
        for msig in method_identifiers:
            mname = msig.split('(')[0]
            mid = int(method_identifiers[msig], 16)
            _methods.append(Contract.Method(mname, mid, _get_method_abi(mname), contract_name, self.sort_method))
        self.methods = tuple(_methods)
        _fields = []
        for storage in contract_json['storageLayout']['storage']:
            if storage['offset'] != 0:
                raise ValueError(f'Unsupported nonzero offset for contract {self.name} storage slot: {storage["label"]}')
            _fields.append(Contract.Field(storage['label'], int(storage['slot']), storage['type'], self.name, self.sort_field, contract_json['storageLayout']['types']))
        self.fields = tuple(_fields)

    @property
    def sort(self) -> KSort:
        return KSort(f'{self.name}Contract')

    @property
    def sort_field(self) -> KSort:
        return KSort(f'{self.name}Field')

    @property
    def sort_method(self) -> KSort:
        return KSort(f'{self.name}Method')

    @property
    def klabel(self) -> KLabel:
        return KLabel(f'contract_{self.name}')

    @property
    def klabel_method(self) -> KLabel:
        return KLabel(f'method_{self.name}')

    @property
    def klabel_field(self) -> KLabel:
        return KLabel(f'field_{self.name}')

    @property
    def subsort(self) -> KProduction:
        return KProduction(KSort('Contract'), [KNonTerminal(self.sort)])

    @property
    def production(self) -> KProduction:
        return KProduction(self.sort, [KTerminal(self.name)], klabel=self.klabel)

    @property
    def macro_bin_runtime(self) -> KRule:
        return KRule(KRewrite(KEVM.bin_runtime(KApply(self.klabel)), KEVM.parse_bytestack(stringToken(self.bytecode))))

    @property
    def method_sentences(self) -> List[KSentence]:
        method_application_production: KSentence = KProduction(KSort('ByteArray'), [KNonTerminal(self.sort), KTerminal('.'), KNonTerminal(self.sort_method)], klabel=self.klabel_method, att=KAtt({'function': ''}))
        res: List[KSentence] = [method_application_production]
        res.extend(method.production for method in self.methods)
        res.extend(method.rule(KApply(self.klabel), self.klabel_method, self.name) for method in self.methods)
        res.extend(method.selector_alias_rule for method in self.methods)
        return res if len(res) > 1 else []

    @property
    def field_sentences(self) -> List[KSentence]:
        field_access_production: KSentence = KProduction(KSort('Int'), [KNonTerminal(self.sort), KTerminal('.'), KNonTerminal(self.sort_field)], klabel=self.klabel_field, att=KAtt({'macro': ''}))
        res: List[KSentence] = [field_access_production]
        res.extend(prod for field in self.fields for prod in field.productions)
        res.extend(rule for field in self.fields for rule in field.rules(KApply(self.klabel), self.klabel_field))
        return res if len(res) > 1 else []

    @property
    def sentences(self) -> List[KSentence]:
        return [self.subsort, self.production, self.macro_bin_runtime] + self.field_sentences + self.method_sentences


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

    sentences = contract.sentences
    module_name = contract_name.upper() + '-BIN-RUNTIME'
    module = KFlatModule(module_name, sentences, [KImport('EDSL')])

    claims_module: Optional[KFlatModule] = None
    function_test_productions = [prod for prod in module.syntax_productions if prod.sort == KSort(f'{contract_name}Method')]
    contract_function_application_label = contract.klabel_method
    function_test_calldatas = []
    for ftp in function_test_productions:
        klabel = ftp.klabel
        assert klabel is not None
        if klabel.name.startswith(f'method_{contract_name}_test'):
            args = [abstract_term_safely(KVariable('_###SOLIDITY_ARG_VAR###_'), base_name='V') for pi in ftp.items if type(pi) is KNonTerminal]
            calldata: KInner = KApply(contract_function_application_label, [KApply(contract.klabel), KApply(klabel, args)])
            function_test_calldatas.append(calldata)
    if function_test_calldatas:
        claims = gen_claims_for_contract(empty_config, contract_name, calldata_cells=function_test_calldatas)
        claims_module = KFlatModule(module_name + '-SPEC', claims, [KImport(module_name)])

    return module, claims_module


# Helpers

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
