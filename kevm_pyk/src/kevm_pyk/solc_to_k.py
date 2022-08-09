import json
import logging
from dataclasses import dataclass
from pathlib import Path
from subprocess import CalledProcessError
from typing import Any, Dict, Final, List, Optional, Tuple

from pyk.cli_utils import run_process
from pyk.cterm import CTerm
from pyk.kast import (
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
from pyk.prelude import Bool, intToken, mlEqualsTrue, stringToken
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

        def rule(self, contract: KInner, application_label: KLabel, contract_name: str) -> Optional[KRule]:
            arg_vars = [KVariable(aname) for aname in self.arg_names]
            prod_klabel = self.production.klabel
            assert prod_klabel is not None
            args: List[KInner] = []
            conjuncts: List[KInner] = []
            for input_name, input_type in zip(self.arg_names, self.arg_types):
                args.append(KEVM.abi_type(input_type, KVariable(input_name)))
                rp = _range_predicate(KVariable(input_name), input_type)
                if rp is None:
                    _LOGGER.warning(f'Unsupported ABI type for method {contract_name}.{prod_klabel.name}, will not generate calldata sugar: {input_type}')
                    return None
            lhs = KApply(application_label, [contract, KApply(prod_klabel, arg_vars)])
            rhs = KEVM.abi_calldata(self.name, args)
            ensures = Bool.andBool(conjuncts)
            return KRule(KRewrite(lhs, rhs), ensures=ensures)

    name: str
    bytecode: str
    methods: Tuple[Method, ...]
    fields: FrozenDict

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
        _fields_list = [(_f['label'], int(_f['slot'])) for _f in contract_json['storageLayout']['storage']]
        _fields = {}
        for _l, _s in _fields_list:
            if _l in _fields:
                raise ValueError(f'Found duplicate field access key on contract {self.name}: {_l}')
            _fields[_l] = _s
        self.fields = FrozenDict(_fields)

    @property
    def name_upper(self) -> str:
        return self.name[0:1].upper() + self.name[1:]

    @property
    def sort(self) -> KSort:
        return KSort(f'{self.name_upper}Contract')

    @property
    def sort_field(self) -> KSort:
        return KSort(f'{self.name_upper}Field')

    @property
    def sort_method(self) -> KSort:
        return KSort(f'{self.name_upper}Method')

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
    def subsort_field(self) -> KProduction:
        return KProduction(KSort('Field'), [KNonTerminal(self.sort_field)])

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
        method_rules = (method.rule(KApply(self.klabel), self.klabel_method, self.name) for method in self.methods)
        res.extend(rule for rule in method_rules if rule)
        res.extend(method.selector_alias_rule for method in self.methods)
        return res if len(res) > 1 else []

    @property
    def field_sentences(self) -> List[KSentence]:
        prods: List[KSentence] = [self.subsort_field]
        rules: List[KSentence] = []
        for field, slot in self.fields.items():
            klabel = KLabel(self.klabel_field.name + f'_{field}')
            prods.append(KProduction(self.sort_field, [KTerminal(field)], klabel=klabel, att=KAtt({'symbol': ''})))
            rule_lhs = KEVM.loc(KApply(KLabel('contract_access_field'), [KApply(self.klabel), KApply(klabel)]))
            rule_rhs = intToken(slot)
            rules.append(KRule(KRewrite(rule_lhs, rule_rhs)))
        if len(prods) == 1 and not rules:
            return []
        return prods + rules

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
        # KApply('_AccountCellMap_', [account_cell, KVariable('ACCOUNTS')]),
        # KEVM.accounts([account_cell, KEVM.foundry_account()])
        'ACCOUNTS_CELL': KEVM.accounts([
            account_cell,
            KEVM.account_CALLER(),
            KEVM.account_TEST_CONTRACT_ADDRESS(),
            KEVM.account_CHEATCODE_ADDRESS(),
            KEVM.account_HARDHAT_CONSOLE_ADDRESS()])
    }
    final_subst = {'K_CELL': KSequence([KEVM.halt(), KVariable('CONTINUATION')])}
    init_term = substitute(empty_config, init_subst)
    if calldata_cells:
        init_terms = [(f'{contract_name.lower()}-{i}', substitute(init_term, {'CALLDATA_CELL': cd})) for i, cd in enumerate(calldata_cells)]
    else:
        init_terms = [(contract_name.lower(), init_term)]
    final_cterm = CTerm(abstract_cell_vars(substitute(empty_config, final_subst)))
    final_cterm = final_cterm.add_constraint(mlEqualsTrue(KEVM.foundry_success()))
    claims: List[KClaim] = []
    for claim_id, i_term in init_terms:
        claim, _ = build_claim(claim_id, CTerm(i_term), final_cterm)
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
    if type_label in {'address', 'bool', 'bytes4', 'bytes32', 'int256', 'uint256', 'uint8', 'uint64', 'uint96', 'uint32'}:
        return KSort('Int')

    if type_label == 'bytes':
        return KSort('ByteArray')

    if type_label == 'string':
        return KSort('String')

    _LOGGER.warning(f'Using generic sort K for type: {type_label}')
    return KSort('K')


def _range_predicate(term, type_label: str):
    if type_label == 'address':
        return KEVM.range_address(term)
    if type_label == 'bool':
        return KEVM.range_bool(term)
    if type_label == 'bytes4':
        return KEVM.range_bytes(intToken(4), term)
    if type_label in {'bytes32', 'uint256'}:
        return KEVM.range_uint(256, term)
    if type_label == 'int256':
        return KEVM.range_sint(256, term)
    if type_label == 'uint8':
        return KEVM.range_uint(8, term)
    if type_label == 'uint64':
        return KEVM.range_uint(64, term)
    if type_label == 'uint96':
        return KEVM.range_uint(96, term)
    if type_label == 'uint32':
        return KEVM.range_uint(32, term)
    if type_label in {'bytes', 'string'}:
        return Bool.true

    _LOGGER.warning(f'Unknown range predicate for type: {type_label}')
    return None
