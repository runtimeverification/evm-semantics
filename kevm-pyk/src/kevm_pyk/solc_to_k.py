import json
import logging
from dataclasses import dataclass
from functools import cached_property
from pathlib import Path
from subprocess import CalledProcessError
from typing import Any, Dict, Final, Iterable, List, Optional, Tuple

from pyk.cli_utils import run_process
from pyk.cterm import CTerm
from pyk.kast import (
    KApply,
    KAtt,
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
    build_assoc,
)
from pyk.kastManip import abstract_term_safely, substitute
from pyk.kcfg import KCFG
from pyk.prelude.kbool import FALSE, TRUE, andBool, notBool
from pyk.prelude.kint import intToken
from pyk.prelude.ml import mlEqualsTrue
from pyk.prelude.string import stringToken
from pyk.utils import FrozenDict, intersperse

from .kevm import KEVM, Foundry
from .utils import abstract_cell_vars

_LOGGER: Final = logging.getLogger(__name__)


@dataclass
class Contract:
    @dataclass
    class Method:
        name: str
        id: int
        sort: KSort
        arg_names: Tuple[str, ...]
        arg_types: Tuple[str, ...]
        contract_name: str
        payable: bool

        def __init__(self, name: str, id: int, abi: Dict, contract_name: str, sort: KSort) -> None:
            self.name = name
            self.id = id
            self.arg_names = tuple([f'V{i}_{input["name"].replace("-", "_")}' for i, input in enumerate(abi['inputs'])])
            self.arg_types = tuple([input['type'] for input in abi['inputs']])
            self.contract_name = contract_name
            self.sort = sort
            # TODO: Check that we're handling all state mutability cases
            self.payable = abi['stateMutability'] == 'payable'

        @property
        def selector_alias_rule(self) -> KRule:
            return KRule(KRewrite(KEVM.abi_selector(self.name), intToken(self.id)))

        @property
        def production(self) -> KProduction:
            input_nonterminals = (KNonTerminal(_evm_base_sort(input_type)) for input_type in self.arg_types)
            items_before: List[KProductionItem] = [KTerminal(self.name), KTerminal('(')]
            items_args: List[KProductionItem] = list(intersperse(input_nonterminals, KTerminal(',')))
            items_after: List[KProductionItem] = [KTerminal(')')]
            return KProduction(
                self.sort,
                items_before + items_args + items_after,
                klabel=KLabel(f'method_{self.contract_name}_{self.name}'),
                att=KAtt({'symbol': ''}),
            )

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
                    _LOGGER.warning(
                        f'Unsupported ABI type for method {contract_name}.{prod_klabel.name}, will not generate calldata sugar: {input_type}'
                    )
                    return None
                conjuncts.append(rp)
            lhs = KApply(application_label, [contract, KApply(prod_klabel, arg_vars)])
            rhs = KEVM.abi_calldata(self.name, args)
            ensures = andBool(conjuncts)
            return KRule(KRewrite(lhs, rhs), ensures=ensures)

        @cached_property
        def callvalue_cell(self) -> KInner:
            return (
                intToken(0)
                if not self.payable
                else abstract_term_safely(KVariable('_###CALLVALUE###_'), base_name='CALLVALUE')
            )

        def calldata_cell(self, contract: 'Contract') -> KInner:
            return KApply(contract.klabel_method, [KApply(contract.klabel), self.application])

        @cached_property
        def application(self) -> KInner:
            klabel = self.production.klabel
            assert klabel is not None
            args = [
                abstract_term_safely(KVariable('_###SOLIDITY_ARG_VAR###_'), base_name=f'V{name}')
                for name in self.arg_names
            ]
            return klabel(args)

    name: str
    bytecode: str
    methods: Tuple[Method, ...]
    test_methods: Tuple[Method, ...]
    fields: FrozenDict

    def __init__(self, contract_name: str, contract_json: Dict, foundry: bool = False) -> None:
        def _get_method_abi(_mname: str) -> Dict:
            for _method in contract_json['abi']:
                if _method['type'] == 'function' and _method['name'] == _mname:
                    return _method
            raise ValueError(f'Method not found in abi: {_mname}')

        self.name = contract_name
        self.bytecode = (
            contract_json['evm']['deployedBytecode']['object']
            if not foundry
            else contract_json['deployedBytecode']['object']
        )
        _methods = []
        if not foundry and 'evm' in contract_json and 'methodIdentifiers' in contract_json['evm']:
            _method_identifiers = contract_json['evm']['methodIdentifiers']
        elif foundry and 'methodIdentifiers' in contract_json:
            _method_identifiers = contract_json['methodIdentifiers']
        else:
            _method_identifiers = []
            _LOGGER.warning(f'Could not find member \'methodIdentifiers\' while processing contract: {self.name}')
        for msig in _method_identifiers:
            mname = msig.split('(')[0]
            mid = int(_method_identifiers[msig], 16)
            _m = Contract.Method(mname, mid, _get_method_abi(mname), contract_name, self.sort_method)
            _methods.append(_m)
        self.methods = tuple(_methods)
        if 'storageLayout' not in contract_json or 'storage' not in contract_json['storageLayout']:
            _LOGGER.warning(f'Could not find member \'storageLayout\' while processing contract: {self.name}')
            self.fields = FrozenDict({})
        else:
            _fields_list = [(_f['label'], int(_f['slot'])) for _f in contract_json['storageLayout']['storage']]
            _fields = {}
            for _l, _s in _fields_list:
                if _l in _fields:
                    _LOGGER.warning(f'Found duplicate field access key on contract {self.name}: {_l}')
                    continue
                _fields[_l] = _s
            self.fields = FrozenDict(_fields)

    @staticmethod
    def contract_to_module_name(c: str, spec: bool = True) -> str:
        m = c.upper() + '-BIN-RUNTIME'
        if spec:
            m = m + '-SPEC'
        return m

    @staticmethod
    def test_to_claim_name(t: str) -> str:
        return t.replace('_', '-')

    @staticmethod
    def contract_test_to_claim_id(ct: str, spec: bool = True) -> str:
        _c, _t = ct.split('.')
        return f'{Contract.contract_to_module_name(_c, spec=spec)}.{Contract.test_to_claim_name(_t)}'

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
        return KProduction(self.sort, [KTerminal(self.name)], klabel=self.klabel, att=KAtt({'symbol': ''}))

    @property
    def macro_bin_runtime(self) -> KRule:
        return KRule(KRewrite(KEVM.bin_runtime(KApply(self.klabel)), KEVM.parse_bytestack(stringToken(self.bytecode))))

    @property
    def method_sentences(self) -> List[KSentence]:
        method_application_production: KSentence = KProduction(
            KSort('ByteArray'),
            [KNonTerminal(self.sort), KTerminal('.'), KNonTerminal(self.sort_method)],
            klabel=self.klabel_method,
            att=KAtt({'function': '', 'symbol': ''}),
        )
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

    def method_by_name(self, name: str) -> Optional['Contract.Method']:
        methods = [method for method in self.methods if method.name == 'setUp']
        if len(methods) > 1:
            raise ValueError(f'Found multiple methods with name {name}, expected at most one')
        if not methods:
            return None
        return methods[0]


def solc_compile(contract_file: Path, profile: bool = False) -> Dict[str, Any]:

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
        process_res = run_process(['solc', '--standard-json'], logger=_LOGGER, input=json.dumps(args), profile=profile)
    except CalledProcessError as err:
        raise RuntimeError('solc error', err.stdout, err.stderr) from err
    result = json.loads(process_res.stdout)
    if 'errors' in result:
        failed = False
        for error in result['errors']:
            if error['severity'] == 'error':
                _LOGGER.error(f'solc error:\n{error["formattedMessage"]}')
                failed = True
            elif error['severity'] == 'warning':
                _LOGGER.warning(f'solc warning:\n{error["formattedMessage"]}')
            else:
                _LOGGER.warning(
                    f'Unknown solc error severity level {error["severity"]}:\n{json.dumps(error, indent=2)}'
                )
        if failed:
            raise ValueError('Compilation failed.')
    return result


def contract_to_main_module(contract: Contract, empty_config: KInner, imports: Iterable[str] = ()) -> KFlatModule:
    module_name = Contract.contract_to_module_name(contract.name, spec=False)
    return KFlatModule(module_name, contract.sentences, [KImport(i) for i in list(imports)])


def method_to_cfg(empty_config: KInner, contract: Contract, method: Contract.Method) -> KCFG:
    calldata = method.calldata_cell(contract)
    callvalue = method.callvalue_cell
    init_term = _init_term(empty_config, contract.name, calldata=calldata, callvalue=callvalue)
    init_cterm = _init_cterm(init_term)
    is_test = method.name.startswith('test')
    failing = method.name.startswith('testFail')
    final_cterm = _final_cterm(empty_config, contract.name, failing=failing, is_test=is_test)

    cfg = KCFG()
    init_node = cfg.create_node(init_cterm)
    cfg.add_init(init_node.id)
    target_node = cfg.create_node(final_cterm)
    cfg.add_target(target_node.id)

    return cfg


def _init_cterm(init_term: KInner) -> CTerm:
    key_dst = KEVM.loc(KToken('FoundryCheat . Failed', 'ContractAccess'))
    dst_failed_prev = KEVM.lookup(KVariable('CHEATCODE_STORAGE'), key_dst)
    init_cterm = CTerm(init_term)
    init_cterm = KEVM.add_invariant(init_cterm)
    init_cterm = init_cterm.add_constraint(mlEqualsTrue(KApply('_==Int_', [dst_failed_prev, KToken('0', 'Int')])))
    return init_cterm


def _init_term(
    empty_config: KInner,
    contract_name: str,
    *,
    calldata: Optional[KInner] = None,
    callvalue: Optional[KInner] = None,
) -> KInner:
    program = KEVM.bin_runtime(KApply(f'contract_{contract_name}'))
    account_cell = KEVM.account_cell(
        Foundry.address_TEST_CONTRACT(),
        intToken(0),
        program,
        KVariable('ACCT_STORAGE'),
        KVariable('ACCT_ORIGSTORAGE'),
        intToken(0),
    )
    init_subst = {
        'MODE_CELL': KApply('NORMAL'),
        'SCHEDULE_CELL': KApply('LONDON_EVM'),
        'STATUSCODE_CELL': KVariable('STATUSCODE'),
        'CALLSTACK_CELL': KApply('.List'),
        'CALLDEPTH_CELL': intToken(0),
        'PROGRAM_CELL': program,
        'JUMPDESTS_CELL': KEVM.compute_valid_jumpdests(program),
        'ORIGIN_CELL': KVariable('ORIGIN_ID'),
        'ID_CELL': Foundry.address_TEST_CONTRACT(),
        'CALLER_CELL': KVariable('CALLER_ID'),
        'ACCESSEDACCOUNTS_CELL': KApply('.Set'),
        'ACCESSEDSTORAGE_CELL': KApply('.Map'),
        'ACTIVEACCOUNTS_CELL': build_assoc(
            KApply('.Set'),
            KLabel('_Set_'),
            map(
                KLabel('SetItem'),
                [
                    Foundry.address_TEST_CONTRACT(),
                    Foundry.address_CHEATCODE(),
                    Foundry.address_CALLER(),
                    Foundry.address_HARDHAT_CONSOLE(),
                ],
            ),
        ),
        'LOCALMEM_CELL': KApply('.Memory_EVM-TYPES_Memory'),
        'PREVCALLER_CELL': KToken('.Account', 'K'),
        'PREVORIGIN_CELL': KToken('.Account', 'K'),
        'NEWCALLER_CELL': KToken('.Account', 'K'),
        'NEWORIGIN_CELL': KToken('.Account', 'K'),
        'ACTIVE_CELL': FALSE,
        'STATIC_CELL': FALSE,
        'MEMORYUSED_CELL': intToken(0),
        'WORDSTACK_CELL': KApply('.WordStack_EVM-TYPES_WordStack'),
        'PC_CELL': intToken(0),
        'GAS_CELL': intToken(9223372036854775807),
        'K_CELL': KSequence([KEVM.execute(), KVariable('CONTINUATION')]),
        'ACCOUNTS_CELL': KEVM.accounts(
            [
                account_cell,  # test contract address
                Foundry.account_CALLER(),
                Foundry.account_CHEATCODE_ADDRESS(KVariable('CHEATCODE_STORAGE')),
                Foundry.account_HARDHAT_CONSOLE_ADDRESS(),
                KVariable('ACCOUNTS_INIT'),
            ]
        ),
    }

    if calldata is not None:
        init_subst['CALLDATA_CELL'] = calldata

    if callvalue is not None:
        init_subst['CALLVALUE_CELL'] = callvalue

    return substitute(empty_config, init_subst)


def _final_cterm(empty_config: KInner, contract_name: str, *, failing: bool, is_test: bool = True) -> CTerm:
    final_term = _final_term(empty_config, contract_name)
    key_dst = KEVM.loc(KToken('FoundryCheat . Failed', 'ContractAccess'))
    dst_failed_post = KEVM.lookup(KVariable('CHEATCODE_STORAGE_FINAL'), key_dst)
    foundry_success = Foundry.success(KVariable('STATUSCODE_FINAL'), dst_failed_post)
    final_cterm = CTerm(final_term)
    if is_test:
        if not failing:
            return final_cterm.add_constraint(mlEqualsTrue(foundry_success))
        else:
            return final_cterm.add_constraint(mlEqualsTrue(notBool(foundry_success)))
    return final_cterm


def _final_term(empty_config: KInner, contract_name: str) -> KInner:
    program = KEVM.bin_runtime(KApply(f'contract_{contract_name}'))
    post_account_cell = KEVM.account_cell(
        Foundry.address_TEST_CONTRACT(),
        KVariable('ACCT_BALANCE'),
        program,
        KVariable('ACCT_STORAGE_FINAL'),
        KVariable('ACCT_ORIGSTORAGE'),
        KVariable('ACCT_NONCE'),
    )
    final_subst = {
        'K_CELL': KSequence([KEVM.halt(), KVariable('CONTINUATION')]),
        'STATUSCODE_CELL': KVariable('STATUSCODE_FINAL'),
        'ID_CELL': Foundry.address_TEST_CONTRACT(),
        'ACCOUNTS_CELL': KEVM.accounts(
            [
                post_account_cell,  # test contract address
                Foundry.account_CALLER(),
                Foundry.account_CHEATCODE_ADDRESS(KVariable('CHEATCODE_STORAGE_FINAL')),
                Foundry.account_HARDHAT_CONSOLE_ADDRESS(),
                KVariable('ACCOUNTS_FINAL'),
            ]
        ),
    }
    return abstract_cell_vars(
        substitute(empty_config, final_subst), [KVariable('STATUSCODE_FINAL'), KVariable('ACCOUNTS_FINAL')]
    )


# Helpers


def _evm_base_sort(type_label: str) -> KSort:
    if _evm_base_sort_int(type_label):
        return KSort('Int')

    if type_label == 'bytes':
        return KSort('ByteArray')

    if type_label == 'string':
        return KSort('String')

    _LOGGER.warning(f'Using generic sort K for type: {type_label}')
    return KSort('K')


def _evm_base_sort_int(type_label: str) -> bool:
    success = False

    # Check address and bool
    if type_label in {'address', 'bool'}:
        success = True

    # Check bytes
    if type_label.startswith('bytes') and len(type_label) > 5 and not type_label.endswith(']'):
        width = int(type_label[5:])
        if not width in {4, 32}:
            raise ValueError(f'Unsupported evm base sort type: {type_label}')
        else:
            success = True

    # Check ints
    if type_label.startswith('int') and not type_label.endswith(']'):
        width = int(type_label[3:])
        if not width == 256:
            raise ValueError(f'Unsupported evm base sort type: {type_label}')
        else:
            success = True

    # Check uints
    if type_label.startswith('uint') and not type_label.endswith(']'):
        width = int(type_label[4:])
        if not (0 < width and width <= 256 and width % 8 == 0):
            raise ValueError(f'Unsupported evm base sort type: {type_label}')
        else:
            success = True

    return success


def _range_predicate(term: KInner, type_label: str) -> Optional[KInner]:
    (success, result) = _range_predicate_uint(term, type_label)
    if success:
        return result
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
    if type_label in {'bytes', 'string'}:
        return TRUE

    _LOGGER.warning(f'Unknown range predicate for type: {type_label}')
    return None


def _range_predicate_uint(term: KInner, type_label: str) -> Tuple[bool, Optional[KInner]]:
    if type_label.startswith('uint') and not type_label.endswith(']'):
        width = int(type_label[4:])
        if not (0 < width and width <= 256 and width % 8 == 0):
            raise ValueError(f'Unsupported range predicate type: {type_label}')
        return (True, KEVM.range_uint(width, term))
    else:
        return (False, None)
