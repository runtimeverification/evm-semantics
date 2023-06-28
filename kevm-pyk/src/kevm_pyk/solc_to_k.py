from __future__ import annotations

import json
import logging
import re
from dataclasses import dataclass
from functools import cached_property
from subprocess import CalledProcessError
from typing import TYPE_CHECKING

from pyk.kast.inner import KApply, KAtt, KLabel, KRewrite, KSort, KVariable
from pyk.kast.manip import abstract_term_safely
from pyk.kast.outer import KDefinition, KFlatModule, KImport, KNonTerminal, KProduction, KRequire, KRule, KTerminal
from pyk.prelude.kbool import TRUE, andBool
from pyk.prelude.kint import intToken
from pyk.prelude.string import stringToken
from pyk.utils import FrozenDict, hash_str, run_process, single

from .kevm import KEVM

if TYPE_CHECKING:
    from collections.abc import Iterable
    from pathlib import Path
    from typing import Any, Final

    from pyk.kast import KInner
    from pyk.kast.outer import KProductionItem, KSentence

_LOGGER: Final = logging.getLogger(__name__)


def solc_to_k(
    definition_dir: Path,
    contract_file: Path,
    contract_name: str,
    main_module: str | None,
    requires: Iterable[str] = (),
    imports: Iterable[str] = (),
) -> str:
    kevm = KEVM(definition_dir)
    empty_config = kevm.definition.empty_config(KEVM.Sorts.KEVM_CELL)

    solc_json = solc_compile(contract_file)
    contract_json = solc_json['contracts'][contract_file.name][contract_name]
    if 'sources' in solc_json and contract_file.name in solc_json['sources']:
        contract_source = solc_json['sources'][contract_file.name]
        for key in ['id', 'ast']:
            if key not in contract_json and key in contract_source:
                contract_json[key] = contract_source[key]
    contract = Contract(contract_name, contract_json, foundry=False)

    imports = list(imports)
    requires = list(requires)
    contract_module = contract_to_main_module(contract, empty_config, imports=['EDSL'] + imports)
    _main_module = KFlatModule(
        main_module if main_module else 'MAIN', [], [KImport(mname) for mname in [contract_module.name] + imports]
    )
    modules = (contract_module, _main_module)
    bin_runtime_definition = KDefinition(
        _main_module.name, modules, requires=tuple(KRequire(req) for req in ['edsl.md'] + requires)
    )

    _kprint = KEVM(definition_dir, extra_unparsing_modules=modules)
    return _kprint.pretty_print(bin_runtime_definition, unalias=False) + '\n'


@dataclass
class Contract:
    @dataclass
    class Method:
        name: str
        id: int
        sort: KSort
        arg_names: tuple[str, ...]
        arg_types: tuple[str, ...]
        contract_name: str
        contract_digest: str
        contract_storage_digest: str
        payable: bool
        signature: str
        ast: dict | None

        def __init__(
            self,
            msig: str,
            id: int,
            abi: dict,
            ast: dict | None,
            contract_name: str,
            contract_digest: str,
            contract_storage_digest: str,
            sort: KSort,
        ) -> None:
            self.signature = msig
            self.name = abi['name']
            self.id = id
            self.arg_names = tuple([f'V{i}_{input["name"].replace("-", "_")}' for i, input in enumerate(abi['inputs'])])
            self.arg_types = tuple([input['type'] for input in abi['inputs']])
            self.contract_name = contract_name
            self.contract_digest = contract_digest
            self.contract_storage_digest = contract_storage_digest
            self.sort = sort
            # TODO: Check that we're handling all state mutability cases
            self.payable = abi['stateMutability'] == 'payable'
            self.ast = ast

        @property
        def klabel(self) -> KLabel:
            args_list = '_'.join(self.arg_types)
            return KLabel(f'method_{self.contract_name}_{self.name}_{args_list}')

        @cached_property
        def qualified_name(self) -> str:
            return f'{self.contract_name}.{self.signature}'

        @property
        def selector_alias_rule(self) -> KRule:
            return KRule(KRewrite(KEVM.abi_selector(self.signature), intToken(self.id)))

        @cached_property
        def is_setup(self) -> bool:
            return self.name == 'setUp'

        def up_to_date(self, digest_file: Path) -> bool:
            if not digest_file.exists():
                return False
            digest_dict = json.loads(digest_file.read_text())
            if 'methods' not in digest_dict:
                digest_dict['methods'] = {}
                digest_file.write_text(json.dumps(digest_dict))
            if self.qualified_name not in digest_dict['methods']:
                return False
            return digest_dict['methods'][self.qualified_name]['method'] == self.digest

        def contract_up_to_date(self, digest_file: Path) -> bool:
            if not digest_file.exists():
                return False
            digest_dict = json.loads(digest_file.read_text())
            if 'methods' not in digest_dict:
                digest_dict['methods'] = {}
                digest_file.write_text(json.dumps(digest_dict))
            if self.qualified_name not in digest_dict['methods']:
                return False
            return digest_dict['methods'][self.qualified_name]['contract'] == self.contract_digest

        def update_digest(self, digest_file: Path) -> None:
            digest_dict = {}
            if digest_file.exists():
                digest_dict = json.loads(digest_file.read_text())
            if 'methods' not in digest_dict:
                digest_dict['methods'] = {}
            digest_dict['methods'][self.qualified_name] = {'method': self.digest, 'contract': self.contract_digest}
            digest_file.write_text(json.dumps(digest_dict))

            _LOGGER.info(f'Updated method {self.qualified_name} in digest file: {digest_file}')

        @cached_property
        def digest(self) -> str:
            ast = json.dumps(self.ast, sort_keys=True) if self.ast is not None else {}
            contract_digest = self.contract_digest if not self.is_setup else {}
            return hash_str(f'{self.signature}{ast}{self.contract_storage_digest}{contract_digest}')

        @property
        def production(self) -> KProduction:
            items_before: list[KProductionItem] = [KTerminal(self.name), KTerminal('(')]

            items_args: list[KProductionItem] = []
            for i, input_type in enumerate(self.arg_types):
                if i > 0:
                    items_args += [KTerminal(',')]
                items_args += [KNonTerminal(_evm_base_sort(input_type)), KTerminal(':'), KTerminal(input_type)]

            items_after: list[KProductionItem] = [KTerminal(')')]
            return KProduction(
                self.sort,
                items_before + items_args + items_after,
                klabel=self.klabel,
                att=KAtt({'symbol': ''}),
            )

        def rule(self, contract: KInner, application_label: KLabel, contract_name: str) -> KRule | None:
            arg_vars = [KVariable(aname) for aname in self.arg_names]
            prod_klabel = self.klabel
            assert prod_klabel is not None
            args: list[KInner] = []
            conjuncts: list[KInner] = []
            for input_name, input_type in zip(self.arg_names, self.arg_types, strict=True):
                args.append(KEVM.abi_type(input_type, KVariable(input_name)))
                rp = _range_predicate(KVariable(input_name), input_type)
                if rp is None:
                    _LOGGER.info(
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

        def calldata_cell(self, contract: Contract) -> KInner:
            return KApply(contract.klabel_method, [KApply(contract.klabel), self.application])

        @cached_property
        def application(self) -> KInner:
            klabel = self.klabel
            assert klabel is not None
            args = [
                abstract_term_safely(KVariable('_###SOLIDITY_ARG_VAR###_'), base_name=f'V{name}')
                for name in self.arg_names
            ]
            return klabel(args)

    name: str
    contract_json: dict
    contract_id: int
    contract_path: str
    bytecode: str
    raw_sourcemap: str | None
    methods: tuple[Method, ...]
    fields: FrozenDict

    def __init__(self, contract_name: str, contract_json: dict, foundry: bool = False) -> None:
        self.name = contract_name
        self.contract_json = contract_json

        self.contract_id = self.contract_json['id']
        self.contract_path = self.contract_json['ast']['absolutePath']

        evm = self.contract_json['evm'] if not foundry else self.contract_json

        deployed_bytecode = evm['deployedBytecode']
        self.bytecode = deployed_bytecode['object'].replace('0x', '')
        self.raw_sourcemap = deployed_bytecode['sourceMap'] if 'sourceMap' in deployed_bytecode else None

        contract_ast_nodes = [
            node
            for node in self.contract_json['ast']['nodes']
            if node['nodeType'] == 'ContractDefinition' and node['name'] == self.name
        ]
        contract_ast = single(contract_ast_nodes) if len(contract_ast_nodes) > 0 else {'nodes': []}
        function_asts = {
            node['functionSelector']: node
            for node in contract_ast['nodes']
            if node['nodeType'] == 'FunctionDefinition' and 'functionSelector' in node
        }

        _methods = []
        for method in contract_json['abi']:
            if method['type'] != 'function':
                continue
            msig = method_sig_from_abi(method)
            method_selector: str = str(evm['methodIdentifiers'][msig])
            mid = int(method_selector, 16)
            method_ast = function_asts[method_selector] if method_selector in function_asts else None
            _m = Contract.Method(
                msig, mid, method, method_ast, self.name, self.digest, self.storage_digest, self.sort_method
            )
            _methods.append(_m)

        self.methods = tuple(sorted(_methods, key=(lambda method: method.signature)))

        self.fields = FrozenDict({})
        if 'storageLayout' in self.contract_json and 'storage' in self.contract_json['storageLayout']:
            _fields_list = [(_f['label'], int(_f['slot'])) for _f in self.contract_json['storageLayout']['storage']]
            _fields = {}
            for _l, _s in _fields_list:
                if _l in _fields:
                    _LOGGER.info(f'Found duplicate field access key on contract {self.name}: {_l}')
                    continue
                _fields[_l] = _s
            self.fields = FrozenDict(_fields)

    @cached_property
    def digest(self) -> str:
        return hash_str(f'{self.name} - {json.dumps(self.contract_json, sort_keys=True)}')

    @cached_property
    def storage_digest(self) -> str:
        storage_layout = self.contract_json.get('storageLayout') or {}
        return hash_str(f'{self.name} - {json.dumps(storage_layout, sort_keys=True)}')

    @cached_property
    def srcmap(self) -> dict[int, tuple[int, int, int, str, int]]:
        _srcmap = {}

        if len(self.bytecode) > 0 and self.raw_sourcemap is not None:
            instr_to_pc = {}
            pc = 0
            instr = 0
            bs = [int(self.bytecode[i : i + 2], 16) for i in range(0, len(self.bytecode), 2)]
            while pc < len(bs):
                b = bs[pc]
                instr_to_pc[instr] = pc
                if 0x60 <= b and b < 0x7F:
                    push_width = b - 0x5F
                    pc = pc + push_width
                pc += 1
                instr += 1

            instrs_srcmap = self.raw_sourcemap.split(';')

            s, l, f, j, m = (0, 0, 0, '', 0)
            for i, instr_srcmap in enumerate(instrs_srcmap):
                fields = instr_srcmap.split(':')
                if len(fields) > 0 and fields[0] != '':
                    s = int(fields[0])
                if len(fields) > 1 and fields[1] != '':
                    l = int(fields[1])
                if len(fields) > 2 and fields[2] != '':
                    f = int(fields[2])
                if len(fields) > 3 and fields[3] != '':
                    j = fields[3]
                if len(fields) > 4 and fields[4] != '':
                    m = int(fields[4])
                _srcmap[i] = (s, l, f, j, m)

        return _srcmap

    @staticmethod
    def contract_to_module_name(c: str) -> str:
        return c.upper() + '-CONTRACT'

    @staticmethod
    def contract_to_verification_module_name(c: str) -> str:
        return c.upper() + '-VERIFICATION'

    @staticmethod
    def test_to_claim_name(t: str) -> str:
        return t.replace('_', '-')

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
        if self.has_unlinked():
            raise ValueError(
                f'Some library placeholders have been found in contract {self.name}. Please link the library(ies) first. Ref: https://docs.soliditylang.org/en/v0.8.20/using-the-compiler.html#library-linking'
            )
        return KRule(
            KRewrite(KEVM.bin_runtime(KApply(self.klabel)), KEVM.parse_bytestack(stringToken('0x' + self.bytecode)))
        )

    def has_unlinked(self) -> bool:
        return 0 <= self.bytecode.find('__')

    @property
    def method_sentences(self) -> list[KSentence]:
        method_application_production: KSentence = KProduction(
            KSort('Bytes'),
            [KNonTerminal(self.sort), KTerminal('.'), KNonTerminal(self.sort_method)],
            klabel=self.klabel_method,
            att=KAtt({'function': '', 'symbol': ''}),
        )
        res: list[KSentence] = [method_application_production]
        res.extend(method.production for method in self.methods)
        method_rules = (method.rule(KApply(self.klabel), self.klabel_method, self.name) for method in self.methods)
        res.extend(rule for rule in method_rules if rule)
        res.extend(method.selector_alias_rule for method in self.methods)
        return res if len(res) > 1 else []

    @property
    def field_sentences(self) -> list[KSentence]:
        prods: list[KSentence] = [self.subsort_field]
        rules: list[KSentence] = []
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
    def sentences(self) -> list[KSentence]:
        return [self.subsort, self.production, self.macro_bin_runtime] + self.field_sentences + self.method_sentences

    @property
    def method_by_name(self) -> dict[str, Contract.Method]:
        return {method.name: method for method in self.methods}


def solc_compile(contract_file: Path) -> dict[str, Any]:
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
                        'evm.deployedBytecode.sourceMap',
                    ],
                    '': ['ast'],
                },
            },
        },
    }

    try:
        process_res = run_process(['solc', '--standard-json'], logger=_LOGGER, input=json.dumps(args))
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
    module_name = Contract.contract_to_module_name(contract.name)
    return KFlatModule(module_name, contract.sentences, [KImport(i) for i in list(imports)])


def contract_to_verification_module(contract: Contract, empty_config: KInner, imports: Iterable[str]) -> KFlatModule:
    main_module_name = Contract.contract_to_module_name(contract.name)
    verification_module_name = Contract.contract_to_verification_module_name(contract.name)
    return KFlatModule(verification_module_name, [], [KImport(main_module_name)] + [KImport(i) for i in list(imports)])


# Helpers


def _evm_base_sort(type_label: str) -> KSort:
    if _evm_base_sort_int(type_label):
        return KSort('Int')

    if type_label == 'bytes':
        return KSort('Bytes')

    if type_label == 'string':
        return KSort('String')

    _LOGGER.info(f'Using generic sort K for type: {type_label}')
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


def _range_predicate(term: KInner, type_label: str) -> KInner | None:
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
    if type_label == 'bytes':
        return KEVM.range_uint(128, KEVM.size_bytes(term))
    if type_label == 'string':
        return TRUE

    _LOGGER.info(f'Unknown range predicate for type: {type_label}')
    return None


def _range_predicate_uint(term: KInner, type_label: str) -> tuple[bool, KInner | None]:
    if type_label.startswith('uint') and not type_label.endswith(']'):
        width = int(type_label[4:])
        if not (0 < width and width <= 256 and width % 8 == 0):
            raise ValueError(f'Unsupported range predicate type: {type_label}')
        return (True, KEVM.range_uint(width, term))
    else:
        return (False, None)


def method_sig_from_abi(method_json: dict) -> str:
    def unparse_input(input_json: dict) -> str:
        is_array = False
        is_sized = False
        array_size = 0
        base_type = input_json['type']
        if re.match(r'.+\[.*\]', base_type):
            is_array = True
            array_size_str = base_type.split('[')[1][:-1]
            if array_size_str != '':
                is_sized = True
                array_size = int(array_size_str)
            base_type = base_type.split('[')[0]
        if base_type == 'tuple':
            input_type = '('
            for i, component in enumerate(input_json['components']):
                if i != 0:
                    input_type += ','
                input_type += unparse_input(component)
            input_type += ')'
            if is_array and not (is_sized):
                input_type += '[]'
            elif is_array and is_sized:
                input_type += f'[{array_size}]'
            return input_type
        else:
            return input_json['type']

    method_name = method_json['name']
    method_args = ''
    for i, _input in enumerate(method_json['inputs']):
        if i != 0:
            method_args += ','
        method_args += unparse_input(_input)
    return f'{method_name}({method_args})'
