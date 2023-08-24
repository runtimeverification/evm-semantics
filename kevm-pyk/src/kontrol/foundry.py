from __future__ import annotations

import concurrent.futures
import json
import logging
import os
import re
import shutil
from functools import cached_property
from pathlib import Path
from subprocess import CalledProcessError
from typing import TYPE_CHECKING

import tomlkit
from pathos.pools import ProcessPool  # type: ignore
from pyk.cterm import CTerm
from pyk.kast.inner import KApply, KSequence, KSort, KToken, KVariable, Subst
from pyk.kast.manip import free_vars, minimize_term
from pyk.kast.outer import KDefinition, KFlatModule, KImport, KRequire
from pyk.kcfg import KCFG
from pyk.ktool.kompile import LLVMKompileType
from pyk.prelude.bytes import bytesToken
from pyk.prelude.k import GENERATED_TOP_CELL
from pyk.prelude.kbool import FALSE, notBool
from pyk.prelude.kint import INT, intToken
from pyk.prelude.ml import mlEqualsTrue
from pyk.proof.proof import Proof
from pyk.proof.reachability import APRBMCProof, APRProof
from pyk.proof.show import APRBMCProofNodePrinter, APRProofNodePrinter, APRProofShow
from pyk.utils import BugReport, ensure_dir_path, hash_str, run_process, single, unique

from kevm_pyk.kevm import KEVM, KEVMNodePrinter, KEVMSemantics
from kevm_pyk.utils import (
    KDefinition__expand_macros,
    abstract_cell_vars,
    byte_offset_to_lines,
    constraints_for,
    kevm_prove,
    legacy_explore,
    print_failure_info,
    print_model,
)

from .solc_to_k import Contract, contract_to_main_module, contract_to_verification_module

if TYPE_CHECKING:
    from collections.abc import Iterable
    from concurrent.futures import Future
    from typing import Any, Final

    from pyk.kast.inner import KInner
    from pyk.kcfg import KCFGExplore
    from pyk.kcfg.kcfg import NodeIdLike
    from pyk.kcfg.tui import KCFGElem
    from pyk.proof.show import NodePrinter

_LOGGER: Final = logging.getLogger(__name__)


class Foundry:
    _root: Path
    _toml: dict[str, Any]
    _bug_report: BugReport | None

    class Sorts:
        FOUNDRY_CELL: Final = KSort('FoundryCell')

    def __init__(
        self,
        foundry_root: Path,
        bug_report: BugReport | None = None,
    ) -> None:
        self._root = foundry_root
        with (foundry_root / 'foundry.toml').open('rb') as f:
            self._toml = tomlkit.load(f)
        self._bug_report = bug_report

    @property
    def profile(self) -> dict[str, Any]:
        profile_name = os.getenv('FOUNDRY_PROFILE', default='default')
        return self._toml['profile'][profile_name]

    @property
    def out(self) -> Path:
        return self._root / self.profile.get('out', '')

    @cached_property
    def kevm(self) -> KEVM:
        definition_dir = self.out / 'kompiled'
        use_directory = self.out / 'tmp'
        main_file = definition_dir / 'foundry.k'
        ensure_dir_path(use_directory)
        return KEVM(
            definition_dir=definition_dir,
            main_file=main_file,
            use_directory=use_directory,
            bug_report=self._bug_report,
        )

    @cached_property
    def contracts(self) -> dict[str, Contract]:
        pattern = '*.sol/*.json'
        paths = self.out.glob(pattern)
        json_paths = [str(path) for path in paths]
        json_paths = [json_path for json_path in json_paths if not json_path.endswith('.metadata.json')]
        json_paths = sorted(json_paths)  # Must sort to get consistent output order on different platforms
        _LOGGER.info(f'Processing contract files: {json_paths}')
        _contracts = {}
        for json_path in json_paths:
            _LOGGER.debug(f'Processing contract file: {json_path}')
            contract_name = json_path.split('/')[-1]
            contract_json = json.loads(Path(json_path).read_text())
            contract_name = contract_name[0:-5] if contract_name.endswith('.json') else contract_name
            _contracts[contract_name] = Contract(contract_name, contract_json, foundry=True)
        return _contracts

    def proof_digest(self, contract: str, test_sig: str) -> str:
        return f'{contract}.{test_sig}:{self.contracts[contract].method_by_sig[test_sig].digest}'

    @cached_property
    def digest(self) -> str:
        contract_digests = [self.contracts[c].digest for c in sorted(self.contracts)]
        return hash_str('\n'.join(contract_digests))

    @cached_property
    def llvm_dylib(self) -> Path | None:
        from kevm_pyk.kompile import Kernel

        arch = Kernel.get()
        foundry_llvm_dir = self.out / 'kompiled-llvm'
        if arch == Kernel.LINUX:
            dylib = foundry_llvm_dir / 'interpreter.so'
        else:
            dylib = foundry_llvm_dir / 'interpreter.dylib'

        if dylib.exists():
            return dylib
        else:
            return None

    def up_to_date(self) -> bool:
        digest_file = self.out / 'digest'
        if not digest_file.exists():
            return False
        digest_dict = json.loads(digest_file.read_text())
        if 'foundry' not in digest_dict:
            digest_dict['foundry'] = ''
        digest_file.write_text(json.dumps(digest_dict))
        return digest_dict['foundry'] == self.digest

    def update_digest(self) -> None:
        digest_file = self.out / 'digest'
        digest_dict = {}
        if digest_file.exists():
            digest_dict = json.loads(digest_file.read_text())
        digest_dict['foundry'] = self.digest
        digest_file.write_text(json.dumps(digest_dict))

        _LOGGER.info(f'Updated Foundry digest file: {digest_file}')

    @cached_property
    def contract_ids(self) -> dict[int, str]:
        _contract_ids = {}
        for c in self.contracts.values():
            _contract_ids[c.contract_id] = c.name
        return _contract_ids

    def srcmap_data(self, contract_name: str, pc: int) -> tuple[Path, int, int] | None:
        if contract_name not in self.contracts:
            _LOGGER.info(f'Contract not found in Foundry project: {contract_name}')
        contract = self.contracts[contract_name]
        if pc not in contract.srcmap:
            _LOGGER.info(f'pc not found in srcmap for contract {contract_name}: {pc}')
            return None
        s, l, f, _, _ = contract.srcmap[pc]
        if f not in self.contract_ids:
            _LOGGER.info(f'Contract id not found in sourcemap data: {f}')
            return None
        src_contract = self.contracts[self.contract_ids[f]]
        src_contract_path = self._root / src_contract.contract_path
        src_contract_text = src_contract_path.read_text()
        _, start, end = byte_offset_to_lines(src_contract_text.split('\n'), s, l)
        return (src_contract_path, start, end)

    def solidity_src(self, contract_name: str, pc: int) -> Iterable[str]:
        srcmap_data = self.srcmap_data(contract_name, pc)
        if srcmap_data is None:
            return [f'No sourcemap data for contract at pc {contract_name}: {pc}']
        contract_path, start, end = srcmap_data
        if not (contract_path.exists() and contract_path.is_file()):
            return [f'No file at path for contract {contract_name}: {contract_path}']
        lines = contract_path.read_text().split('\n')
        prefix_lines = [f'   {l}' for l in lines[:start]]
        actual_lines = [f' | {l}' for l in lines[start:end]]
        suffix_lines = [f'   {l}' for l in lines[end:]]
        return prefix_lines + actual_lines + suffix_lines

    def short_info_for_contract(self, contract_name: str, cterm: CTerm) -> list[str]:
        ret_strs = self.kevm.short_info(cterm)
        _pc = cterm.cell('PC_CELL')
        if type(_pc) is KToken and _pc.sort == INT:
            srcmap_data = self.srcmap_data(contract_name, int(_pc.token))
            if srcmap_data is not None:
                path, start, end = srcmap_data
                ret_strs.append(f'src: {str(path)}:{start}:{end}')
        return ret_strs

    def custom_view(self, contract_name: str, element: KCFGElem) -> Iterable[str]:
        if type(element) is KCFG.Node:
            pc_cell = element.cterm.cell('PC_CELL')
            if type(pc_cell) is KToken and pc_cell.sort == INT:
                return self.solidity_src(contract_name, int(pc_cell.token))
        return ['NO DATA']

    def build(self) -> None:
        try:
            run_process(['forge', 'build', '--root', str(self._root)], logger=_LOGGER)
        except CalledProcessError as err:
            raise RuntimeError("Couldn't forge build!") from err

    @cached_property
    def all_tests(self) -> list[str]:
        return [
            f'{contract.name}.{method.signature}'
            for contract in self.contracts.values()
            if contract.name.endswith('Test')
            for method in contract.methods
            if method.name.startswith('test')
        ]

    @cached_property
    def all_non_tests(self) -> list[str]:
        return [
            f'{contract.name}.{method.signature}'
            for contract in self.contracts.values()
            for method in contract.methods
            if f'{contract.name}.{method.signature}' not in self.all_tests
        ]

    def matching_tests(self, tests: list[str], exclude_tests: list[str]) -> list[str]:
        def _escape_brackets(regs: list[str]) -> list[str]:
            regs = [reg.replace('[', '\\[') for reg in regs]
            regs = [reg.replace(']', '\\]') for reg in regs]
            regs = [reg.replace('(', '\\(') for reg in regs]
            return [reg.replace(')', '\\)') for reg in regs]

        all_tests = self.all_tests
        all_non_tests = self.all_non_tests
        matched_tests = set()
        unfound_tests: list[str] = []
        if not tests:
            tests = all_tests
        tests = _escape_brackets(tests)
        exclude_tests = _escape_brackets(exclude_tests)
        for t in tests:
            if not any(re.search(t, test) for test in (all_tests + all_non_tests)):
                unfound_tests.append(t)
        for test in all_tests:
            if any(re.search(t, test) for t in tests) and not any(re.search(t, test) for t in exclude_tests):
                matched_tests.add(test)
        for test in all_non_tests:
            if any(re.search(t, test) for t in tests) and not any(re.search(t, test) for t in exclude_tests):
                matched_tests.add(test)
        if unfound_tests:
            raise ValueError(f'Test identifiers not found: {set(unfound_tests)}')
        elif len(matched_tests) == 0:
            raise ValueError('No test matched the predicates')
        return list(matched_tests)

    def matching_sig(self, test: str) -> str:
        test_sigs = self.matching_tests([test], [])
        if len(test_sigs) != 1:
            raise RuntimeError(f'Found {test_sigs} matching tests, must specify one')
        return test_sigs[0]

    def unique_sig(self, test: str) -> tuple[str, str]:
        contract_name = test.split('.')[0]
        test_sig = self.matching_sig(test).split('.')[1]
        return (contract_name, test_sig)

    @staticmethod
    def success(s: KInner, dst: KInner, r: KInner, c: KInner, e1: KInner, e2: KInner) -> KApply:
        return KApply('foundry_success', [s, dst, r, c, e1, e2])

    @staticmethod
    def fail(s: KInner, dst: KInner, r: KInner, c: KInner, e1: KInner, e2: KInner) -> KApply:
        return notBool(Foundry.success(s, dst, r, c, e1, e2))

    # address(uint160(uint256(keccak256("foundry default caller"))))

    @staticmethod
    def loc_FOUNDRY_FAILED() -> KApply:  # noqa: N802
        return KEVM.loc(
            KApply(
                'contract_access_field',
                [
                    KApply('FoundryCheat_FOUNDRY-ACCOUNTS_FoundryContract'),
                    KApply('Failed_FOUNDRY-ACCOUNTS_FoundryField'),
                ],
            )
        )

    @staticmethod
    def address_TEST_CONTRACT() -> KToken:  # noqa: N802
        return intToken(0x7FA9385BE102AC3EAC297483DD6233D62B3E1496)

    @staticmethod
    def address_CHEATCODE() -> KToken:  # noqa: N802
        return intToken(0x7109709ECFA91A80626FF3989D68F67F5B1DD12D)

    # Same address as the one used in DappTools's HEVM
    # address(bytes20(uint160(uint256(keccak256('hevm cheat code')))))
    @staticmethod
    def account_CHEATCODE_ADDRESS(store_var: KInner) -> KApply:  # noqa: N802
        return KEVM.account_cell(
            Foundry.address_CHEATCODE(),  # Hardcoded for now
            intToken(0),
            bytesToken(b'\x00'),
            store_var,
            KApply('.Map'),
            intToken(0),
        )

    @staticmethod
    def help_info() -> list[str]:
        res_lines: list[str] = []
        print_foundry_success_info = any('foundry_success' in line for line in res_lines)
        if print_foundry_success_info:
            res_lines.append('')
            res_lines.append('See `foundry_success` predicate for more information:')
            res_lines.append(
                'https://github.com/runtimeverification/evm-semantics/blob/master/include/kframework/foundry.md#foundry-success-predicate'
            )
        res_lines.append('')
        res_lines.append(
            'Access documentation for KEVM foundry integration at https://docs.runtimeverification.com/kevm-integration-for-foundry/'
        )
        return res_lines

    def get_apr_proof(
        self,
        test: str,
    ) -> APRProof:
        proof = self.get_proof(test)
        if not isinstance(proof, APRProof):
            raise ValueError('Specified proof is not an APRProof.')
        return proof

    def get_proof(
        self,
        test: str,
    ) -> Proof:
        proofs_dir = self.out / 'apr_proofs'
        contract_name, test_sig = self.unique_sig(test)
        proof_digest = self.proof_digest(contract_name, test_sig)
        proof = Proof.read_proof_data(proofs_dir, proof_digest)
        return proof


def foundry_kompile(
    foundry_root: Path,
    includes: Iterable[str],
    regen: bool = False,
    rekompile: bool = False,
    requires: Iterable[str] = (),
    imports: Iterable[str] = (),
    ccopts: Iterable[str] = (),
    llvm_kompile: bool = True,
    debug: bool = False,
    llvm_library: bool = False,
    verbose: bool = False,
) -> None:
    from kevm_pyk.kompile import KompileTarget, kevm_kompile

    syntax_module = 'FOUNDRY-CONTRACTS'
    foundry = Foundry(foundry_root)
    foundry_definition_dir = foundry.out / 'kompiled'
    foundry_requires_dir = foundry_definition_dir / 'requires'
    foundry_llvm_dir = foundry.out / 'kompiled-llvm'
    foundry_contracts_file = foundry_definition_dir / 'contracts.k'
    foundry_main_file = foundry_definition_dir / 'foundry.k'
    kompiled_timestamp = foundry_definition_dir / 'timestamp'
    main_module = 'FOUNDRY-MAIN'
    ensure_dir_path(foundry_definition_dir)
    ensure_dir_path(foundry_requires_dir)
    ensure_dir_path(foundry_llvm_dir)

    requires_paths: dict[str, str] = {}

    foundry.build()

    if not foundry.up_to_date():
        _LOGGER.info('Detected updates to contracts, regenerating K definition.')
        regen = True

    for r in requires:
        req = Path(r)
        if not req.exists():
            raise ValueError(f'No such file: {req}')
        if req.name in requires_paths.keys():
            raise ValueError(
                f'Required K files have conflicting names: {r} and {requires_paths[req.name]}. Consider changing the name of one of these files.'
            )
        requires_paths[req.name] = r
        req_path = foundry_requires_dir / req.name
        if regen or not req_path.exists():
            _LOGGER.info(f'Copying requires path: {req} -> {req_path}')
            shutil.copy(req, req_path)
            regen = True

    _imports: dict[str, list[str]] = {contract.name: [] for contract in foundry.contracts.values()}
    for i in imports:
        imp = i.split(':')
        if not len(imp) == 2:
            raise ValueError(f'module imports must be of the form "[ContractName]:[MODULE-NAME]". Got: {i}')
        if imp[0] in _imports:
            _imports[imp[0]].append(imp[1])
        else:
            raise ValueError(f'Could not find contract: {imp[0]}')

    if regen or not foundry_contracts_file.exists() or not foundry_main_file.exists():
        copied_requires = []
        copied_requires += [f'requires/{name}' for name in list(requires_paths.keys())]
        imports = ['FOUNDRY']
        kevm = KEVM(KompileTarget.FOUNDRY.definition_dir)
        empty_config = kevm.definition.empty_config(Foundry.Sorts.FOUNDRY_CELL)
        bin_runtime_definition = _foundry_to_contract_def(
            empty_config=empty_config,
            contracts=foundry.contracts.values(),
            requires=['foundry.md'],
        )

        contract_main_definition = _foundry_to_main_def(
            main_module=main_module,
            empty_config=empty_config,
            contracts=foundry.contracts.values(),
            requires=(['contracts.k'] + copied_requires),
            imports=_imports,
        )

        kevm = KEVM(
            KompileTarget.FOUNDRY.definition_dir,
            extra_unparsing_modules=(bin_runtime_definition.all_modules + contract_main_definition.all_modules),
        )
        foundry_contracts_file.write_text(kevm.pretty_print(bin_runtime_definition, unalias=False) + '\n')
        _LOGGER.info(f'Wrote file: {foundry_contracts_file}')
        foundry_main_file.write_text(kevm.pretty_print(contract_main_definition) + '\n')
        _LOGGER.info(f'Wrote file: {foundry_main_file}')

    def _kompile(
        out_dir: Path,
        backend: KompileTarget,
        llvm_kompile_type: LLVMKompileType | None = None,
    ) -> None:
        kevm_kompile(
            target=backend,
            output_dir=out_dir,
            main_file=foundry_main_file,
            main_module=main_module,
            syntax_module=syntax_module,
            includes=[include for include in includes if Path(include).exists()],
            emit_json=True,
            ccopts=ccopts,
            llvm_kompile_type=llvm_kompile_type,
            debug=debug,
            verbose=verbose,
        )

    def kompilation_digest() -> str:
        k_files = list(requires) + [foundry_contracts_file, foundry_main_file]
        return hash_str(''.join([hash_str(Path(k_file).read_text()) for k_file in k_files]))

    def kompilation_up_to_date() -> bool:
        digest_file = foundry_definition_dir / 'digest'
        if not digest_file.exists():
            return False
        old_digest = digest_file.read_text()

        return old_digest == kompilation_digest()

    def kompile_haskell() -> None:
        _LOGGER.info(f'Kompiling definition: {foundry_main_file}')
        _kompile(foundry_definition_dir, KompileTarget.HASKELL)

    def kompile_llvm() -> None:
        _LOGGER.info(f'Kompiling definition to LLVM dynamic library: {foundry_main_file}')
        _kompile(
            foundry_llvm_dir,
            KompileTarget.LLVM,
            llvm_kompile_type=LLVMKompileType.C,
        )

    def update_kompilation_digest() -> None:
        digest_file = foundry_definition_dir / 'digest'
        digest_file.write_text(kompilation_digest())

    if not kompilation_up_to_date() or rekompile or not kompiled_timestamp.exists():
        with concurrent.futures.ThreadPoolExecutor(max_workers=2) as executor:
            futures: list[Future] = []
            futures.append(executor.submit(kompile_haskell))
            if llvm_library:
                futures.append(executor.submit(kompile_llvm))
            [future.result() for future in futures]

    update_kompilation_digest()
    foundry.update_digest()


def foundry_prove(
    foundry_root: Path,
    max_depth: int = 1000,
    max_iterations: int | None = None,
    reinit: bool = False,
    tests: Iterable[str] = (),
    exclude_tests: Iterable[str] = (),
    workers: int = 1,
    simplify_init: bool = True,
    break_every_step: bool = False,
    break_on_jumpi: bool = False,
    break_on_calls: bool = True,
    bmc_depth: int | None = None,
    bug_report: bool = False,
    kore_rpc_command: str | Iterable[str] | None = None,
    use_booster: bool = False,
    smt_timeout: int | None = None,
    smt_retry_limit: int | None = None,
    failure_info: bool = True,
    counterexample_info: bool = False,
    trace_rewrites: bool = False,
    auto_abstract_gas: bool = False,
) -> dict[str, tuple[bool, list[str] | None]]:
    if workers <= 0:
        raise ValueError(f'Must have at least one worker, found: --workers {workers}')
    if max_iterations is not None and max_iterations < 0:
        raise ValueError(f'Must have a non-negative number of iterations, found: --max-iterations {max_iterations}')

    br = BugReport(foundry_root / 'bug_report') if bug_report else None
    foundry = Foundry(foundry_root, bug_report=br)

    save_directory = foundry.out / 'apr_proofs'
    save_directory.mkdir(exist_ok=True)

    if use_booster:
        try:
            run_process(('which', 'kore-rpc-booster'), pipe_stderr=True).stdout.strip()
        except CalledProcessError:
            raise RuntimeError(
                "Couldn't locate the kore-rpc-booster RPC binary. Please put 'kore-rpc-booster' on PATH manually or using kup install/kup shell."
            ) from None

    if kore_rpc_command is None:
        kore_rpc_command = ('kore-rpc-booster',) if use_booster else ('kore-rpc',)

    all_tests = [
        f'{contract.name}.{method.name}'
        for contract in foundry.contracts.values()
        if contract.name.endswith('Test')
        for method in contract.methods
        if method.name.startswith('test')
    ]
    all_non_tests = [
        f'{contract.name}.{method.name}'
        for contract in foundry.contracts.values()
        for method in contract.methods
        if f'{contract.name}.{method.name}' not in all_tests
    ]
    unfound_tests: list[str] = []
    tests = list(tests)
    if not tests:
        tests = all_tests
    for _t in tests:
        if _t not in (all_tests + all_non_tests):
            unfound_tests.append(_t)
    for _t in exclude_tests:
        if _t not in all_tests:
            unfound_tests.append(_t)
        if _t in tests:
            tests.remove(_t)

    tests = foundry.matching_tests(list(tests), list(exclude_tests))
    _LOGGER.info(f'Running tests: {tests}')

    setup_methods: dict[str, str] = {}
    contracts = set(unique({test.split('.')[0] for test in tests}))
    for contract_name in contracts:
        if 'setUp' in foundry.contracts[contract_name].method_by_name:
            setup_methods[contract_name] = f'{contract_name}.setUp()'

    test_methods = [
        method
        for contract in foundry.contracts.values()
        for method in contract.methods
        if (
            f'{method.contract_name}.{method.signature}' in tests
            or (method.is_setup and method.contract_name in contracts)
        )
    ]

    out_of_date_methods: set[str] = set()
    for method in test_methods:
        if not method.up_to_date(foundry.out / 'digest') or reinit:
            out_of_date_methods.add(method.qualified_name)
            _LOGGER.info(f'Method {method.qualified_name} is out of date, so it was reinitialized')
        else:
            _LOGGER.info(f'Method {method.qualified_name} not reinitialized because it is up to date')
            if not method.contract_up_to_date(foundry.out / 'digest'):
                _LOGGER.warning(
                    f'Method {method.qualified_name} not reinitialized because digest was up to date, but the contract it is a part of has changed.'
                )
        method.update_digest(foundry.out / 'digest')

    def _init_and_run_proof(_init_problem: tuple[str, str]) -> tuple[bool, list[str] | None]:
        proof_id = f'{_init_problem[0]}.{_init_problem[1]}'
        llvm_definition_dir = foundry.out / 'kompiled-llvm' if use_booster else None

        with legacy_explore(
            foundry.kevm,
            kcfg_semantics=KEVMSemantics(auto_abstract_gas=auto_abstract_gas),
            id=proof_id,
            bug_report=br,
            kore_rpc_command=kore_rpc_command,
            llvm_definition_dir=llvm_definition_dir,
            smt_timeout=smt_timeout,
            smt_retry_limit=smt_retry_limit,
            trace_rewrites=trace_rewrites,
        ) as kcfg_explore:
            contract_name, method_sig = _init_problem
            contract = foundry.contracts[contract_name]
            method = contract.method_by_sig[method_sig]
            proof = _method_to_apr_proof(
                foundry=foundry,
                contract=contract,
                method=method,
                save_directory=save_directory,
                kcfg_explore=kcfg_explore,
                reinit=(method.qualified_name in out_of_date_methods),
                simplify_init=simplify_init,
                bmc_depth=bmc_depth,
            )

            passed = kevm_prove(
                foundry.kevm,
                proof,
                kcfg_explore,
                max_depth=max_depth,
                max_iterations=max_iterations,
                break_every_step=break_every_step,
                break_on_jumpi=break_on_jumpi,
                break_on_calls=break_on_calls,
            )
            failure_log = None
            if not passed:
                failure_log = print_failure_info(proof, kcfg_explore, counterexample_info)
            return passed, failure_log

    def run_cfg_group(tests: list[str]) -> dict[str, tuple[bool, list[str] | None]]:
        def _split_test(test: str) -> tuple[str, str]:
            contract, method = test.split('.')
            return contract, method

        init_problems = [_split_test(test) for test in tests]

        _apr_proofs: list[tuple[bool, list[str] | None]]
        if workers > 1:
            with ProcessPool(ncpus=workers) as process_pool:
                _apr_proofs = process_pool.map(_init_and_run_proof, init_problems)
        else:
            _apr_proofs = []
            for init_problem in init_problems:
                _apr_proofs.append(_init_and_run_proof(init_problem))

        apr_proofs = dict(zip(tests, _apr_proofs, strict=True))
        return apr_proofs

    _LOGGER.info(f'Running setup functions in parallel: {list(setup_methods.values())}')
    results = run_cfg_group(list(setup_methods.values()))
    failed = [setup_cfg for setup_cfg, passed in results.items() if not passed]
    if failed:
        raise ValueError(f'Running setUp method failed for {len(failed)} contracts: {failed}')

    _LOGGER.info(f'Running test functions in parallel: {tests}')
    results = run_cfg_group(tests)

    return results


def foundry_show(
    foundry_root: Path,
    test: str,
    nodes: Iterable[NodeIdLike] = (),
    node_deltas: Iterable[tuple[NodeIdLike, NodeIdLike]] = (),
    to_module: bool = False,
    minimize: bool = True,
    sort_collections: bool = False,
    omit_unstable_output: bool = False,
    pending: bool = False,
    failing: bool = False,
    failure_info: bool = False,
    counterexample_info: bool = False,
    smt_timeout: int | None = None,
    smt_retry_limit: int | None = None,
) -> str:
    contract_name = test.split('.')[0]
    foundry = Foundry(foundry_root)
    proof = foundry.get_proof(test)
    assert isinstance(proof, APRProof)

    if pending:
        nodes = list(nodes) + [node.id for node in proof.pending]
    if failing:
        nodes = list(nodes) + [node.id for node in proof.failing]
    nodes = unique(nodes)

    unstable_cells = [
        '<program>',
        '<jumpDests>',
        '<pc>',
        '<gas>',
        '<code>',
    ]

    node_printer = foundry_node_printer(foundry, contract_name, proof)
    proof_show = APRProofShow(foundry.kevm, node_printer=node_printer)

    res_lines = proof_show.show(
        proof,
        nodes=nodes,
        node_deltas=node_deltas,
        to_module=to_module,
        minimize=minimize,
        sort_collections=sort_collections,
        omit_cells=(unstable_cells if omit_unstable_output else []),
    )

    if failure_info:
        with legacy_explore(
            foundry.kevm,
            kcfg_semantics=KEVMSemantics(),
            id=proof.id,
            smt_timeout=smt_timeout,
            smt_retry_limit=smt_retry_limit,
        ) as kcfg_explore:
            res_lines += print_failure_info(proof, kcfg_explore, counterexample_info)
            res_lines += Foundry.help_info()

    return '\n'.join(res_lines)


def foundry_to_dot(foundry_root: Path, test: str) -> None:
    foundry = Foundry(foundry_root)
    proofs_dir = foundry.out / 'apr_proofs'
    dump_dir = proofs_dir / 'dump'
    contract_name, test_name = test.split('.')
    proof = foundry.get_apr_proof(test)

    node_printer = foundry_node_printer(foundry, contract_name, proof)
    proof_show = APRProofShow(foundry.kevm, node_printer=node_printer)

    proof_show.dump(proof, dump_dir, dot=True)


def foundry_list(foundry_root: Path) -> list[str]:
    foundry = Foundry(foundry_root)
    apr_proofs_dir = foundry.out / 'apr_proofs'

    all_methods = [
        f'{contract.name}.{method.signature}' for contract in foundry.contracts.values() for method in contract.methods
    ]

    lines: list[str] = []
    for method in sorted(all_methods):
        if Proof.proof_data_exists(method, apr_proofs_dir):
            proof = foundry.get_proof(method)
            lines.extend(proof.summary.lines)
            lines.append('')
    if len(lines) > 0:
        lines = lines[0:-1]

    return lines


def foundry_remove_node(foundry_root: Path, test: str, node: NodeIdLike) -> None:
    foundry = Foundry(foundry_root)
    apr_proof = foundry.get_apr_proof(test)
    node_ids = apr_proof.prune_from(node)
    _LOGGER.info(f'Pruned nodes: {node_ids}')
    apr_proof.write_proof_data()


def foundry_simplify_node(
    foundry_root: Path,
    test: str,
    node: NodeIdLike,
    replace: bool = False,
    minimize: bool = True,
    sort_collections: bool = False,
    bug_report: bool = False,
    smt_timeout: int | None = None,
    smt_retry_limit: int | None = None,
    trace_rewrites: bool = False,
) -> str:
    br = BugReport(Path(f'{test}.bug_report')) if bug_report else None
    foundry = Foundry(foundry_root, bug_report=br)
    apr_proof = foundry.get_apr_proof(test)
    cterm = apr_proof.kcfg.node(node).cterm
    with legacy_explore(
        foundry.kevm,
        kcfg_semantics=KEVMSemantics(),
        id=apr_proof.id,
        bug_report=br,
        smt_timeout=smt_timeout,
        smt_retry_limit=smt_retry_limit,
        trace_rewrites=trace_rewrites,
    ) as kcfg_explore:
        new_term, _ = kcfg_explore.cterm_simplify(cterm)
    if replace:
        apr_proof.kcfg.replace_node(node, CTerm.from_kast(new_term))
        apr_proof.write_proof_data()
    res_term = minimize_term(new_term) if minimize else new_term
    return foundry.kevm.pretty_print(res_term, unalias=False, sort_collections=sort_collections)


def foundry_merge_nodes(
    foundry_root: Path,
    test: str,
    node_ids: Iterable[NodeIdLike],
    bug_report: bool = False,
    include_disjunct: bool = False,
) -> None:
    def check_cells_equal(cell: str, nodes: Iterable[KCFG.Node]) -> bool:
        nodes = list(nodes)
        if len(nodes) < 2:
            return True
        cell_value = nodes[0].cterm.cell(cell)
        for node in nodes[1:]:
            if cell_value != node.cterm.cell(cell):
                return False
        return True

    br = BugReport(Path(f'{test}.bug_report')) if bug_report else None
    foundry = Foundry(foundry_root, bug_report=br)
    proof = foundry.get_apr_proof(test)

    if not isinstance(proof, APRProof):
        raise ValueError('Specified proof is not an APRProof.')

    if len(list(node_ids)) < 2:
        raise ValueError(f'Must supply at least 2 nodes to merge, got: {node_ids}')

    nodes = [proof.kcfg.node(int(node_id)) for node_id in node_ids]
    check_cells = ['K_CELL', 'PROGRAM_CELL', 'PC_CELL', 'CALLDEPTH_CELL']
    check_cells_ne = [check_cell for check_cell in check_cells if not check_cells_equal(check_cell, nodes)]
    if check_cells_ne:
        raise ValueError(f'Nodes {node_ids} cannot be merged because they differ in: {check_cells_ne}')

    anti_unification = nodes[0].cterm
    for node in nodes[1:]:
        anti_unification, _, _ = anti_unification.anti_unify(node.cterm, keep_values=True, kdef=foundry.kevm.definition)
    new_node = proof.kcfg.create_node(anti_unification)
    for node in nodes:
        proof.kcfg.create_cover(node.id, new_node.id)

    proof.write_proof_data()

    print(f'Merged nodes {node_ids} into new node {new_node.id}.')
    print(foundry.kevm.pretty_print(new_node.cterm.kast))


def foundry_step_node(
    foundry_root: Path,
    test: str,
    node: NodeIdLike,
    repeat: int = 1,
    depth: int = 1,
    bug_report: bool = False,
    smt_timeout: int | None = None,
    smt_retry_limit: int | None = None,
    trace_rewrites: bool = False,
) -> None:
    if repeat < 1:
        raise ValueError(f'Expected positive value for --repeat, got: {repeat}')
    if depth < 1:
        raise ValueError(f'Expected positive value for --depth, got: {depth}')

    br = BugReport(Path(f'{test}.bug_report')) if bug_report else None
    foundry = Foundry(foundry_root, bug_report=br)

    apr_proof = foundry.get_apr_proof(test)
    with legacy_explore(
        foundry.kevm,
        kcfg_semantics=KEVMSemantics(),
        id=apr_proof.id,
        bug_report=br,
        smt_timeout=smt_timeout,
        smt_retry_limit=smt_retry_limit,
        trace_rewrites=trace_rewrites,
    ) as kcfg_explore:
        for _i in range(repeat):
            node = kcfg_explore.step(apr_proof.kcfg, node, apr_proof.logs, depth=depth)
            apr_proof.write_proof_data()


def foundry_section_edge(
    foundry_root: Path,
    test: str,
    edge: tuple[str, str],
    sections: int = 2,
    replace: bool = False,
    bug_report: bool = False,
    smt_timeout: int | None = None,
    smt_retry_limit: int | None = None,
    trace_rewrites: bool = False,
) -> None:
    br = BugReport(Path(f'{test}.bug_report')) if bug_report else None
    foundry = Foundry(foundry_root, bug_report=br)
    apr_proof = foundry.get_apr_proof(test)
    source_id, target_id = edge
    with legacy_explore(
        foundry.kevm,
        kcfg_semantics=KEVMSemantics(),
        id=apr_proof.id,
        bug_report=br,
        smt_timeout=smt_timeout,
        smt_retry_limit=smt_retry_limit,
        trace_rewrites=trace_rewrites,
    ) as kcfg_explore:
        kcfg_explore.section_edge(
            apr_proof.kcfg, source_id=int(source_id), target_id=int(target_id), logs=apr_proof.logs, sections=sections
        )
    apr_proof.write_proof_data()


def foundry_get_model(
    foundry_root: Path,
    test: str,
    nodes: Iterable[NodeIdLike] = (),
    pending: bool = False,
    failing: bool = False,
) -> str:
    foundry = Foundry(foundry_root)
    proof = foundry.get_proof(test)
    assert isinstance(proof, APRProof)

    if not nodes:
        _LOGGER.warning('Node ID is not provided. Displaying models of failing and pending nodes:')
        failing = pending = True

    if pending:
        nodes = list(nodes) + [node.id for node in proof.pending]
    if failing:
        nodes = list(nodes) + [node.id for node in proof.failing]
    nodes = unique(nodes)

    res_lines = []

    with legacy_explore(foundry.kevm, kcfg_semantics=KEVMSemantics(), id=proof.id) as kcfg_explore:
        for node_id in nodes:
            res_lines.append('')
            res_lines.append(f'Node id: {node_id}')
            node = proof.kcfg.node(node_id)
            res_lines.extend(print_model(node, kcfg_explore))

    return '\n'.join(res_lines)


def _write_cfg(cfg: KCFG, path: Path) -> None:
    path.write_text(cfg.to_json())
    _LOGGER.info(f'Updated CFG file: {path}')


def _foundry_to_contract_def(
    empty_config: KInner,
    contracts: Iterable[Contract],
    requires: Iterable[str],
) -> KDefinition:
    modules = [contract_to_main_module(contract, empty_config, imports=['FOUNDRY']) for contract in contracts]
    # First module is chosen as main module arbitrarily, since the contract definition is just a set of
    # contract modules.
    main_module = Contract.contract_to_module_name(list(contracts)[0].name_upper)

    return KDefinition(
        main_module,
        modules,
        requires=(KRequire(req) for req in list(requires)),
    )


def _foundry_to_main_def(
    main_module: str,
    contracts: Iterable[Contract],
    empty_config: KInner,
    requires: Iterable[str],
    imports: dict[str, list[str]],
) -> KDefinition:
    modules = [
        contract_to_verification_module(contract, empty_config, imports=imports[contract.name])
        for contract in contracts
    ]
    _main_module = KFlatModule(
        main_module,
        imports=(KImport(mname) for mname in [_m.name for _m in modules]),
    )

    return KDefinition(
        main_module,
        [_main_module] + modules,
        requires=(KRequire(req) for req in list(requires)),
    )


def _method_to_apr_proof(
    foundry: Foundry,
    contract: Contract,
    method: Contract.Method,
    save_directory: Path,
    kcfg_explore: KCFGExplore,
    reinit: bool = False,
    simplify_init: bool = True,
    bmc_depth: int | None = None,
) -> APRProof | APRBMCProof:
    contract_name = contract.name
    method_sig = method.signature
    test = f'{contract_name}.{method_sig}'
    proof_digest = foundry.proof_digest(contract_name, method_sig)
    if Proof.proof_data_exists(proof_digest, save_directory) and not reinit:
        apr_proof = foundry.get_apr_proof(test)
        assert isinstance(apr_proof, APRProof)
    else:
        _LOGGER.info(f'Initializing KCFG for test: {test}')

        setup_digest = None
        if method_sig != 'setUp()' and 'setUp' in contract.method_by_name:
            setup_digest = foundry.proof_digest(contract_name, 'setUp()')
            _LOGGER.info(f'Using setUp method for test: {test}')

        empty_config = foundry.kevm.definition.empty_config(GENERATED_TOP_CELL)
        kcfg, init_node_id, target_node_id = _method_to_cfg(
            empty_config, contract, method, save_directory, init_state=setup_digest
        )

        _LOGGER.info(f'Expanding macros in initial state for test: {test}')
        init_term = kcfg.node(init_node_id).cterm.kast
        init_term = KDefinition__expand_macros(foundry.kevm.definition, init_term)
        init_cterm = CTerm.from_kast(init_term)
        _LOGGER.info(f'Computing definedness constraint for test: {test}')
        init_cterm = kcfg_explore.cterm_assume_defined(init_cterm)
        kcfg.replace_node(init_node_id, init_cterm)

        _LOGGER.info(f'Expanding macros in target state for test: {test}')
        target_term = kcfg.node(target_node_id).cterm.kast
        target_term = KDefinition__expand_macros(foundry.kevm.definition, target_term)
        target_cterm = CTerm.from_kast(target_term)
        kcfg.replace_node(target_node_id, target_cterm)

        if simplify_init:
            _LOGGER.info(f'Simplifying KCFG for test: {test}')
            kcfg_explore.simplify(kcfg, {})
        if bmc_depth is not None:
            apr_proof = APRBMCProof(
                proof_digest, kcfg, init_node_id, target_node_id, {}, bmc_depth, proof_dir=save_directory
            )
        else:
            apr_proof = APRProof(proof_digest, kcfg, init_node_id, target_node_id, {}, proof_dir=save_directory)

    apr_proof.write_proof_data()
    return apr_proof


def _method_to_cfg(
    empty_config: KInner,
    contract: Contract,
    method: Contract.Method,
    kcfgs_dir: Path,
    init_state: str | None = None,
) -> tuple[KCFG, NodeIdLike, NodeIdLike]:
    calldata = method.calldata_cell(contract)
    callvalue = method.callvalue_cell
    init_cterm = _init_cterm(
        empty_config,
        contract.name,
        kcfgs_dir,
        calldata=calldata,
        callvalue=callvalue,
        init_state=init_state,
    )
    is_test = method.name.startswith('test')
    failing = method.name.startswith('testFail')
    final_cterm = _final_cterm(empty_config, contract.name, failing=failing, is_test=is_test)

    cfg = KCFG()
    init_node = cfg.create_node(init_cterm)
    target_node = cfg.create_node(final_cterm)

    return cfg, init_node.id, target_node.id


def get_final_accounts_cell(proof_digest: str, proof_dir: Path) -> tuple[KInner, Iterable[KInner]]:
    apr_proof = APRProof.read_proof_data(proof_dir, proof_digest)
    target = apr_proof.kcfg.node(apr_proof.target)
    target_states = apr_proof.kcfg.covers(target_id=target.id)
    if len(target_states) == 0:
        raise ValueError(
            f'setUp() function for {apr_proof.id} did not reach the end of execution. Maybe --max-iterations is too low?'
        )
    if len(target_states) > 1:
        raise ValueError(f'setUp() function for {apr_proof.id} branched and has {len(target_states)} target states.')
    cterm = single(target_states).source.cterm
    acct_cell = cterm.cell('ACCOUNTS_CELL')
    fvars = free_vars(acct_cell)
    acct_cons = constraints_for(fvars, cterm.constraints)
    return (acct_cell, acct_cons)


def _init_cterm(
    empty_config: KInner,
    contract_name: str,
    kcfgs_dir: Path,
    *,
    calldata: KInner | None = None,
    callvalue: KInner | None = None,
    init_state: str | None = None,
) -> CTerm:
    program = KEVM.bin_runtime(KApply(f'contract_{contract_name}'))
    account_cell = KEVM.account_cell(
        Foundry.address_TEST_CONTRACT(),
        intToken(0),
        program,
        KApply('.Map'),
        KApply('.Map'),
        intToken(1),
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
        'LOG_CELL': KApply('.List'),
        'ID_CELL': Foundry.address_TEST_CONTRACT(),
        'CALLER_CELL': KVariable('CALLER_ID'),
        'ACCESSEDACCOUNTS_CELL': KApply('.Set'),
        'ACCESSEDSTORAGE_CELL': KApply('.Map'),
        'INTERIMSTATES_CELL': KApply('.List'),
        'LOCALMEM_CELL': KApply('.Bytes_BYTES-HOOKED_Bytes'),
        'PREVCALLER_CELL': KApply('.Account_EVM-TYPES_Account'),
        'PREVORIGIN_CELL': KApply('.Account_EVM-TYPES_Account'),
        'NEWCALLER_CELL': KApply('.Account_EVM-TYPES_Account'),
        'NEWORIGIN_CELL': KApply('.Account_EVM-TYPES_Account'),
        'ACTIVE_CELL': FALSE,
        'STATIC_CELL': FALSE,
        'MEMORYUSED_CELL': intToken(0),
        'WORDSTACK_CELL': KApply('.WordStack_EVM-TYPES_WordStack'),
        'PC_CELL': intToken(0),
        'GAS_CELL': intToken(9223372036854775807),
        'K_CELL': KSequence([KEVM.sharp_execute(), KVariable('CONTINUATION')]),
        'ACCOUNTS_CELL': KEVM.accounts(
            [
                account_cell,  # test contract address
                Foundry.account_CHEATCODE_ADDRESS(KApply('.Map')),
            ]
        ),
        'SINGLECALL_CELL': FALSE,
        'ISREVERTEXPECTED_CELL': FALSE,
        'ISOPCODEEXPECTED_CELL': FALSE,
        'EXPECTEDADDRESS_CELL': KApply('.Account_EVM-TYPES_Account'),
        'EXPECTEDVALUE_CELL': intToken(0),
        'EXPECTEDDATA_CELL': KApply('.Bytes_BYTES-HOOKED_Bytes'),
        'OPCODETYPE_CELL': KApply('.OpcodeType_FOUNDRY-CHEAT-CODES_OpcodeType'),
        'RECORDEVENT_CELL': FALSE,
        'ISEVENTEXPECTED_CELL': FALSE,
        'ISCALLWHITELISTACTIVE_CELL': FALSE,
        'ISSTORAGEWHITELISTACTIVE_CELL': FALSE,
        'ADDRESSSET_CELL': KApply('.Set'),
        'STORAGESLOTSET_CELL': KApply('.Set'),
    }

    constraints = None
    if init_state:
        accts, constraints = get_final_accounts_cell(init_state, kcfgs_dir)
        init_subst['ACCOUNTS_CELL'] = accts

    if calldata is not None:
        init_subst['CALLDATA_CELL'] = calldata

    if callvalue is not None:
        init_subst['CALLVALUE_CELL'] = callvalue

    init_term = Subst(init_subst)(empty_config)
    init_cterm = CTerm.from_kast(init_term)
    init_cterm = KEVM.add_invariant(init_cterm)
    if constraints is None:
        return init_cterm
    else:
        for constraint in constraints:
            init_cterm = init_cterm.add_constraint(constraint)
        return init_cterm


def _final_cterm(empty_config: KInner, contract_name: str, *, failing: bool, is_test: bool = True) -> CTerm:
    final_term = _final_term(empty_config, contract_name)
    dst_failed_post = KEVM.lookup(KVariable('CHEATCODE_STORAGE_FINAL'), Foundry.loc_FOUNDRY_FAILED())
    foundry_success = Foundry.success(
        KVariable('STATUSCODE_FINAL'),
        dst_failed_post,
        KVariable('ISREVERTEXPECTED_FINAL'),
        KVariable('ISOPCODEEXPECTED_FINAL'),
        KVariable('RECORDEVENT_FINAL'),
        KVariable('ISEVENTEXPECTED_FINAL'),
    )
    final_cterm = CTerm.from_kast(final_term)
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
        KVariable('ACCT_BALANCE_FINAL'),
        program,
        KVariable('ACCT_STORAGE_FINAL'),
        KVariable('ACCT_ORIGSTORAGE_FINAL'),
        KVariable('ACCT_NONCE_FINAL'),
    )
    final_subst = {
        'K_CELL': KSequence([KEVM.halt(), KVariable('CONTINUATION')]),
        'STATUSCODE_CELL': KVariable('STATUSCODE_FINAL'),
        'ID_CELL': Foundry.address_TEST_CONTRACT(),
        'ACCOUNTS_CELL': KEVM.accounts(
            [
                post_account_cell,  # test contract address
                Foundry.account_CHEATCODE_ADDRESS(KVariable('CHEATCODE_STORAGE_FINAL')),
                KVariable('ACCOUNTS_FINAL'),
            ]
        ),
        'ISREVERTEXPECTED_CELL': KVariable('ISREVERTEXPECTED_FINAL'),
        'ISOPCODEEXPECTED_CELL': KVariable('ISOPCODEEXPECTED_FINAL'),
        'RECORDEVENT_CELL': KVariable('RECORDEVENT_FINAL'),
        'ISEVENTEXPECTED_CELL': KVariable('ISEVENTEXPECTED_FINAL'),
        'ISCALLWHITELISTACTIVE_CELL': KVariable('ISCALLWHITELISTACTIVE_FINAL'),
        'ISSTORAGEWHITELISTACTIVE_CELL': KVariable('ISSTORAGEWHITELISTACTIVE_FINAL'),
        'ADDRESSSET_CELL': KVariable('ADDRESSSET_FINAL'),
        'STORAGESLOTSET_CELL': KVariable('STORAGESLOTSET_FINAL'),
    }
    return abstract_cell_vars(
        Subst(final_subst)(empty_config),
        [
            KVariable('STATUSCODE_FINAL'),
            KVariable('ACCOUNTS_FINAL'),
            KVariable('ISREVERTEXPECTED_FINAL'),
            KVariable('ISOPCODEEXPECTED_FINAL'),
            KVariable('RECORDEVENT_FINAL'),
            KVariable('ISEVENTEXPECTED_FINAL'),
            KVariable('ISCALLWHITELISTACTIVE_FINAL'),
            KVariable('ISSTORAGEWHITELISTACTIVE_FINAL'),
            KVariable('ADDRESSSET_FINAL'),
            KVariable('STORAGESLOTSET_FINAL'),
        ],
    )


class FoundryNodePrinter(KEVMNodePrinter):
    foundry: Foundry
    contract_name: str

    def __init__(self, foundry: Foundry, contract_name: str):
        KEVMNodePrinter.__init__(self, foundry.kevm)
        self.foundry = foundry
        self.contract_name = contract_name

    def print_node(self, kcfg: KCFG, node: KCFG.Node) -> list[str]:
        ret_strs = super().print_node(kcfg, node)
        _pc = node.cterm.cell('PC_CELL')
        if type(_pc) is KToken and _pc.sort == INT:
            srcmap_data = self.foundry.srcmap_data(self.contract_name, int(_pc.token))
            if srcmap_data is not None:
                path, start, end = srcmap_data
                ret_strs.append(f'src: {str(path)}:{start}:{end}')
        return ret_strs


class FoundryAPRNodePrinter(FoundryNodePrinter, APRProofNodePrinter):
    def __init__(self, foundry: Foundry, contract_name: str, proof: APRProof):
        FoundryNodePrinter.__init__(self, foundry, contract_name)
        APRProofNodePrinter.__init__(self, proof, foundry.kevm)


class FoundryAPRBMCNodePrinter(FoundryNodePrinter, APRBMCProofNodePrinter):
    def __init__(self, foundry: Foundry, contract_name: str, proof: APRBMCProof):
        FoundryNodePrinter.__init__(self, foundry, contract_name)
        APRBMCProofNodePrinter.__init__(self, proof, foundry.kevm)


def foundry_node_printer(foundry: Foundry, contract_name: str, proof: APRProof) -> NodePrinter:
    if type(proof) is APRBMCProof:
        return FoundryAPRBMCNodePrinter(foundry, contract_name, proof)
    if type(proof) is APRProof:
        return FoundryAPRNodePrinter(foundry, contract_name, proof)
    raise ValueError(f'Cannot build NodePrinter for proof type: {type(proof)}')
