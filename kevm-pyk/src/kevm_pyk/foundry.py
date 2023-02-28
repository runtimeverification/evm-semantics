import json
import logging
import sys
from pathlib import Path
from typing import Dict, Final, Iterable, List, Optional, Tuple

from pyk.cli_utils import BugReport
from pyk.cterm import CTerm, build_claim, build_rule
from pyk.kast.inner import KApply, KInner, KLabel, KRewrite, KSequence, KSort, KToken, KVariable, Subst, build_assoc
from pyk.kast.manip import get_cell, minimize_term, push_down_rewrites
from pyk.kast.outer import KDefinition, KFlatModule, KImport, KRequire, KRuleLike
from pyk.kcfg import KCFG, KCFGExplore
from pyk.ktool.kompile import KompileBackend
from pyk.prelude.bytes import bytesToken
from pyk.prelude.k import GENERATED_TOP_CELL
from pyk.prelude.kbool import FALSE, notBool
from pyk.prelude.kint import intToken
from pyk.prelude.ml import mlEqualsTrue, mlTop
from pyk.utils import shorten_hashes

from .kevm import KEVM
from .solc_to_k import Contract, contract_to_main_module
from .utils import KDefinition__expand_macros, abstract_cell_vars, find_free_port, parallel_kcfg_explore

_LOGGER: Final = logging.getLogger(__name__)


class Foundry(KEVM):
    def __init__(
        self,
        definition_dir: Path,
        main_file: Optional[Path] = None,
        use_directory: Optional[Path] = None,
        profile: bool = False,
        extra_unparsing_modules: Iterable[KFlatModule] = (),
        bug_report: Optional[BugReport] = None,
    ) -> None:
        # copied from KEVM class and adapted to inherit KPrint instead
        KEVM.__init__(
            self,
            definition_dir,
            main_file=main_file,
            use_directory=use_directory,
            profile=profile,
            extra_unparsing_modules=extra_unparsing_modules,
            bug_report=bug_report,
        )

    class Sorts:
        FOUNDRY_CELL: Final = KSort('FoundryCell')

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
        return intToken(0xB4C79DAB8F259C7AEE6E5B2AA729821864227E84)

    @staticmethod
    def account_TEST_CONTRACT_ADDRESS() -> KApply:  # noqa: N802
        return KEVM.account_cell(
            Foundry.address_TEST_CONTRACT(),
            intToken(0),
            KVariable('TEST_CODE'),
            KApply('.Map'),
            KApply('.Map'),
            intToken(0),
        )

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
            bytesToken('\x00'),
            store_var,
            KApply('.Map'),
            intToken(0),
        )


def foundry_kompile(
    definition_dir: Path,
    profile: bool,
    foundry_out: Path,
    includes: Iterable[str],
    md_selector: Optional[str],
    regen: bool = False,
    rekompile: bool = False,
    requires: Iterable[str] = (),
    imports: Iterable[str] = (),
    ccopts: Iterable[str] = (),
    llvm_kompile: bool = True,
    debug: bool = False,
) -> None:
    main_module = 'FOUNDRY-MAIN'
    syntax_module = 'FOUNDRY-MAIN'
    foundry_definition_dir = foundry_out / 'kompiled'
    foundry_main_file = foundry_definition_dir / 'foundry.k'
    kompiled_timestamp = foundry_definition_dir / 'timestamp'
    srcmap_dir = foundry_out / 'srcmaps'
    requires = ['foundry.md'] + list(requires)
    imports = ['FOUNDRY'] + list(imports)

    if not foundry_definition_dir.exists():
        foundry_definition_dir.mkdir()
    if not srcmap_dir.exists():
        srcmap_dir.mkdir()

    json_paths = _contract_json_paths(foundry_out)
    contracts = [_contract_from_json(json_path) for json_path in json_paths]

    for c in contracts:
        srcmap_file = srcmap_dir / f'{c.name}.json'
        with open(srcmap_file, 'w') as smf:
            smf.write(json.dumps(c.srcmap))
            _LOGGER.info(f'Wrote source map: {srcmap_file}')

    foundry = Foundry(definition_dir, profile=profile)
    empty_config = foundry.definition.empty_config(Foundry.Sorts.FOUNDRY_CELL)

    if regen or not foundry_main_file.exists():
        bin_runtime_definition = _foundry_to_bin_runtime(
            empty_config=empty_config,
            contracts=contracts,
            main_module=main_module,
            requires=requires,
            imports=imports,
        )
        with open(foundry_main_file, 'w') as fmf:
            _LOGGER.info(f'Writing file: {foundry_main_file}')
            _foundry = Foundry(
                definition_dir=definition_dir,
                extra_unparsing_modules=bin_runtime_definition.modules,
            )
            fmf.write(_foundry.pretty_print(bin_runtime_definition) + '\n')

    if regen or rekompile or not kompiled_timestamp.exists():
        _LOGGER.info(f'Kompiling definition: {foundry_main_file}')
        KEVM.kompile(
            foundry_definition_dir,
            KompileBackend.HASKELL,
            foundry_main_file,
            emit_json=True,
            includes=includes,
            main_module_name=main_module,
            syntax_module_name=syntax_module,
            md_selector=md_selector,
            profile=profile,
            debug=debug,
            ccopts=ccopts,
            llvm_kompile=llvm_kompile,
        )


def foundry_prove(
    profile: bool,
    foundry_out: Path,
    max_depth: int = 100,
    max_iterations: Optional[int] = None,
    reinit: bool = False,
    tests: Iterable[str] = (),
    exclude_tests: Iterable[str] = (),
    workers: int = 1,
    simplify_init: bool = True,
    break_every_step: bool = False,
    break_on_calls: bool = True,
    implication_every_block: bool = True,
    rpc_base_port: Optional[int] = None,
    bug_report: bool = False,
) -> None:
    if workers <= 0:
        raise ValueError(f'Must have at least one worker, found: --workers {workers}')
    if max_iterations is not None and max_iterations < 0:
        raise ValueError(f'Must have a non-negative number of iterations, found: --max-iterations {max_iterations}')
    definition_dir = foundry_out / 'kompiled'
    use_directory = foundry_out / 'specs'
    use_directory.mkdir(parents=True, exist_ok=True)
    kcfgs_dir = foundry_out / 'kcfgs'
    if not kcfgs_dir.exists():
        kcfgs_dir.mkdir()
    br = BugReport(foundry_out / 'bug_report') if bug_report else None
    foundry = Foundry(definition_dir, profile=profile, use_directory=use_directory, bug_report=br)

    json_paths = _contract_json_paths(foundry_out)
    contracts = [_contract_from_json(json_path) for json_path in json_paths]
    all_tests = [
        f'{contract.name}.{method.name}'
        for contract in contracts
        if contract.name.endswith('Test')
        for method in contract.methods
        if method.name.startswith('test')
    ]
    all_non_tests = [
        f'{contract.name}.{method.name}'
        for contract in contracts
        for method in contract.methods
        if f'{contract.name}.{method.name}' not in all_tests
    ]
    unfound_tests: List[str] = []
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
    _LOGGER.info(f'Running tests: {tests}')
    if unfound_tests:
        raise ValueError(f'Test identifiers not found: {unfound_tests}')

    kcfgs: Dict[str, KCFG] = {}
    for test in tests:
        kcfg = KCFGExplore.read_cfg(test, kcfgs_dir)
        if kcfg is not None and not reinit:
            kcfgs[test] = kcfg
        else:
            _LOGGER.info(f'Initializing KCFG for test: {test}')
            contract_name, method_name = test.split('.')
            contract = [c for c in contracts if c.name == contract_name][0]
            method = [m for m in contract.methods if m.name == method_name][0]
            empty_config = foundry.definition.empty_config(GENERATED_TOP_CELL)
            kcfg = _method_to_cfg(empty_config, contract, method)
            init_term = kcfg.get_unique_init().cterm.kast
            target_term = kcfg.get_unique_target().cterm.kast
            _LOGGER.info(f'Expanding macros in initial state for test: {test}')
            init_term = KDefinition__expand_macros(foundry.definition, init_term)
            init_cterm = KEVM.add_invariant(CTerm(init_term))
            _LOGGER.info(f'Expanding macros in target state for test: {test}')
            target_term = KDefinition__expand_macros(foundry.definition, target_term)
            target_cterm = KEVM.add_invariant(CTerm(target_term))
            kcfg.replace_node(kcfg.get_unique_init().id, init_cterm)
            kcfg.replace_node(kcfg.get_unique_target().id, target_cterm)
            if simplify_init:
                with KCFGExplore(foundry, port=find_free_port(), bug_report=br) as kcfg_explore:
                    kcfg = kcfg_explore.simplify(test, kcfg)
            kcfgs[test] = kcfg
            KCFGExplore.write_cfg(test, kcfgs_dir, kcfg)

    results = parallel_kcfg_explore(
        foundry,
        kcfgs,
        save_directory=kcfgs_dir,
        max_depth=max_depth,
        max_iterations=max_iterations,
        workers=workers,
        break_every_step=break_every_step,
        break_on_calls=break_on_calls,
        implication_every_block=implication_every_block,
        rpc_base_port=rpc_base_port,
        is_terminal=KEVM.is_terminal,
        extract_branches=KEVM.extract_branches,
        bug_report=br,
    )
    failed = 0
    for pid, r in results.items():
        if r:
            print(f'PROOF PASSED: {pid}')
        else:
            failed += 1
            print(f'PROOF FAILED: {pid}')
    sys.exit(failed)


def foundry_show(
    profile: bool,
    foundry_out: Path,
    test: str,
    nodes: Iterable[str] = (),
    node_deltas: Iterable[Tuple[str, str]] = (),
    to_module: bool = False,
    minimize: bool = True,
) -> None:
    definition_dir = foundry_out / 'kompiled'
    use_directory = foundry_out / 'specs'
    use_directory.mkdir(parents=True, exist_ok=True)
    kcfgs_dir = foundry_out / 'kcfgs'
    contract = test.split('.')[0]
    srcmap_dir = foundry_out / 'srcmaps'
    srcmap_file = srcmap_dir / f'{contract}.json'
    foundry = Foundry(definition_dir, profile=profile, use_directory=use_directory)
    srcmap: Optional[Dict[int, str]] = None
    if srcmap_file.exists():
        with open(srcmap_file, 'r') as sm:
            srcmap = {int(k): v for k, v in json.loads(sm.read()).items()}

    def _node_pretty(_ct: CTerm) -> List[str]:
        k_cell = foundry.pretty_print(get_cell(_ct.config, 'K_CELL')).replace('\n', ' ')
        if len(k_cell) > 80:
            k_cell = k_cell[0:80] + ' ...'
        k_str = f'k: {k_cell}'
        calldepth_str = f'callDepth: {foundry.pretty_print(get_cell(_ct.config, "CALLDEPTH_CELL"))}'
        statuscode_str = f'statusCode: {foundry.pretty_print(get_cell(_ct.config, "STATUSCODE_CELL"))}'
        _pc = get_cell(_ct.config, 'PC_CELL')
        pc_str = f'pc: {foundry.pretty_print(_pc)}'
        ret_strs = [k_str, calldepth_str, statuscode_str, pc_str]
        if type(_pc) is KToken and srcmap is not None:
            pc = int(_pc.token)
            if pc in srcmap:
                ret_strs.append(f'srcmap: {srcmap[pc]}')
            else:
                _LOGGER.warning(f'pc not found in srcmap: {pc}')
        return ret_strs

    kcfg = KCFGExplore.read_cfg(test, kcfgs_dir)
    if kcfg is None:
        raise ValueError(f'Could not load CFG {test} from {kcfgs_dir}')
    list(map(print, kcfg.pretty(foundry, minimize=minimize, node_printer=_node_pretty)))

    for node_id in nodes:
        kast = kcfg.node(node_id).cterm.kast
        if minimize:
            kast = minimize_term(kast)
        print(f'\n\nNode {node_id}:\n\n{foundry.pretty_print(kast)}\n')

    for node_id_1, node_id_2 in node_deltas:
        config_1 = kcfg.node(node_id_1).cterm.config
        config_2 = kcfg.node(node_id_2).cterm.config
        config_delta = push_down_rewrites(KRewrite(config_1, config_2))
        if minimize:
            config_delta = minimize_term(config_delta)
        print(f'\n\nState Delta {node_id_1} => {node_id_2}:\n\n{foundry.pretty_print(config_delta)}\n')

    if to_module:

        def to_rule(edge: KCFG.Edge, *, claim: bool = False) -> KRuleLike:
            sentence_id = f'BASIC-BLOCK-{edge.source.id}-TO-{edge.target.id}'
            init_cterm = CTerm(edge.source.cterm.config)
            for c in edge.source.cterm.constraints:
                assert type(c) is KApply
                if c.label.name == '#Ceil':
                    _LOGGER.warning(f'Ignoring Ceil condition: {c}')
                else:
                    init_cterm.add_constraint(c)
            target_cterm = CTerm(edge.target.cterm.config)
            for c in edge.source.cterm.constraints:
                assert type(c) is KApply
                if c.label.name == '#Ceil':
                    _LOGGER.warning(f'Ignoring Ceil condition: {c}')
                else:
                    target_cterm.add_constraint(c)
            rule: KRuleLike
            if claim:
                rule, _ = build_claim(sentence_id, init_cterm.add_constraint(edge.condition), target_cterm)
            else:
                rule, _ = build_rule(sentence_id, init_cterm.add_constraint(edge.condition), target_cterm, priority=35)
            return rule

        rules = [to_rule(e) for e in kcfg.edges() if e.depth > 0]
        claims = [to_rule(KCFG.Edge(nd, kcfg.get_unique_target(), mlTop(), -1), claim=True) for nd in kcfg.frontier]
        new_module = KFlatModule('SUMMARY', rules + claims)
        print(foundry.pretty_print(new_module) + '\n')


def foundry_list(
    profile: bool,
    foundry_out: Path,
    details: bool = True,
) -> None:
    kcfgs_dir = foundry_out / 'kcfgs'
    pattern = '*.json'
    paths = kcfgs_dir.glob(pattern)
    for kcfg_file in paths:
        kcfg_json = json.loads(Path(kcfg_file).read_text())
        cfg_id = kcfg_json['cfgid']
        kcfg = KCFG.from_dict(kcfg_json)
        total_nodes = len(kcfg.nodes)
        frontier_nodes = len(kcfg.frontier)
        stuck_nodes = len(kcfg.stuck)
        proven = 'failed'
        if stuck_nodes == 0:
            proven = 'pending'
            if frontier_nodes == 0:
                proven = 'passed'
        print(f'{cfg_id}: {proven}')
        if details:
            print(f'    path: {kcfg_file}')
            print(f'    nodes: {total_nodes}')
            print(f'    frontier: {frontier_nodes}')
            print(f'    stuck: {stuck_nodes}')
            print()


def foundry_remove_node(foundry_out: Path, test: str, node: str, profile: bool) -> None:
    kcfgs_dir = foundry_out / 'kcfgs'
    kcfg = KCFGExplore.read_cfg(test, kcfgs_dir)
    if kcfg is None:
        raise ValueError(f'Could not load CFG {test} from {kcfgs_dir}')
    for _node in kcfg.reachable_nodes(node, traverse_covers=True):
        if not kcfg.is_target(_node.id):
            _LOGGER.info(f'Removing node: {shorten_hashes(_node.id)}')
            kcfg.remove_node(_node.id)
    KCFGExplore.write_cfg(test, kcfgs_dir, kcfg)


def foundry_simplify_node(
    foundry_out: Path,
    test: str,
    node: str,
    profile: bool,
    replace: bool = False,
    minimize: bool = True,
    bug_report: bool = False,
) -> None:
    definition_dir = foundry_out / 'kompiled'
    use_directory = foundry_out / 'specs'
    kcfgs_dir = foundry_out / 'kcfgs'
    use_directory.mkdir(parents=True, exist_ok=True)
    br = BugReport(Path(f'{test}.bug_report')) if bug_report else None
    foundry = Foundry(definition_dir, profile=profile, use_directory=use_directory, bug_report=br)
    kcfg = KCFGExplore.read_cfg(test, kcfgs_dir)
    if kcfg is None:
        raise ValueError(f'Could not load CFG {test} from {kcfgs_dir}')
    cterm = kcfg.node(node).cterm
    port = find_free_port()
    with KCFGExplore(foundry, port=port, bug_report=br) as kcfg_explore:
        new_term = kcfg_explore.cterm_simplify(cterm)
    new_term_minimized = new_term if not minimize else minimize_term(new_term)
    print(f'Simplified:\n{foundry.pretty_print(new_term_minimized)}')
    if replace:
        kcfg.replace_node(node, CTerm(new_term))
        KCFGExplore.write_cfg(test, kcfgs_dir, kcfg)


def foundry_step_node(
    foundry_out: Path,
    test: str,
    node: str,
    profile: bool,
    repeat: int = 1,
    depth: int = 1,
    minimize: bool = True,
    bug_report: bool = False,
) -> None:
    if repeat < 1:
        raise ValueError(f'Expected positive value for --repeat, got: {repeat}')
    if depth < 1:
        raise ValueError(f'Expected positive value for --depth, got: {depth}')
    definition_dir = foundry_out / 'kompiled'
    use_directory = foundry_out / 'specs'
    kcfgs_dir = foundry_out / 'kcfgs'
    use_directory.mkdir(parents=True, exist_ok=True)
    br = BugReport(Path(f'{test}.bug_report')) if bug_report else None
    foundry = Foundry(definition_dir, profile=profile, use_directory=use_directory, bug_report=br)
    kcfg = KCFGExplore.read_cfg(test, kcfgs_dir)
    if kcfg is None:
        raise ValueError(f'Could not load CFG {test} from {kcfgs_dir}')
    port = find_free_port()
    with KCFGExplore(foundry, port=port, bug_report=br) as kcfg_explore:
        for _i in range(repeat):
            kcfg, node = kcfg_explore.step(test, kcfg, node, depth=depth)
            KCFGExplore.write_cfg(test, kcfgs_dir, kcfg)


def foundry_section_edge(
    foundry_out: Path,
    test: str,
    edge: Tuple[str, str],
    profile: bool,
    sections: int = 2,
    replace: bool = False,
    minimize: bool = True,
    bug_report: bool = False,
) -> None:
    definition_dir = foundry_out / 'kompiled'
    use_directory = foundry_out / 'specs'
    kcfgs_dir = foundry_out / 'kcfgs'
    use_directory.mkdir(parents=True, exist_ok=True)
    br = BugReport(Path(f'{test}.bug_report')) if bug_report else None
    foundry = Foundry(definition_dir, profile=profile, use_directory=use_directory, bug_report=br)
    kcfg = KCFGExplore.read_cfg(test, kcfgs_dir)
    if kcfg is None:
        raise ValueError(f'Could not load CFG {test} from {kcfgs_dir}')
    port = find_free_port()
    source_id, target_id = edge
    with KCFGExplore(foundry, port=port, bug_report=br) as kcfg_explore:
        kcfg, _ = kcfg_explore.section_edge(test, kcfg, source_id=source_id, target_id=target_id, sections=sections)
    KCFGExplore.write_cfg(test, kcfgs_dir, kcfg)


def _write_cfg(cfg: KCFG, path: Path) -> None:
    path.write_text(cfg.to_json())
    _LOGGER.info(f'Updated CFG file: {path}')


def _contract_json_paths(foundry_out: Path) -> List[str]:
    pattern = '*.sol/*.json'
    paths = foundry_out.glob(pattern)
    json_paths = [str(path) for path in paths]
    json_paths = [json_path for json_path in json_paths if not json_path.endswith('.metadata.json')]
    json_paths = sorted(json_paths)  # Must sort to get consistent output order on different platforms
    return json_paths


def _contract_from_json(json_path: str) -> Contract:
    _LOGGER.info(f'Processing contract file: {json_path}')
    with open(json_path, 'r') as json_file:
        contract_json = json.loads(json_file.read())
    contract_name = json_path.split('/')[-1]
    contract_name = contract_name[0:-5] if contract_name.endswith('.json') else contract_name
    return Contract(contract_name, contract_json, foundry=True)


def _foundry_to_bin_runtime(
    empty_config: KInner,
    contracts: Iterable[Contract],
    main_module: Optional[str],
    requires: Iterable[str],
    imports: Iterable[str],
) -> KDefinition:
    modules = []
    for contract in contracts:
        module = contract_to_main_module(contract, empty_config, imports=imports)
        _LOGGER.info(f'Produced contract module: {module.name}')
        modules.append(module)
    _main_module = KFlatModule(
        main_module if main_module else 'MAIN',
        imports=(KImport(mname) for mname in [_m.name for _m in modules] + list(imports)),
    )
    modules.append(_main_module)

    bin_runtime_definition = KDefinition(
        _main_module.name,
        modules,
        requires=(KRequire(req) for req in list(requires)),
    )

    return bin_runtime_definition


def _method_to_cfg(empty_config: KInner, contract: Contract, method: Contract.Method) -> KCFG:
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
    dst_failed_prev = KEVM.lookup(KVariable('CHEATCODE_STORAGE'), Foundry.loc_FOUNDRY_FAILED())
    init_cterm = CTerm(init_term)
    init_cterm = KEVM.add_invariant(init_cterm)
    init_cterm = init_cterm.add_constraint(mlEqualsTrue(KApply('_==Int_', [dst_failed_prev, intToken(0)])))
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
        'LOG_CELL': KApply('.List'),
        'ID_CELL': Foundry.address_TEST_CONTRACT(),
        'CALLER_CELL': KVariable('CALLER_ID'),
        'ACCESSEDACCOUNTS_CELL': KApply('.Set'),
        'ACCESSEDSTORAGE_CELL': KApply('.Map'),
        'INTERIMSTATES_CELL': KApply('.List'),
        'ACTIVEACCOUNTS_CELL': build_assoc(
            KApply('.Set'),
            KLabel('_Set_'),
            map(
                KLabel('SetItem'),
                [
                    Foundry.address_TEST_CONTRACT(),
                    Foundry.address_CHEATCODE(),
                ],
            ),
        ),
        'LOCALMEM_CELL': KApply('.Memory_EVM-TYPES_Memory'),
        'PREVCALLER_CELL': KApply('.Account_EVM-TYPES_Account'),
        'PREVORIGIN_CELL': KApply('.Account_EVM-TYPES_Account'),
        'NEWCALLER_CELL': KApply('.Account_EVM-TYPES_Account'),
        'NEWORIGIN_CELL': KApply('.Account_EVM-TYPES_Account'),
        'ACTIVE_CELL': FALSE,
        'STATIC_CELL': FALSE,
        'MEMORYUSED_CELL': intToken(0),
        'WORDSTACK_CELL': KApply('.WordStack_EVM-TYPES_WordStack'),
        'PC_CELL': intToken(0),
        'GAS_CELL': KEVM.inf_gas(KVariable('VGAS')),
        'K_CELL': KSequence([KEVM.sharp_execute(), KVariable('CONTINUATION')]),
        'ACCOUNTS_CELL': KEVM.accounts(
            [
                account_cell,  # test contract address
                Foundry.account_CHEATCODE_ADDRESS(KVariable('CHEATCODE_STORAGE')),
                KVariable('ACCOUNTS_INIT'),
            ]
        ),
        'SINGLECALL_CELL': FALSE,
        'ISREVERTEXPECTED_CELL': FALSE,
        'ISOPCODEEXPECTED_CELL': FALSE,
        'EXPECTEDADDRESS_CELL': KApply('.Account_EVM-TYPES_Account'),
        'EXPECTEDVALUE_CELL': intToken(0),
        'EXPECTEDDATA_CELL': KApply('.ByteArray_EVM-TYPES_ByteArray'),
        'OPCODETYPE_CELL': KApply('.OpcodeType_FOUNDRY-CHEAT-CODES_OpcodeType'),
        'RECORDEVENT_CELL': FALSE,
        'ISEVENTEXPECTED_CELL': FALSE,
        'ISCALLWHITELISTACTIVE_CELL': FALSE,
        'ISSTORAGEWHITELISTACTIVE_CELL': FALSE,
        'ADDRESSSET_CELL': KApply('.Set'),
        'STORAGESLOTSET_CELL': KApply('.Set'),
    }

    if calldata is not None:
        init_subst['CALLDATA_CELL'] = calldata

    if callvalue is not None:
        init_subst['CALLVALUE_CELL'] = callvalue

    return Subst(init_subst)(empty_config)


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
