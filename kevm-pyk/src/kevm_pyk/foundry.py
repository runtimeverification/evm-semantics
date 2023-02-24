import json
import logging
import sys
from pathlib import Path
from typing import Dict, Final, Iterable, List, Optional, Tuple

from pyk.cli_utils import BugReport
from pyk.cterm import CTerm, build_claim, build_rule
from pyk.kast.inner import KApply, KInner, KRewrite, KToken
from pyk.kast.manip import get_cell, minimize_term, push_down_rewrites
from pyk.kast.outer import KDefinition, KFlatModule, KImport, KRequire, KRuleLike
from pyk.kcfg import KCFG, KCFGExplore
from pyk.ktool.kompile import KompileBackend
from pyk.prelude.k import GENERATED_TOP_CELL
from pyk.prelude.ml import mlTop
from pyk.utils import shorten_hashes

from .kevm import KEVM, Foundry
from .solc_to_k import Contract, contract_to_main_module, method_to_cfg
from .utils import KDefinition__expand_macros, find_free_port, parallel_kcfg_explore

_LOGGER: Final = logging.getLogger(__name__)


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
            kcfg = method_to_cfg(empty_config, contract, method)
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
