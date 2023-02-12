import json
import logging
import sys
from argparse import ArgumentParser, Namespace
from pathlib import Path
from typing import Any, Callable, Dict, Final, Iterable, List, Optional, Tuple, TypeVar

from pyk.cli_utils import BugReport, dir_path, file_path
from pyk.cterm import CTerm, build_claim, build_rule
from pyk.kast.inner import KApply, KInner, KRewrite, KToken
from pyk.kast.manip import get_cell, minimize_term, push_down_rewrites
from pyk.kast.outer import KDefinition, KFlatModule, KImport, KRequire, KRuleLike
from pyk.kcfg import KCFG, KCFGExplore, KCFGViewer
from pyk.ktool.kompile import KompileBackend
from pyk.ktool.krun import KRunOutput, _krun
from pyk.prelude.k import GENERATED_TOP_CELL
from pyk.prelude.ml import mlTop
from pyk.utils import shorten_hashes

from .gst_to_kore import gst_to_kore
from .kevm import KEVM, Foundry
from .solc_to_k import Contract, contract_to_main_module, method_to_cfg, solc_compile
from .utils import KDefinition__expand_macros, arg_pair_of, find_free_port, parallel_kcfg_explore

T = TypeVar('T')

_LOGGER: Final = logging.getLogger(__name__)
_LOG_FORMAT: Final = '%(levelname)s %(asctime)s %(name)s - %(message)s'


def _ignore_arg(args: Dict[str, Any], arg: str, cli_option: str) -> None:
    if arg in args:
        if args[arg] is not None:
            _LOGGER.warning(f'Ignoring command-line option: {cli_option}')
        args.pop(arg)


def main() -> None:
    sys.setrecursionlimit(15000000)
    parser = _create_argument_parser()
    args = parser.parse_args()
    logging.basicConfig(level=_loglevel(args), format=_LOG_FORMAT)

    executor_name = 'exec_' + args.command.lower().replace('-', '_')
    if executor_name not in globals():
        raise AssertionError(f'Unimplemented command: {args.command}')

    execute = globals()[executor_name]
    execute(**vars(args))


# Command implementation


def exec_compile(contract_file: Path, profile: bool, **kwargs: Any) -> None:
    res = solc_compile(contract_file, profile=profile)
    print(json.dumps(res))


def exec_gst_to_kore(input_file: Path, schedule: str, mode: str, chainid: int, **kwargs: Any) -> None:
    gst_to_kore(input_file, sys.stdout, schedule, mode, chainid)


def exec_kompile(
    definition_dir: Path,
    backend: KompileBackend,
    profile: bool,
    main_file: Path,
    emit_json: bool,
    includes: List[str],
    main_module: Optional[str],
    syntax_module: Optional[str],
    md_selector: Optional[str],
    ccopts: Iterable[str] = (),
    llvm_kompile: bool = True,
    o0: bool = False,
    o1: bool = False,
    o2: bool = False,
    o3: bool = False,
    debug: bool = False,
    **kwargs: Any,
) -> None:
    optimization = 0
    if o1:
        optimization = 1
    if o2:
        optimization = 2
    if o3:
        optimization = 3
    KEVM.kompile(
        definition_dir,
        backend,
        main_file,
        emit_json=emit_json,
        includes=includes,
        main_module_name=main_module,
        syntax_module_name=syntax_module,
        md_selector=md_selector,
        profile=profile,
        debug=debug,
        ccopts=ccopts,
        llvm_kompile=llvm_kompile,
        optimization=optimization,
    )


def exec_solc_to_k(
    definition_dir: Path,
    profile: bool,
    contract_file: Path,
    contract_name: str,
    main_module: Optional[str],
    requires: List[str],
    imports: List[str],
    **kwargs: Any,
) -> None:
    kevm = KEVM(definition_dir, profile=profile)
    empty_config = kevm.definition.empty_config(KEVM.Sorts.KEVM_CELL)
    solc_json = solc_compile(contract_file, profile=profile)
    contract_json = solc_json['contracts'][contract_file.name][contract_name]
    contract = Contract(contract_name, contract_json, foundry=False)
    contract_module = contract_to_main_module(contract, empty_config, imports=['EDSL'] + imports)
    _main_module = KFlatModule(
        main_module if main_module else 'MAIN', [], [KImport(mname) for mname in [contract_module.name] + imports]
    )
    modules = (contract_module, _main_module)
    bin_runtime_definition = KDefinition(
        _main_module.name, modules, requires=[KRequire(req) for req in ['edsl.md'] + requires]
    )
    _kprint = KEVM(
        definition_dir,
        profile=profile,
        extra_unparsing_modules=modules,
    )
    print(_kprint.pretty_print(bin_runtime_definition) + '\n')


def exec_foundry_kompile(
    definition_dir: Path,
    profile: bool,
    foundry_out: Path,
    md_selector: Optional[str] = None,
    includes: Iterable[str] = (),
    regen: bool = False,
    rekompile: bool = False,
    requires: Iterable[str] = (),
    imports: Iterable[str] = (),
    ccopts: Iterable[str] = (),
    llvm_kompile: bool = True,
    debug: bool = False,
    **kwargs: Any,
) -> None:
    _ignore_arg(kwargs, 'main_module', f'--main-module {kwargs["main_module"]}')
    _ignore_arg(kwargs, 'syntax_module', f'--syntax-module {kwargs["syntax_module"]}')
    _ignore_arg(kwargs, 'spec_module', f'--spec-module {kwargs["spec_module"]}')
    _ignore_arg(kwargs, 'backend', f'--backend {kwargs["backend"]}')
    _ignore_arg(kwargs, 'o0', '-O0')
    _ignore_arg(kwargs, 'o1', '-O1')
    _ignore_arg(kwargs, 'o2', '-O2')
    _ignore_arg(kwargs, 'o3', '-O3')
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


def exec_prove(
    definition_dir: Path,
    profile: bool,
    spec_file: Path,
    includes: List[str],
    bug_report: bool = False,
    save_directory: Optional[Path] = None,
    spec_module: Optional[str] = None,
    md_selector: Optional[str] = None,
    claim_labels: Iterable[str] = (),
    exclude_claim_labels: Iterable[str] = (),
    max_depth: int = 100,
    max_iterations: Optional[int] = None,
    workers: int = 1,
    simplify_init: bool = True,
    break_every_step: bool = False,
    break_on_calls: bool = True,
    implication_every_block: bool = True,
    rpc_base_port: Optional[int] = None,
    **kwargs: Any,
) -> None:
    br = None if not bug_report else BugReport(spec_file.with_suffix('.bug_report'))
    kevm = KEVM(definition_dir, use_directory=save_directory, profile=profile, bug_report=br)

    _LOGGER.info(f'Extracting claims from file: {spec_file}')
    claims = kevm.get_claims(
        spec_file,
        spec_module_name=spec_module,
        include_dirs=[Path(i) for i in includes],
        md_selector=md_selector,
        claim_labels=claim_labels,
        exclude_claim_labels=exclude_claim_labels,
    )

    _LOGGER.info(f'Converting {len(claims)} KClaims to KCFGs')
    proof_problems = {c.label: KCFG.from_claim(kevm.definition, c) for c in claims}
    if simplify_init:
        with KCFGExplore(kevm, port=find_free_port(), bug_report=br) as kcfg_explore:
            proof_problems = {claim: kcfg_explore.simplify(claim, cfg) for claim, cfg in proof_problems.items()}

    results = parallel_kcfg_explore(
        kevm,
        proof_problems,
        save_directory=save_directory,
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


def exec_view_kcfg(definition_dir: Path, claim: str, kcfgs_dir: Path, profile: bool, **kwargs: Any) -> None:
    kevm = KEVM(definition_dir, profile=profile)
    kcfg = KCFGExplore.read_cfg(claim, kcfgs_dir)
    if kcfg is None:
        raise ValueError(f'Could not load CFG {claim} from {kcfgs_dir}')
    viewer = KCFGViewer(kcfg, kevm, node_printer=kevm.short_info)
    viewer.run()


def exec_foundry_prove(
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
    **kwargs: Any,
) -> None:
    _ignore_arg(kwargs, 'main_module', f'--main-module: {kwargs["main_module"]}')
    _ignore_arg(kwargs, 'syntax_module', f'--syntax-module: {kwargs["syntax_module"]}')
    _ignore_arg(kwargs, 'definition_dir', f'--definition: {kwargs["definition_dir"]}')
    _ignore_arg(kwargs, 'spec_module', f'--spec-module: {kwargs["spec_module"]}')
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
    br = None if not bug_report else BugReport(foundry_out / 'bug_report')
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


def exec_foundry_show(
    profile: bool,
    foundry_out: Path,
    test: str,
    nodes: Iterable[str] = (),
    node_deltas: Iterable[Tuple[str, str]] = (),
    to_module: bool = False,
    minimize: bool = True,
    **kwargs: Any,
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

        def to_rule(edge: KCFG.Edge, claim: bool = False) -> KRuleLike:
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
            if not claim:
                rule, _ = build_rule(sentence_id, init_cterm.add_constraint(edge.condition), target_cterm, priority=35)
            else:
                rule, _ = build_claim(sentence_id, init_cterm.add_constraint(edge.condition), target_cterm)
            return rule

        rules = [to_rule(e) for e in kcfg.edges() if e.depth > 0]
        claims = [to_rule(KCFG.Edge(nd, kcfg.get_unique_target(), mlTop(), -1), claim=True) for nd in kcfg.frontier]
        new_module = KFlatModule('SUMMARY', rules + claims)
        print(foundry.pretty_print(new_module) + '\n')


def exec_foundry_list(
    profile: bool,
    foundry_out: Path,
    details: bool = True,
    **kwargs: Any,
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


def exec_run(
    definition_dir: Path,
    profile: bool,
    input_file: Path,
    term: bool,
    parser: Optional[str],
    expand_macros: str,
    depth: Optional[int],
    output: str,
    **kwargs: Any,
) -> None:
    krun_result = _krun(
        definition_dir=Path(definition_dir),
        input_file=Path(input_file),
        depth=depth,
        profile=profile,
        term=term,
        no_expand_macros=not expand_macros,
        parser=parser,
        output=KRunOutput[output.upper()],
    )
    print(krun_result.stdout)
    sys.exit(krun_result.returncode)


def exec_foundry_view_kcfg(foundry_out: Path, test: str, profile: bool, **kwargs: Any) -> None:
    definition_dir = foundry_out / 'kompiled'
    use_directory = foundry_out / 'specs'
    kcfgs_dir = foundry_out / 'kcfgs'
    use_directory.mkdir(parents=True, exist_ok=True)
    foundry = Foundry(definition_dir, profile=profile, use_directory=use_directory)
    kcfg = KCFGExplore.read_cfg(test, kcfgs_dir)
    if kcfg is None:
        raise ValueError(f'Could not load CFG {test} from {kcfgs_dir}')
    viewer = KCFGViewer(kcfg, foundry, node_printer=foundry.short_info)
    viewer.run()


def exec_foundry_remove_node(foundry_out: Path, test: str, node: str, profile: bool, **kwargs: Any) -> None:
    kcfgs_dir = foundry_out / 'kcfgs'
    kcfg = KCFGExplore.read_cfg(test, kcfgs_dir)
    if kcfg is None:
        raise ValueError(f'Could not load CFG {test} from {kcfgs_dir}')
    for _node in kcfg.reachable_nodes(node, traverse_covers=True):
        if not kcfg.is_target(_node.id):
            _LOGGER.info(f'Removing node: {shorten_hashes(_node.id)}')
            kcfg.remove_node(_node.id)
    KCFGExplore.write_cfg(test, kcfgs_dir, kcfg)


def exec_foundry_simplify_node(
    foundry_out: Path,
    test: str,
    node: str,
    profile: bool,
    replace: bool = False,
    minimize: bool = True,
    bug_report: bool = False,
    **kwargs: Any,
) -> None:
    definition_dir = foundry_out / 'kompiled'
    use_directory = foundry_out / 'specs'
    kcfgs_dir = foundry_out / 'kcfgs'
    use_directory.mkdir(parents=True, exist_ok=True)
    br = None if not bug_report else BugReport(Path(f'{test}.bug_report'))
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


def exec_foundry_step_node(
    foundry_out: Path,
    test: str,
    node: str,
    profile: bool,
    repeat: int = 1,
    depth: int = 1,
    minimize: bool = True,
    bug_report: bool = False,
    **kwargs: Any,
) -> None:
    if repeat < 1:
        raise ValueError(f'Expected positive value for --repeat, got: {repeat}')
    if depth < 1:
        raise ValueError(f'Expected positive value for --depth, got: {depth}')
    definition_dir = foundry_out / 'kompiled'
    use_directory = foundry_out / 'specs'
    kcfgs_dir = foundry_out / 'kcfgs'
    use_directory.mkdir(parents=True, exist_ok=True)
    br = None if not bug_report else BugReport(Path(f'{test}.bug_report'))
    foundry = Foundry(definition_dir, profile=profile, use_directory=use_directory, bug_report=br)
    kcfg = KCFGExplore.read_cfg(test, kcfgs_dir)
    if kcfg is None:
        raise ValueError(f'Could not load CFG {test} from {kcfgs_dir}')
    port = find_free_port()
    with KCFGExplore(foundry, port=port, bug_report=br) as kcfg_explore:
        for _i in range(repeat):
            kcfg, node = kcfg_explore.step(test, kcfg, node, depth=depth)
            KCFGExplore.write_cfg(test, kcfgs_dir, kcfg)


def exec_foundry_section_edge(
    foundry_out: Path,
    test: str,
    edge: Tuple[str, str],
    profile: bool,
    sections: int = 2,
    replace: bool = False,
    minimize: bool = True,
    bug_report: bool = False,
    **kwargs: Any,
) -> None:
    definition_dir = foundry_out / 'kompiled'
    use_directory = foundry_out / 'specs'
    kcfgs_dir = foundry_out / 'kcfgs'
    use_directory.mkdir(parents=True, exist_ok=True)
    br = None if not bug_report else BugReport(Path(f'{test}.bug_report'))
    foundry = Foundry(definition_dir, profile=profile, use_directory=use_directory, bug_report=br)
    kcfg = KCFGExplore.read_cfg(test, kcfgs_dir)
    if kcfg is None:
        raise ValueError(f'Could not load CFG {test} from {kcfgs_dir}')
    port = find_free_port()
    source_id, target_id = edge
    with KCFGExplore(foundry, port=port, bug_report=br) as kcfg_explore:
        kcfg, _ = kcfg_explore.section_edge(test, kcfg, source_id=source_id, target_id=target_id, sections=sections)
    KCFGExplore.write_cfg(test, kcfgs_dir, kcfg)


# Helpers


def _create_argument_parser() -> ArgumentParser:
    def list_of(elem_type: Callable[[str], T], delim: str = ';') -> Callable[[str], List[T]]:
        def parse(s: str) -> List[T]:
            return [elem_type(elem) for elem in s.split(delim)]

        return parse

    shared_args = ArgumentParser(add_help=False)
    shared_args.add_argument('--verbose', '-v', default=False, action='store_true', help='Verbose output.')
    shared_args.add_argument('--debug', default=False, action='store_true', help='Debug output.')
    shared_args.add_argument('--profile', default=False, action='store_true', help='Coarse process-level profiling.')
    shared_args.add_argument('--workers', '-j', default=1, type=int, help='Number of processes to run in parallel.')

    rpc_args = ArgumentParser(add_help=False)
    rpc_args.add_argument(
        '--rpc-base-port',
        dest='rpc_base_port',
        type=int,
        help='Base port to use for RPC server invocations.',
    )
    rpc_args.add_argument(
        '--bug-report',
        default=False,
        action='store_true',
        help='Generate a haskell-backend bug report for the execution.',
    )

    explore_args = ArgumentParser(add_help=False)
    explore_args.add_argument(
        '--break-every-step',
        dest='break_every_step',
        default=False,
        action='store_true',
        help='Store a node for every EVM opcode step (expensive).',
    )
    explore_args.add_argument(
        '--break-on-calls',
        dest='break_on_calls',
        default=True,
        action='store_true',
        help='Store a node for every EVM call made.',
    )
    explore_args.add_argument(
        '--no-break-on-calls',
        dest='break_on_calls',
        action='store_false',
        help='Do not store a node for every EVM call made.',
    )
    explore_args.add_argument(
        '--implication-every-block',
        dest='implication_every_block',
        default=True,
        action='store_true',
        help='Check subsumption into target state every basic block, not just at terminal nodes.',
    )
    explore_args.add_argument(
        '--no-implication-every-block',
        dest='implication_every_block',
        action='store_false',
        help='Do not check subsumption into target state every basic block, not just at terminal nodes.',
    )
    explore_args.add_argument(
        '--simplify-init',
        dest='simplify_init',
        default=True,
        action='store_true',
        help='Simplify the initial and target states at startup.',
    )
    explore_args.add_argument(
        '--no-simplify-init',
        dest='simplify_init',
        action='store_false',
        help='Do not simplify the initial and target states at startup.',
    )
    explore_args.add_argument(
        '--max-depth',
        dest='max_depth',
        default=1000,
        type=int,
        help='Store every Nth state in the CFG for inspection.',
    )
    explore_args.add_argument(
        '--max-iterations',
        dest='max_iterations',
        default=None,
        type=int,
        help='Store every Nth state in the CFG for inspection.',
    )

    k_args = ArgumentParser(add_help=False)
    k_args.add_argument('--depth', default=None, type=int, help='Maximum depth to execute to.')
    k_args.add_argument(
        '-I', type=str, dest='includes', default=[], action='append', help='Directories to lookup K definitions in.'
    )
    k_args.add_argument('--main-module', default=None, type=str, help='Name of the main module.')
    k_args.add_argument('--syntax-module', default=None, type=str, help='Name of the syntax module.')
    k_args.add_argument('--spec-module', default=None, type=str, help='Name of the spec module.')
    k_args.add_argument('--definition', type=str, dest='definition_dir', help='Path to definition to use.')
    k_args.add_argument(
        '--md-selector',
        type=str,
        default='k & ! nobytes & ! node',
        help='Code selector expression to use when reading markdown.',
    )

    kprove_args = ArgumentParser(add_help=False)
    kprove_args.add_argument(
        '--debug-equations', type=list_of(str, delim=','), default=[], help='Comma-separate list of equations to debug.'
    )
    kprove_args.add_argument(
        '--minimize', dest='minimize', default=True, action='store_true', help='Minimize prover output.'
    )
    kprove_args.add_argument(
        '--no-minimize', dest='minimize', action='store_false', help='Do not minimize prover output.'
    )

    k_kompile_args = ArgumentParser(add_help=False)
    k_kompile_args.add_argument('--backend', type=KompileBackend, help='[llvm|haskell]')
    k_kompile_args.add_argument(
        '--emit-json',
        dest='emit_json',
        default=True,
        action='store_true',
        help='Emit JSON definition after compilation.',
    )
    k_kompile_args.add_argument(
        '--no-emit-json', dest='emit_json', action='store_false', help='Do not JSON definition after compilation.'
    )
    k_kompile_args.add_argument(
        '-ccopt',
        dest='ccopts',
        default=[],
        action='append',
        help='Additional arguments to pass to llvm-kompile.',
    )
    k_kompile_args.add_argument(
        '--no-llvm-kompile',
        dest='llvm_kompile',
        default=True,
        action='store_false',
        help='Do not run llvm-kompile process.',
    )
    k_kompile_args.add_argument('-O0', dest='o0', default=False, action='store_true', help='Optimization level 0.')
    k_kompile_args.add_argument('-O1', dest='o1', default=False, action='store_true', help='Optimization level 1.')
    k_kompile_args.add_argument('-O2', dest='o2', default=False, action='store_true', help='Optimization level 2.')
    k_kompile_args.add_argument('-O3', dest='o3', default=False, action='store_true', help='Optimization level 3.')

    evm_chain_args = ArgumentParser(add_help=False)
    evm_chain_args.add_argument(
        '--schedule',
        type=str,
        default='LONDON',
        help='KEVM Schedule to use for execution. One of [DEFAULT|FRONTIER|HOMESTEAD|TANGERINE_WHISTLE|SPURIOUS_DRAGON|BYZANTIUM|CONSTANTINOPLE|PETERSBURG|ISTANBUL|BERLIN|LONDON].',
    )
    evm_chain_args.add_argument('--chainid', type=int, default=1, help='Chain ID to use for execution.')
    evm_chain_args.add_argument(
        '--mode', type=str, default='NORMAL', help='Execution mode to use. One of [NORMAL|VMTESTS].'
    )

    k_gen_args = ArgumentParser(add_help=False)
    k_gen_args.add_argument(
        '--require',
        dest='requires',
        default=[],
        action='append',
        help='Extra K requires to include in generated output.',
    )
    k_gen_args.add_argument(
        '--module-import',
        dest='imports',
        default=[],
        action='append',
        help='Extra modules to import into generated main module.',
    )

    parser = ArgumentParser(prog='python3 -m kevm_pyk')

    command_parser = parser.add_subparsers(dest='command', required=True)

    kompile_args = command_parser.add_parser(
        'kompile', help='Kompile KEVM specification.', parents=[shared_args, k_args, k_kompile_args]
    )
    kompile_args.add_argument('main_file', type=file_path, help='Path to file with main module.')

    prove_args = command_parser.add_parser(
        'prove', help='Run KEVM proof.', parents=[shared_args, k_args, kprove_args, rpc_args, explore_args]
    )
    prove_args.add_argument('spec_file', type=file_path, help='Path to spec file.')
    prove_args.add_argument('--save-directory', dest='kcfgs_dir', type=dir_path, help='Directory to store CFGs in.')
    prove_args.add_argument(
        '--claim', type=str, dest='claim_labels', action='append', help='Only prove listed claims, MODULE_NAME.claim-id'
    )
    prove_args.add_argument(
        '--exclude-claim',
        type=str,
        dest='exclude_claim_labels',
        action='append',
        help='Skip listed claims, MODULE_NAME.claim-id',
    )

    view_kcfg_args = command_parser.add_parser(
        'view-kcfg',
        help='Display tree view of CFG',
        parents=[shared_args, k_args],
    )
    view_kcfg_args.add_argument(
        'save_directory', type=dir_path, help='Path to where CFGs are stored (--save-directory option to prove).'
    )
    view_kcfg_args.add_argument('claim', type=str, help='Claim identifier to load CFG for.')

    run_args = command_parser.add_parser(
        'run', help='Run KEVM test/simulation.', parents=[shared_args, evm_chain_args, k_args]
    )
    run_args.add_argument('input_file', type=file_path, help='Path to input file.')
    run_args.add_argument(
        '--term', default=False, action='store_true', help='<input_file> is the entire term to execute.'
    )
    run_args.add_argument('--parser', default=None, type=str, help='Parser to use for $PGM.')
    run_args.add_argument(
        '--output',
        default='pretty',
        type=str,
        help='Output format to use, one of [pretty|program|kast|binary|json|latex|kore|none].',
    )
    run_args.add_argument(
        '--expand-macros',
        dest='expand_macros',
        default=True,
        action='store_true',
        help='Expand macros on the input term before execution.',
    )
    run_args.add_argument(
        '--no-expand-macros',
        dest='expand_macros',
        action='store_false',
        help='Do not expand macros on the input term before execution.',
    )

    solc_args = command_parser.add_parser('compile', help='Generate combined JSON with solc compilation results.')
    solc_args.add_argument('contract_file', type=file_path, help='Path to contract file.')

    gst_to_kore_args = command_parser.add_parser(
        'gst-to-kore',
        help='Convert a GeneralStateTest to Kore for compsumption by KEVM.',
        parents=[shared_args, evm_chain_args],
    )
    gst_to_kore_args.add_argument('input_file', type=file_path, help='Path to GST.')

    solc_to_k_args = command_parser.add_parser(
        'solc-to-k',
        help='Output helper K definition for given JSON output from solc compiler.',
        parents=[shared_args, k_args, k_gen_args],
    )
    solc_to_k_args.add_argument('contract_file', type=file_path, help='Path to contract file.')
    solc_to_k_args.add_argument('contract_name', type=str, help='Name of contract to generate K helpers for.')

    foundry_kompile = command_parser.add_parser(
        'foundry-kompile',
        help='Kompile K definition corresponding to given output directory.',
        parents=[shared_args, k_args, k_gen_args, k_kompile_args],
    )
    foundry_kompile.add_argument('foundry_out', type=dir_path, help='Path to Foundry output directory.')
    foundry_kompile.add_argument(
        '--regen',
        dest='regen',
        default=False,
        action='store_true',
        help='Regenerate foundry.k even if it already exists.',
    )
    foundry_kompile.add_argument(
        '--rekompile',
        dest='rekompile',
        default=False,
        action='store_true',
        help='Rekompile foundry.k even if kompiled definition already exists.',
    )

    foundry_prove_args = command_parser.add_parser(
        'foundry-prove',
        help='Run Foundry Proof.',
        parents=[shared_args, k_args, kprove_args, rpc_args, explore_args],
    )
    foundry_prove_args.add_argument('foundry_out', type=dir_path, help='Path to Foundry output directory.')
    foundry_prove_args.add_argument(
        '--test',
        type=str,
        dest='tests',
        default=[],
        action='append',
        help='Limit to only listed tests, ContractName.TestName',
    )
    foundry_prove_args.add_argument(
        '--exclude-test',
        type=str,
        dest='exclude_tests',
        default=[],
        action='append',
        help='Skip listed tests, ContractName.TestName',
    )
    foundry_prove_args.add_argument(
        '--reinit',
        dest='reinit',
        default=False,
        action='store_true',
        help='Reinitialize CFGs even if they already exist.',
    )

    foundry_show_args = command_parser.add_parser(
        'foundry-show',
        help='Display a given Foundry CFG.',
        parents=[shared_args, k_args],
    )
    foundry_show_args.add_argument('foundry_out', type=dir_path, help='Path to Foundry output directory.')
    foundry_show_args.add_argument('test', type=str, help='Display the CFG for this test.')
    foundry_show_args.add_argument(
        '--node',
        type=str,
        dest='nodes',
        default=[],
        action='append',
        help='List of nodes to display as well.',
    )
    foundry_show_args.add_argument(
        '--node-delta',
        type=arg_pair_of(str, str),
        dest='node_deltas',
        default=[],
        action='append',
        help='List of nodes to display delta for.',
    )
    foundry_show_args.add_argument(
        '--minimize', dest='minimize', default=True, action='store_true', help='Minimize output.'
    )
    foundry_show_args.add_argument(
        '--no-minimize', dest='minimize', action='store_false', help='Do not minimize output.'
    )
    foundry_show_args.add_argument(
        '--to-module', dest='to_module', default=False, action='store_true', help='Output edges as a K module.'
    )

    foundry_list_args = command_parser.add_parser(
        'foundry-list',
        help='List information about CFGs on disk',
        parents=[shared_args, k_args],
    )
    foundry_list_args.add_argument('foundry_out', type=dir_path, help='Path to Foundry output directory.')
    foundry_list_args.add_argument(
        '--details', dest='details', default=True, action='store_true', help='Information about progress on each CFG.'
    )
    foundry_list_args.add_argument('--no-details', dest='details', action='store_false', help='Just list the CFGs.')

    foundry_view_kcfg_args = command_parser.add_parser(
        'foundry-view-kcfg',
        help='Display tree view of CFG',
        parents=[shared_args],
    )
    foundry_view_kcfg_args.add_argument('foundry_out', type=dir_path, help='Path to Foundry output directory.')
    foundry_view_kcfg_args.add_argument('test', type=str, help='View the CFG for this test.')

    foundry_remove_node = command_parser.add_parser(
        'foundry-remove-node',
        help='Remove a node and its successors.',
        parents=[shared_args],
    )
    foundry_remove_node.add_argument('foundry_out', type=dir_path, help='Path to Foundry output directory.')
    foundry_remove_node.add_argument('test', type=str, help='View the CFG for this test.')
    foundry_remove_node.add_argument('node', type=str, help='Node to remove CFG subgraph from.')

    foundry_simplify_node = command_parser.add_parser(
        'foundry-simplify-node',
        help='Simplify a given node, and potentially replace it.',
        parents=[shared_args, rpc_args],
    )
    foundry_simplify_node.add_argument('foundry_out', type=dir_path, help='Path to Foundry output directory.')
    foundry_simplify_node.add_argument('test', type=str, help='Simplify node in this CFG.')
    foundry_simplify_node.add_argument('node', type=str, help='Node to simplify in CFG.')
    foundry_simplify_node.add_argument(
        '--replace', default=False, help='Replace the original node with the simplified variant in the graph.'
    )
    foundry_simplify_node.add_argument(
        '--minimize', dest='minimize', default=True, action='store_true', help='Minimize output.'
    )
    foundry_simplify_node.add_argument(
        '--no-minimize', dest='minimize', action='store_false', help='Do not minimize output.'
    )

    foundry_step_node = command_parser.add_parser(
        'foundry-step-node',
        help='Step from a given node, adding it to the CFG.',
        parents=[shared_args, rpc_args],
    )
    foundry_step_node.add_argument('foundry_out', type=dir_path, help='Path to Foundry output directory.')
    foundry_step_node.add_argument('test', type=str, help='Step from node in this CFG.')
    foundry_step_node.add_argument('node', type=str, help='Node to step from in CFG.')
    foundry_step_node.add_argument(
        '--repeat', type=int, default=1, help='How many node expansions to do from the given start node (>= 1).'
    )
    foundry_step_node.add_argument(
        '--depth', type=int, default=1, help='How many steps to take from initial node on edge.'
    )

    foundry_section_edge = command_parser.add_parser(
        'foundry-section-edge',
        help='Given an edge in the graph, cut it into sections to get intermediate nodes.',
        parents=[shared_args, rpc_args],
    )
    foundry_section_edge.add_argument('foundry_out', type=dir_path, help='Path to Foundry output directory.')
    foundry_section_edge.add_argument('test', type=str, help='Section edge in this CFG.')
    foundry_section_edge.add_argument('edge', type=arg_pair_of(str, str), help='Edge to section in CFG.')
    foundry_section_edge.add_argument(
        '--sections', type=int, default=2, help='Number of sections to make from edge (>= 2).'
    )

    return parser


def _loglevel(args: Namespace) -> int:
    if args.debug:
        return logging.DEBUG

    if args.verbose or args.profile:
        return logging.INFO

    return logging.WARNING


if __name__ == '__main__':
    main()
