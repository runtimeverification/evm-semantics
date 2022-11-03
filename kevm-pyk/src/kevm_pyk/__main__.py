import json
import logging
import sys
from argparse import ArgumentParser, Namespace
from pathlib import Path
from typing import Any, Callable, Dict, Final, Iterable, List, Optional, Tuple, TypeVar

from pathos.pools import ProcessPool  # type: ignore
from pyk.cli_utils import dir_path, file_path
from pyk.cterm import CTerm
from pyk.kast import KApply, KAtt, KDefinition, KFlatModule, KImport, KInner, KRequire, KRewrite, KRule, KToken
from pyk.kastManip import flatten_label, minimize_term, push_down_rewrites
from pyk.kcfg import KCFG
from pyk.ktool.kit import KIT
from pyk.ktool.krun import _krun
from pyk.prelude.ml import is_top, mlTop

from .gst_to_kore import gst_to_kore
from .kevm import KEVM, Foundry
from .solc_to_k import Contract, contract_to_main_module, method_to_cfg, solc_compile
from .utils import KCFG__replace_node, KPrint_make_unparsing, KProve_prove_claim, add_include_arg, sanitize_config

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
    profile: bool,
    main_file: Path,
    emit_json: bool,
    includes: List[str],
    main_module: Optional[str],
    syntax_module: Optional[str],
    md_selector: Optional[str],
    **kwargs: Any,
) -> None:
    KEVM.kompile(
        definition_dir,
        main_file,
        emit_json=emit_json,
        includes=includes,
        main_module_name=main_module,
        syntax_module_name=syntax_module,
        md_selector=md_selector,
        profile=profile,
    )


def exec_solc_to_k(
    definition_dir: Path,
    profile: bool,
    contract_file: Path,
    contract_name: str,
    main_module: Optional[str],
    spec_module: Optional[str],
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
    _spec_module = KFlatModule(spec_module if spec_module else 'SPEC')
    modules = (contract_module, _main_module, _spec_module)
    bin_runtime_definition = KDefinition(
        _main_module.name, modules, requires=[KRequire(req) for req in ['edsl.md'] + requires]
    )
    _kprint = KPrint_make_unparsing(kevm, extra_modules=modules)
    KEVM._patch_symbol_table(_kprint.symbol_table)
    print(_kprint.pretty_print(bin_runtime_definition) + '\n')


def exec_foundry_kompile(
    definition_dir: Path,
    profile: bool,
    foundry_out: Path,
    includes: List[str],
    md_selector: Optional[str],
    regen: bool = False,
    rekompile: bool = False,
    requires: Iterable[str] = (),
    imports: Iterable[str] = (),
    **kwargs: Any,
) -> None:
    _ignore_arg(kwargs, 'main_module', f'--main-module {kwargs["main_module"]}')
    _ignore_arg(kwargs, 'syntax_module', f'--syntax-module {kwargs["syntax_module"]}')
    _ignore_arg(kwargs, 'spec_module', f'--spec-module {kwargs["spec_module"]}')
    main_module = 'FOUNDRY-MAIN'
    syntax_module = 'FOUNDRY-MAIN'
    foundry_definition_dir = foundry_out / 'kompiled'
    foundry_main_file = foundry_definition_dir / 'foundry.k'
    kompiled_timestamp = foundry_definition_dir / 'timestamp'
    requires = ['foundry.md'] + list(requires)
    imports = ['FOUNDRY'] + list(imports)

    if not foundry_definition_dir.exists():
        foundry_definition_dir.mkdir()

    json_paths = _contract_json_paths(foundry_out)
    contracts = [_contract_from_json(json_path) for json_path in json_paths]

    foundry = Foundry(definition_dir, profile=profile)
    empty_config = foundry.definition.empty_config(Foundry.Sorts.FOUNDRY_CELL)

    bin_runtime_definition = _foundry_to_bin_runtime(
        empty_config=empty_config,
        contracts=contracts,
        main_module=main_module,
        requires=requires,
        imports=imports,
    )

    if regen or not foundry_main_file.exists():
        with open(foundry_main_file, 'w') as fmf:
            _LOGGER.info(f'Writing file: {foundry_main_file}')
            _foundry = Foundry(definition_dir=definition_dir)
            _kprint = KPrint_make_unparsing(_foundry, extra_modules=bin_runtime_definition.modules)
            Foundry._patch_symbol_table(_kprint.symbol_table)
            fmf.write(_kprint.pretty_print(bin_runtime_definition) + '\n')

    if regen or rekompile or not kompiled_timestamp.exists():
        _LOGGER.info(f'Kompiling definition: {foundry_main_file}')
        KEVM.kompile(
            foundry_definition_dir,
            foundry_main_file,
            emit_json=True,
            includes=includes,
            main_module_name=main_module,
            syntax_module_name=syntax_module,
            md_selector=md_selector,
            profile=profile,
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
    debug_equations: List[str],
    bug_report: bool,
    spec_module: Optional[str],
    depth: Optional[int],
    claims: Iterable[str] = (),
    exclude_claims: Iterable[str] = (),
    minimize: bool = True,
    **kwargs: Any,
) -> None:
    _ignore_arg(kwargs, 'lemmas', '--lemma')
    kevm = KEVM(definition_dir, profile=profile)
    prove_args = add_include_arg(includes)
    haskell_args = []
    for de in debug_equations:
        haskell_args += ['--debug-equation', de]
    if bug_report:
        haskell_args += ['--bug-report', str(spec_file.with_suffix(''))]
    if depth is not None:
        prove_args += ['--depth', str(depth)]
    if claims:
        prove_args += ['--claims', ','.join(claims)]
    if exclude_claims:
        prove_args += ['--exclude', ','.join(exclude_claims)]
    final_state = kevm.prove(spec_file, spec_module_name=spec_module, args=prove_args, haskell_args=haskell_args)
    if minimize:
        final_state = minimize_term(final_state)
    print(kevm.pretty_print(final_state) + '\n')
    if not (type(final_state) is KApply and final_state.label.name == '#Top'):
        _LOGGER.error('Proof failed!')
        sys.exit(1)


def exec_foundry_prove(
    profile: bool,
    foundry_out: Path,
    includes: List[str],
    debug_equations: List[str],
    bug_report: bool,
    depth: Optional[int],
    reinit: bool = False,
    tests: Iterable[str] = (),
    exclude_tests: Iterable[str] = (),
    workers: int = 1,
    minimize: bool = True,
    lemmas: Iterable[str] = (),
    simplify_init: bool = True,
    **kwargs: Any,
) -> None:
    _ignore_arg(kwargs, 'main_module', f'--main-module: {kwargs["main_module"]}')
    _ignore_arg(kwargs, 'syntax_module', f'--syntax-module: {kwargs["syntax_module"]}')
    _ignore_arg(kwargs, 'definition_dir', f'--definition: {kwargs["definition_dir"]}')
    _ignore_arg(kwargs, 'spec_module', f'--spec-module: {kwargs["spec_module"]}')
    if workers <= 0:
        raise ValueError(f'Must have at least one worker, found: --workers {workers}')
    definition_dir = foundry_out / 'kompiled'
    use_directory = foundry_out / 'specs'
    use_directory.mkdir(parents=True, exist_ok=True)
    kcfgs_dir = foundry_out / 'kcfgs'
    if not kcfgs_dir.exists():
        kcfgs_dir.mkdir()
    foundry = Foundry(definition_dir, profile=profile, use_directory=use_directory)

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

    kcfgs: Dict[str, Tuple[KCFG, Path]] = {}
    for test in tests:
        kcfg_file = kcfgs_dir / f'{test}.json'
        if reinit or not kcfg_file.exists():
            _LOGGER.info(f'Initializing KCFG for test: {test}')
            contract_name, method_name = test.split('.')
            contract = [c for c in contracts if c.name == contract_name][0]
            method = [m for m in contract.methods if m.name == method_name][0]
            empty_config = foundry.definition.empty_config(Foundry.Sorts.FOUNDRY_CELL)
            cfg = method_to_cfg(empty_config, contract, method)
            if simplify_init:
                _LOGGER.info(f'Simplifying initial state for test: {test}')
                edge = KCFG.Edge(cfg.get_unique_init(), cfg.get_unique_target(), mlTop(), -1)
                claim = edge.to_claim()
                init_simplified = foundry.prove_claim(
                    claim, f'simplify-init-{cfg.get_unique_init().id}', args=['--depth', '0']
                )
                init_simplified = sanitize_config(foundry.definition, init_simplified)
                cfg = KCFG__replace_node(cfg, cfg.get_unique_init().id, CTerm(init_simplified))
                _LOGGER.info(f'Simplifying target state for test: {test}')
                edge = KCFG.Edge(cfg.get_unique_target(), cfg.get_unique_init(), mlTop(), -1)
                claim = edge.to_claim()
                target_simplified = foundry.prove_claim(
                    claim, f'simplify-target-{cfg.get_unique_target().id}', args=['--depth', '0']
                )
                target_simplified = sanitize_config(foundry.definition, target_simplified)
                cfg = KCFG__replace_node(cfg, cfg.get_unique_target().id, CTerm(target_simplified))
            kcfgs[test] = (cfg, kcfg_file)
            with open(kcfg_file, 'w') as kf:
                kf.write(json.dumps(cfg.to_dict()))
                kf.close()
            _LOGGER.info(f'Wrote file: {kcfg_file}')
        else:
            with open(kcfg_file, 'r') as kf:
                kcfgs[test] = (KCFG.from_dict(json.loads(kf.read())), kcfg_file)

    lemma_rules = [KRule(KToken(lr, 'K'), att=KAtt({'simplification': ''})) for lr in lemmas]

    def _write_cfg(_cfg: KCFG, _cfgpath: Path) -> None:
        with open(_cfgpath, 'w') as cfgfile:
            cfgfile.write(json.dumps(_cfg.to_dict()))
            _LOGGER.info(f'Updated CFG file: {_cfgpath}')

    def prove_it(_id_and_cfg: Tuple[str, Tuple[KCFG, Path]]) -> bool:
        _cfg_id, (_cfg, _cfg_path) = _id_and_cfg
        if len(_cfg.frontier) == 0:
            return True
        _init_node = _cfg.frontier[0]
        _target_node = _cfg.get_unique_target()
        _claim = KCFG.Edge(_init_node, _target_node, mlTop(), -1).to_claim()
        _claim_id = _cfg_id.replace('.', '-').replace('_', '-')
        ret, result = KProve_prove_claim(foundry, _claim, _claim_id, _LOGGER, depth=depth, lemmas=lemma_rules)
        if is_top(result):
            _cfg.create_edge(_cfg.get_unique_init().id, _cfg.get_unique_target().id, mlTop(), -1)
            _LOGGER.info(f'Proof passed: {_cfg_id}')
        else:
            for result_state in flatten_label('#Or', result):
                _cfg.add_expanded(_init_node.id)
                new_node = _cfg.get_or_create_node(CTerm(result_state))
                _cfg.create_edge(_cfg.get_unique_init().id, new_node.id, mlTop(), -1)
                if minimize:
                    result_state = minimize_term(result_state)
                _LOGGER.error(f'Proof failed: {_cfg_id}\n{foundry.pretty_print(result_state)}')
        _write_cfg(_cfg, _cfg_path)
        failure_nodes = cfg.frontier + cfg.stuck
        return failure_nodes == 0

    with ProcessPool(ncpus=workers) as process_pool:
        results = process_pool.map(prove_it, kcfgs.items())
        process_pool.close()

    failed = 0
    for (cid, _), succeeded in zip(kcfgs.items(), results):
        if succeeded:
            print(f'PASSED: {cid}')
        else:
            print(f'FAILED: {cid}')
            failed += 1
    sys.exit(failed)


def exec_foundry_show(
    profile: bool,
    foundry_out: Path,
    test: str,
    nodes: Iterable[str] = (),
    node_deltas: Iterable[Tuple[str, str]] = (),
    minimize: bool = True,
    **kwargs: Any,
) -> None:
    definition_dir = foundry_out / 'kompiled'
    use_directory = foundry_out / 'specs'
    use_directory.mkdir(parents=True, exist_ok=True)
    kcfgs_dir = foundry_out / 'kcfgs'
    foundry = Foundry(definition_dir, profile=profile, use_directory=use_directory)
    kcfg_file = kcfgs_dir / f'{test}.json'
    with open(kcfg_file, 'r') as kf:
        kcfg = KCFG.from_dict(json.loads(kf.read()))
        list(map(print, kcfg.pretty(foundry)))
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
        with open(kcfg_file, 'r') as kf:
            kcfg = KCFG.from_dict(json.loads(kf.read()))
        kcfg_name = kcfg_file.name[0:-5]
        total_nodes = len(kcfg.nodes)
        frontier_nodes = len(kcfg.frontier)
        stuck_nodes = len(kcfg.stuck)
        proven = 'failed'
        if stuck_nodes == 0:
            proven = 'pending'
            if frontier_nodes == 0:
                proven = 'passed'
        print(f'{kcfg_name}: {proven}')
        if details:
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
    kevm = KEVM(definition_dir, profile=profile)
    krun_args = []
    if term:
        krun_args += ['--term']
    if parser is not None:
        krun_args += ['--parser', parser]
    if not expand_macros:
        krun_args += ['--no-expand-macros']
    # TODO: These are inlined into _krun
    krun_args += ['--output', output]
    krun_result = _krun(kevm.definition_dir, Path(input_file), depth=depth, args=krun_args, profile=profile)
    print(krun_result.stdout)
    sys.exit(krun_result.returncode)


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

    k_args = ArgumentParser(add_help=False)
    k_args.add_argument('--depth', default=None, type=int, help='Maximum depth to execute to.')
    k_args.add_argument(
        '-I', type=str, dest='includes', default=[], action='append', help='Directories to lookup K definitions in.'
    )
    k_args.add_argument('--main-module', default=None, type=str, help='Name of the main module.')
    k_args.add_argument('--syntax-module', default=None, type=str, help='Name of the syntax module.')
    k_args.add_argument('--spec-module', default=None, type=str, help='Name of the spec module.')
    k_args.add_argument('--definition', type=str, dest='definition_dir', help='Path to definition to use.')

    kprove_args = ArgumentParser(add_help=False)
    kprove_args.add_argument(
        '--debug-equations', type=list_of(str, delim=','), default=[], help='Comma-separate list of equations to debug.'
    )
    kprove_args.add_argument(
        '--bug-report',
        default=False,
        action='store_true',
        help='Generate a haskell-backend bug report for the execution.',
    )
    kprove_args.add_argument(
        '--lemma',
        dest='lemmas',
        default=[],
        action='append',
        help='Additional lemmas to include as simplification rules during execution.',
    )
    kprove_args.add_argument(
        '--minimize', dest='minimize', default=True, action='store_true', help='Minimize prover output.'
    )
    kprove_args.add_argument(
        '--no-minimize', dest='minimize', action='store_false', help='Do not minimize prover output.'
    )

    k_kompile_args = ArgumentParser(add_help=False)
    k_kompile_args.add_argument(
        '--md-selector',
        type=str,
        default='k & ! nobytes & ! node',
        help='Code selector expression to use when reading markdown.',
    )
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

    prove_args = command_parser.add_parser('prove', help='Run KEVM proof.', parents=[shared_args, k_args, kprove_args])
    prove_args.add_argument('spec_file', type=file_path, help='Path to spec file.')
    prove_args.add_argument(
        '--claim', type=str, dest='claims', action='append', help='Only prove listed claims, MODULE_NAME.claim-id'
    )
    prove_args.add_argument(
        '--exclude-claim',
        type=str,
        dest='exclude_claims',
        action='append',
        help='Skip listed claims, MODULE_NAME.claim-id',
    )

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
        parents=[shared_args, k_args, kprove_args],
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
        help='Reinitialize KCFGs even if they already exist.',
    )
    foundry_prove_args.add_argument(
        '--simplify-init',
        dest='simplify_init',
        default=True,
        action='store_true',
        help='Simplify the initial and target states at startup.',
    )
    foundry_prove_args.add_argument(
        '--no-simplify-init',
        dest='simplify_init',
        action='store_false',
        help='Do not simplify the initial and target states at startup.',
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
        type=KIT.arg_pair_of(str, str),
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

    foundry_list_args = command_parser.add_parser(
        'foundry-list',
        help='List information about KCFGs on disk',
        parents=[shared_args, k_args],
    )
    foundry_list_args.add_argument('foundry_out', type=dir_path, help='Path to Foundry output directory.')
    foundry_list_args.add_argument(
        '--details', dest='details', default=True, action='store_true', help='Information about progress on each KCFG.'
    )
    foundry_list_args.add_argument('--no-details', dest='details', action='store_false', help='Just list the KCFGs.')

    return parser


def _loglevel(args: Namespace) -> int:
    if args.verbose or args.profile:
        return logging.INFO

    if args.debug:
        return logging.DEBUG

    return logging.WARNING


if __name__ == "__main__":
    main()
