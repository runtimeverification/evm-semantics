import hashlib
import logging
from pathlib import Path
from typing import Callable, Collection, Dict, Final, Iterable, List, Optional, Tuple

from pathos.pools import ProcessPool  # type: ignore
from pyk.cterm import CTerm
from pyk.kast.inner import KApply, KInner, KRewrite, KVariable, Subst
from pyk.kast.manip import abstract_term_safely, bottom_up, is_anon_var, split_config_and_constraints, split_config_from
from pyk.kast.outer import KDefinition, KFlatModule, KImport
from pyk.kcfg import KCFG, KCFGExplore
from pyk.ktool import KPrint

_LOGGER: Final = logging.getLogger(__name__)


def parallel_kcfg_explore(
    kcfg_explore: KCFGExplore,
    proof_problems: Dict[str, KCFG],
    save_directory: Optional[Path] = None,
    max_depth: int = 100,
    max_iterations: Optional[int] = None,
    workers: int = 1,
    simplify_init: bool = True,
    break_every_step: bool = False,
    break_on_calls: bool = False,
    implication_every_block: bool = False,
    rpc_base_port: int = 3010,
    is_terminal: Optional[Callable[[CTerm], bool]] = None,
    extract_branches: Optional[Callable[[CTerm], Iterable[KInner]]] = None,
) -> int:
    def _call_rpc(packed_args: Tuple[str, KCFG, int]) -> bool:
        _cfgid, _cfg, _index = packed_args
        terminal_rules = ['EVM.halt']
        if break_every_step:
            terminal_rules.append('EVM.step')
        if break_on_calls:
            terminal_rules.extend(
                [
                    'EVM.call',
                    'EVM.callcode',
                    'EVM.delegatecall',
                    'EVM.staticcall',
                    'EVM.create',
                    'EVM.create2',
                    'FOUNDRY.foundry.call',
                ]
            )
        if simplify_init:
            kcfg_explore.simplify(_cfgid, _cfg)
        try:
            cfg_path = None
            if save_directory is not None:
                if _cfgid.isalnum():
                    _cfg_path = _cfgid
                else:
                    hash = hashlib.sha256()
                    hash.update(_cfgid.encode('utf-8'))
                    _cfg_path = str(hash.hexdigest())
                    _LOGGER.info(f'Using hashed path for storing KCFG: {_cfgid} -> {_cfg_path}')
                cfg_path = save_directory / f'{_cfg_path}.json'
            _cfg = kcfg_explore.rpc_prove(
                _cfgid,
                _cfg,
                cfg_path=cfg_path,
                rpc_port=rpc_base_port + _index,
                is_terminal=is_terminal,
                extract_branches=extract_branches,
                max_iterations=max_iterations,
                execute_depth=max_depth,
                terminal_rules=terminal_rules,
                implication_every_block=implication_every_block,
            )
            failure_nodes = _cfg.frontier + _cfg.stuck
            if len(failure_nodes) == 0:
                _LOGGER.info(f'Proof passed: {_cfgid}')
                return True
            else:
                _LOGGER.error(f'Proof failed: {_cfgid}')
                return False

        except Exception as e:
            _LOGGER.error(f'Proof crashed: {_cfgid}\n{e}')
            kcfg_explore.close()
            return False

    with ProcessPool(ncpus=workers) as process_pool:
        kcfg_explore.close()
        results = process_pool.map(_call_rpc, proof_problems)

    failed = 0
    for cid, succeeded in zip(proof_problems.keys(), results, strict=True):
        if succeeded:
            print(f'PASSED: {cid}')
        else:
            print(f'FAILED: {cid}')
            failed += 1
    return failed


def write_cfg(_cfg: KCFG, _cfgpath: Path) -> None:
    _cfgpath.write_text(_cfg.to_json())
    _LOGGER.info(f'Updated CFG file: {_cfgpath}')


def KDefinition__expand_macros(defn: KDefinition, term: KInner) -> KInner:  # noqa: N802
    def _expand_macros(_term: KInner) -> KInner:
        if type(_term) is KApply:
            prod = defn.production_for_klabel(_term.label)
            if 'macro' in prod.att or 'alias' in prod.att or 'macro-rec' in prod.att or 'alias-rec' in prod.att:
                for r in defn.macro_rules:
                    assert type(r.body) is KRewrite
                    _new_term = r.body.apply_top(_term)
                    if _new_term != _term:
                        _term = _new_term
                        break
        return _term

    old_term = None
    while term != old_term:
        old_term = term
        term = bottom_up(_expand_macros, term)

    return term


def KPrint_make_unparsing(_self: KPrint, extra_modules: Iterable[KFlatModule] = ()) -> KPrint:  # noqa: N802
    modules = _self.definition.modules + tuple(extra_modules)
    main_module = KFlatModule('UNPARSING', [], [KImport(_m.name) for _m in modules])
    defn = KDefinition('UNPARSING', (main_module,) + modules)
    kprint = KPrint(_self.definition_dir)
    kprint._definition = defn
    kprint._symbol_table = None
    return kprint


def add_include_arg(includes: Iterable[str]) -> List[str]:
    return [arg for include in includes for arg in ['-I', include]]


def abstract_cell_vars(cterm: KInner, keep_vars: Collection[KVariable] = ()) -> KInner:
    state, _ = split_config_and_constraints(cterm)
    config, subst = split_config_from(state)
    for s in subst:
        if type(subst[s]) is KVariable and not is_anon_var(subst[s]) and subst[s] not in keep_vars:
            subst[s] = abstract_term_safely(KVariable('_'), base_name=s)
    return Subst(subst)(config)


def replace_special_chars(inp: str, c: str) -> str:
    return inp.replace('.', c).replace('-', c).replace('_', c).replace('/', c)
