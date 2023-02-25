import logging
import socket
from contextlib import closing
from pathlib import Path
from typing import Callable, Collection, Dict, Final, Iterable, List, Optional, Tuple, TypeVar

from pathos.pools import ProcessPool  # type: ignore
from pyk.cli_utils import BugReport
from pyk.cterm import CTerm
from pyk.kast.inner import KApply, KInner, KRewrite, KVariable, Subst
from pyk.kast.manip import (
    abstract_term_safely,
    bottom_up,
    flatten_label,
    is_anon_var,
    minimize_term,
    push_down_rewrites,
    split_config_and_constraints,
    split_config_from,
)
from pyk.kast.outer import KDefinition
from pyk.kcfg import KCFG, KCFGExplore
from pyk.ktool.kprint import KPrint
from pyk.ktool.kprove import KProve
from pyk.prelude.ml import mlAnd

_LOGGER: Final = logging.getLogger(__name__)

T1 = TypeVar('T1')
T2 = TypeVar('T2')


def find_free_port(host: str = 'localhost') -> int:
    with closing(socket.socket(socket.AF_INET, socket.SOCK_STREAM)) as s:
        s.bind((host, 0))
        s.setsockopt(socket.SOL_SOCKET, socket.SO_REUSEADDR, 1)
        return s.getsockname()[1]


def parallel_kcfg_explore(
    kprove: KProve,
    proof_problems: Dict[str, KCFG],
    save_directory: Optional[Path] = None,
    max_depth: int = 100,
    max_iterations: Optional[int] = None,
    workers: int = 1,
    break_every_step: bool = False,
    break_on_calls: bool = True,
    implication_every_block: bool = False,
    rpc_base_port: Optional[int] = None,
    is_terminal: Optional[Callable[[CTerm], bool]] = None,
    extract_branches: Optional[Callable[[CTerm], Iterable[KInner]]] = None,
    bug_report: Optional[BugReport] = None,
    use_booster_with_lib: Optional[str] = None,
) -> Dict[str, bool]:
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
                    'EVM.end',
                    'EVM.return.exception',
                    'EVM.return.revert',
                    'EVM.return.success',
                    'EVM.jumpi.true',
                    'EVM.jumpi.false',
                ]
            )
        base_port = rpc_base_port if rpc_base_port is not None else find_free_port()

        rpc_cmd = (
            [
                'hs-booster-proxy',
                '--llvm-backend-library',
                use_booster_with_lib,
                '-l',
                'warn',
            ]
            if use_booster_with_lib is not None
            else ['kore-rpc']
        )

        with KCFGExplore(
            kprove,
            port=(base_port + _index),
            bug_report=bug_report,
            kore_rpc_command=rpc_cmd,
        ) as kcfg_explore:
            try:
                _cfg = kcfg_explore.all_path_reachability_prove(
                    _cfgid,
                    _cfg,
                    cfg_dir=save_directory,
                    is_terminal=is_terminal,
                    extract_branches=extract_branches,
                    max_iterations=max_iterations,
                    execute_depth=max_depth,
                    terminal_rules=terminal_rules,
                    implication_every_block=implication_every_block,
                )
            except Exception as e:
                _LOGGER.error(f'Proof crashed: {_cfgid}\n{e}')
                return False

        failure_nodes = _cfg.frontier + _cfg.stuck
        if len(failure_nodes) == 0:
            _LOGGER.info(f'Proof passed: {_cfgid}')
            return True
        else:
            _LOGGER.error(f'Proof failed: {_cfgid}')
            return False

    with ProcessPool(ncpus=workers) as process_pool:
        _proof_problems = [(_id, _cfg, _i) for _i, (_id, _cfg) in enumerate(proof_problems.items())]
        results = process_pool.map(_call_rpc, _proof_problems)

    return {pid: result for pid, result in zip(proof_problems, results, strict=True)}


def arg_pair_of(
    fst_type: Callable[[str], T1], snd_type: Callable[[str], T2], delim: str = ','
) -> Callable[[str], Tuple[T1, T2]]:
    def parse(s: str) -> Tuple[T1, T2]:
        elems = s.split(delim)
        length = len(elems)
        if length != 2:
            raise ValueError(f'Expected 2 elements, found {length}')
        return fst_type(elems[0]), snd_type(elems[1])

    return parse


def byte_offset_to_lines(lines: Iterable[str], byte_start: int, byte_width: int) -> Tuple[List[str], int, int]:
    text_lines = []
    line_start = 0
    for l in lines:
        if len(l) < byte_start:
            byte_start -= len(l) + 1
            line_start += 1
        else:
            break
    line_end = line_start
    for l in list(lines)[line_start:]:
        if byte_start + byte_width < 0:
            break
        else:
            text_lines.append(l)
            byte_width -= len(l) + 1
            line_end += 1
    return (text_lines, line_start, line_end)


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


def abstract_cell_vars(cterm: KInner, keep_vars: Collection[KVariable] = ()) -> KInner:
    state, _ = split_config_and_constraints(cterm)
    config, subst = split_config_from(state)
    for s in subst:
        if type(subst[s]) is KVariable and not is_anon_var(subst[s]) and subst[s] not in keep_vars:
            subst[s] = abstract_term_safely(KVariable('_'), base_name=s)
    return Subst(subst)(config)


def cfg_dump_dot(kprint: KPrint, cfg_id: str, kcfgs_dir: Path) -> None:
    dot_dir = kcfgs_dir / 'dot'
    if not dot_dir.exists():
        dot_dir.mkdir()
    elif not dot_dir.is_dir():
        raise ValueError(f'Not a directory: {dot_dir}')

    kcfg = KCFGExplore.read_cfg(cfg_id, kcfgs_dir)
    if kcfg is None:
        raise ValueError(f'Could not load CFG {cfg_id} from {kcfgs_dir}')

    dot_file = dot_dir / f'{cfg_id}.dot'
    dot_file.write_text(kcfg.to_dot(kprint))
    _LOGGER.info(f'Wrote DOT file {cfg_id}: {dot_file}')

    for node in kcfg.nodes:
        node_file = dot_dir / f'node_config_{node.id}.txt'
        node_minimized_file = dot_dir / f'node_config_minimized_{node.id}.txt'
        node_constraint_file = dot_dir / f'node_constraint_{node.id}.txt'

        config = node.cterm.config
        if not node_file.exists():
            node_file.write_text(kprint.pretty_print(config))
            _LOGGER.info(f'Wrote node file {cfg_id}: {node_file}')
        config = minimize_term(config)
        if not node_minimized_file.exists():
            node_minimized_file.write_text(kprint.pretty_print(config))
            _LOGGER.info(f'Wrote node file {cfg_id}: {node_minimized_file}')
        if not node_constraint_file.exists():
            constraint = mlAnd(node.cterm.constraints)
            node_constraint_file.write_text(kprint.pretty_print(constraint))
            _LOGGER.info(f'Wrote node file {cfg_id}: {node_constraint_file}')

    for edge in kcfg.edges():
        edge_file = dot_dir / f'edge_config_{edge.source.id}_{edge.target.id}.txt'
        edge_minimized_file = dot_dir / f'edge_config_minimized_{edge.source.id}_{edge.target.id}.txt'
        edge_constraint_file = dot_dir / f'edge_constraint_{edge.source.id}_{edge.target.id}.txt'

        config = push_down_rewrites(KRewrite(edge.source.cterm.config, edge.target.cterm.config))
        if not edge_file.exists():
            edge_file.write_text(kprint.pretty_print(config))
            _LOGGER.info(f'Wrote edge file {cfg_id}: {edge_file}')
        config = minimize_term(config)
        if not edge_minimized_file.exists():
            edge_minimized_file.write_text(kprint.pretty_print(config))
            _LOGGER.info(f'Wrote edge file {cfg_id}: {edge_minimized_file}')
        if not edge_constraint_file.exists():
            edge_constraint_file.write_text(kprint.pretty_print(edge.condition))
            _LOGGER.info(f'Wrote edge file {cfg_id}: {edge_constraint_file}')

    for cover in kcfg.covers():
        cover_file = dot_dir / f'cover_config_{cover.source.id}_{cover.target.id}.txt'
        cover_constraint_file = dot_dir / f'cover_constraint_{cover.source.id}_{cover.target.id}.txt'

        subst_equalities = flatten_label('#And', cover.subst.ml_pred)

        if not cover_file.exists():
            cover_file.write_text('\n'.join(kprint.pretty_print(se) for se in subst_equalities))
            _LOGGER.info(f'Wrote cover file {cfg_id}: {cover_file}')
        if not cover_constraint_file.exists():
            cover_constraint_file.write_text(kprint.pretty_print(cover.constraint))
            _LOGGER.info(f'Wrote cover file {cfg_id}: {cover_constraint_file}')
