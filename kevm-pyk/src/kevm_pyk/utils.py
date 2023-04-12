from __future__ import annotations

import logging
from pathlib import Path
from typing import TYPE_CHECKING

from pathos.pools import ProcessPool  # type: ignore
from pyk.cterm import CTerm
from pyk.kast.inner import KApply, KRewrite, KVariable, Subst
from pyk.kast.manip import (
    abstract_term_safely,
    bottom_up,
    extract_lhs,
    extract_rhs,
    flatten_label,
    get_cell,
    is_anon_var,
    minimize_term,
    ml_pred_to_bool,
    push_down_rewrites,
    split_config_and_constraints,
    split_config_from,
)
from pyk.kcfg import KCFGExplore
from pyk.prelude import k
from pyk.prelude.ml import mlTop
from pyk.proof import AGProof, AGProver
from pyk.utils import single

if TYPE_CHECKING:
    from typing import Callable, Collection, Dict, Final, Iterable, List, Optional, Tuple, TypeVar, Union

    from pyk.kcfg import KCFG
    from pyk.cli_utils import BugReport
    from pyk.kast import KInner
    from pyk.kast.outer import KDefinition
    from pyk.ktool.kprove import KProve

    T1 = TypeVar('T1')
    T2 = TypeVar('T2')

_LOGGER: Final = logging.getLogger(__name__)


def get_ag_proof_for_spec(  # noqa: N802
    kprove: KProve,
    spec_file: Path,
    save_directory: Optional[Path],
    spec_module_name: Optional[str] = None,
    include_dirs: Iterable[Path] = (),
    md_selector: Optional[str] = None,
    claim_labels: Iterable[str] = (),
    exclude_claim_labels: Iterable[str] = (),
) -> AGProof:
    if save_directory is None:
        save_directory = Path('.')
        _LOGGER.info(f'Using default save_directory: {save_directory}')

    _LOGGER.info(f'Extracting claim from file: {spec_file}')
    claim = single(
        kprove.get_claims(
            spec_file,
            spec_module_name=spec_module_name,
            include_dirs=include_dirs,
            md_selector=md_selector,
            claim_labels=claim_labels,
            exclude_claim_labels=exclude_claim_labels,
        )
    )

    ag_proof = AGProof.read_proof(claim.label, save_directory)
    assert type(ag_proof) is AGProof
    return ag_proof


def parallel_kcfg_explore(
    kprove: KProve,
    proof_problems: Dict[str, AGProof],
    save_directory: Optional[Path] = None,
    max_depth: int = 1000,
    max_iterations: Optional[int] = None,
    workers: int = 1,
    break_every_step: bool = False,
    break_on_jumpi: bool = False,
    break_on_calls: bool = True,
    implication_every_block: bool = False,
    is_terminal: Optional[Callable[[CTerm], bool]] = None,
    extract_branches: Optional[Callable[[CTerm], Iterable[KInner]]] = None,
    bug_report: Optional[BugReport] = None,
    kore_rpc_command: Union[str, Iterable[str]] = ('kore-rpc',),
    smt_timeout: Optional[int] = None,
    smt_retry_limit: Optional[int] = None,
) -> Dict[str, bool]:
    def _call_rpc(packed_args: Tuple[str, AGProof, int]) -> bool:
        _cfgid, _ag_proof, _index = packed_args
        terminal_rules = ['EVM.halt']
        if break_every_step:
            terminal_rules.append('EVM.step')
        if break_on_jumpi:
            terminal_rules.extend(['EVM.jumpi.true', 'EVM.jumpi.false'])
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
                ]
            )

        with KCFGExplore(
            kprove,
            bug_report=bug_report,
            kore_rpc_command=kore_rpc_command,
            smt_timeout=smt_timeout,
            smt_retry_limit=smt_retry_limit,
        ) as kcfg_explore:
            ag_prover = AGProver(_ag_proof)
            try:
                _cfg = ag_prover.advance_proof(
                    kcfg_explore,
                    is_terminal=is_terminal,
                    extract_branches=extract_branches,
                    max_iterations=max_iterations,
                    execute_depth=max_depth,
                    terminal_rules=terminal_rules,
                    implication_every_block=implication_every_block,
                )
            except Exception as e:
                _LOGGER.error(f'Proof crashed: {_cfgid}\n{e}', exc_info=True)
                return False

            failure_nodes = _cfg.frontier + _cfg.stuck
            if len(failure_nodes) == 0:
                _LOGGER.info(f'Proof passed: {_cfgid}')
                return True
            else:
                _LOGGER.error(f'Proof failed: {_cfgid}')
                failure_log = print_failure_info(_cfg, _cfgid, kcfg_explore)
                for line in failure_log:
                    _LOGGER.error(line)
                return False

    with ProcessPool(ncpus=workers) as process_pool:
        _proof_problems = [(_id, _cfg, _i) for _i, (_id, _cfg) in enumerate(proof_problems.items())]
        results = process_pool.map(_call_rpc, _proof_problems)

    return dict(zip(proof_problems, results, strict=True))


def print_failure_info(_cfg: KCFG, _cfgid: str, kcfg_explore: KCFGExplore) -> list[str]:
    unique_target = _cfg.get_unique_target()

    res_lines: list[str] = []

    num_frontier = len(_cfg.frontier)
    num_stuck = len(_cfg.stuck)
    res_lines.append(f'{num_frontier + num_stuck} Failure nodes. ({num_frontier} frontier and {num_stuck} stuck)')
    if num_frontier > 0:
        res_lines.append('')
        res_lines.append('Frontier nodes:')
        for node in _cfg.frontier:
            res_lines.append('')
            res_lines.append(f'ID: {node.id}:')
    if num_stuck > 0:
        res_lines.append('')
        res_lines.append('Stuck nodes:')
        for node in _cfg.stuck:

            node_cterm = CTerm.from_kast(kcfg_explore.cterm_simplify(node.cterm))
            target_cterm = CTerm.from_kast(kcfg_explore.cterm_simplify(unique_target.cterm))

            res_lines.append('')
            res_lines.append(f'ID: {node.id}:')
            res_lines.append('Failed subsumption into the target node because:')
            _, reason = check_implication(kcfg_explore, node_cterm, target_cterm)
            res_lines += reason.split('\n')

    return res_lines


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
    _LOGGER.info(f'byte_start: {byte_start}')
    _LOGGER.info(f'byte_width: {byte_width}')
    _LOGGER.info('lines:')
    for line in lines:
        _LOGGER.info(line)
    text_lines = []
    line_start = 0
    for line in lines:
        if len(line) < byte_start:
            byte_start -= len(line) + 1
            line_start += 1
        else:
            break
    line_end = line_start
    for line in list(lines)[line_start:]:
        if byte_start + byte_width < 0:
            break
        else:
            text_lines.append(line)
            byte_width -= len(line) + 1
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


def check_implication(kcfg_explore: KCFGExplore, concrete: CTerm, abstract: CTerm) -> Tuple[bool, str]:
    def _is_cell_subst(csubst: KInner) -> bool:
        if type(csubst) is KApply and csubst.label.name == '_==K_':
            csubst_arg = csubst.args[0]
            if type(csubst_arg) is KVariable and csubst_arg.name.endswith('_CELL'):
                return True
        return False

    def _is_negative_cell_subst(constraint: KInner) -> bool:
        constraint_bool = ml_pred_to_bool(constraint)
        if type(constraint_bool) is KApply and constraint_bool.label.name == 'notBool_':
            negative_constraint = constraint_bool.args[0]
            if type(negative_constraint) is KApply and negative_constraint.label.name == '_andBool_':
                constraints = flatten_label('_andBool_', negative_constraint)
                cell_constraints = list(filter(_is_cell_subst, constraints))
                if len(cell_constraints) > 0:
                    return True
        return False

    concrete_config, *concrete_constraints = concrete
    abstract_config, *abstract_constraints = abstract
    config_match = abstract_config.match(concrete_config)
    if config_match is None:
        _, concrete_subst = split_config_from(concrete_config)
        cell_names = concrete_subst.keys()
        failing_cells = []
        for cell in cell_names:
            concrete_cell = get_cell(concrete_config, cell)
            abstract_cell = get_cell(abstract_config, cell)
            _LOGGER.info(f'concrete_cell: {concrete_cell}')
            _LOGGER.info(f'abstract_cell: {abstract_cell}')
            cell_match = abstract_cell.match(concrete_cell)
            _LOGGER.info(f'cell_match: {cell_match}')
            if cell_match is None:
                failing_cell = push_down_rewrites(KRewrite(concrete_cell, abstract_cell))
                failing_cell = no_cell_rewrite_to_dots(failing_cell)
                failing_cells.append((cell, failing_cell))
            else:
                abstract_config = cell_match.apply(abstract_config)
        failing_cells_str = '\n'.join(
            f'{cell}: {kcfg_explore.kprint.pretty_print(minimize_term(rew))}' for cell, rew in failing_cells
        )
        return (
            False,
            f'Structural matching failed, the following cells failed individually (abstract => concrete):\n{failing_cells_str}',
        )
    else:
        abstract_constraints = [config_match.apply(abstract_constraint) for abstract_constraint in abstract_constraints]
        abstract_constraints = list(
            filter(
                lambda x: not CTerm._is_spurious_constraint(x),
                [config_match.apply(abstract_constraint) for abstract_constraint in abstract_constraints],
            )
        )
        impl = CTerm._ml_impl(concrete_constraints, abstract_constraints)
        if impl != mlTop(k.GENERATED_TOP_CELL):
            fail_str = kcfg_explore.kprint.pretty_print(impl)
            negative_cell_constraints = list(filter(_is_negative_cell_subst, concrete_constraints))
            if len(negative_cell_constraints) > 0:
                fail_str = f'{fail_str}\n\nNegated cell substitutions found (consider using _ => ?_):\n' + '\n'.join(
                    [kcfg_explore.kprint.pretty_print(cc) for cc in negative_cell_constraints]
                )
            return (False, f'Implication check failed, the following is the remaining implication:\n{fail_str}')
    return (True, '')


def no_cell_rewrite_to_dots(term: KInner) -> KInner:
    def _no_cell_rewrite_to_dots(_term: KInner) -> KInner:
        if type(_term) is KApply and _term.is_cell:
            lhs = extract_lhs(_term)
            rhs = extract_rhs(_term)
            if lhs == rhs:
                return KApply(_term.label, [abstract_term_safely(lhs, base_name=_term.label.name)])
        return _term

    return bottom_up(_no_cell_rewrite_to_dots, term)
