from __future__ import annotations

import logging
from pathlib import Path
from typing import TYPE_CHECKING

from pathos.pools import ProcessPool  # type: ignore
from pyk.kast.inner import KApply, KRewrite, KVariable, Subst
from pyk.kast.manip import abstract_term_safely, bottom_up, is_anon_var, split_config_and_constraints, split_config_from
from pyk.kcfg import KCFGExplore
from pyk.proof import AGProof, AGProver
from pyk.utils import single

if TYPE_CHECKING:
    from collections.abc import Callable, Collection, Iterable
    from typing import Final, TypeVar

    from pyk.cli_utils import BugReport
    from pyk.cterm import CTerm
    from pyk.kast import KInner
    from pyk.kast.outer import KDefinition
    from pyk.ktool.kprove import KProve

    T1 = TypeVar('T1')
    T2 = TypeVar('T2')

_LOGGER: Final = logging.getLogger(__name__)


def get_ag_proof_for_spec(  # noqa: N802
    kprove: KProve,
    spec_file: Path,
    save_directory: Path | None,
    spec_module_name: str | None = None,
    include_dirs: Iterable[Path] = (),
    md_selector: str | None = None,
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
    return ag_proof


def parallel_kcfg_explore(
    kprove: KProve,
    proof_problems: dict[str, AGProof],
    save_directory: Path | None = None,
    max_depth: int = 1000,
    max_iterations: int | None = None,
    workers: int = 1,
    break_every_step: bool = False,
    break_on_jumpi: bool = False,
    break_on_calls: bool = True,
    implication_every_block: bool = False,
    is_terminal: Callable[[CTerm], bool] | None = None,
    extract_branches: Callable[[CTerm], Iterable[KInner]] | None = None,
    bug_report: BugReport | None = None,
    kore_rpc_command: str | Iterable[str] = ('kore-rpc',),
    smt_timeout: int | None = None,
    smt_retry_limit: int | None = None,
) -> dict[str, bool]:
    def _call_rpc(packed_args: tuple[str, AGProof, int]) -> bool:
        _cfgid, _ag_proof, _index = packed_args
        terminal_rules = ['EVM.halt']
        cut_point_rules = []
        if break_every_step:
            cut_point_rules.append('EVM.step')
        if break_on_jumpi:
            cut_point_rules.extend(['EVM.jumpi.true', 'EVM.jumpi.false'])
        if break_on_calls:
            cut_point_rules.extend(
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
            id=_ag_proof.id,
            bug_report=bug_report,
            kore_rpc_command=kore_rpc_command,
            smt_timeout=smt_timeout,
            smt_retry_limit=smt_retry_limit,
        ) as kcfg_explore:
            ag_prover = AGProver(_ag_proof, is_terminal=is_terminal, extract_branches=extract_branches)
            try:
                _cfg = ag_prover.advance_proof(
                    kcfg_explore,
                    max_iterations=max_iterations,
                    execute_depth=max_depth,
                    terminal_rules=terminal_rules,
                    cut_point_rules=cut_point_rules,
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
            return False

    with ProcessPool(ncpus=workers) as process_pool:
        _proof_problems = [(_id, _cfg, _i) for _i, (_id, _cfg) in enumerate(proof_problems.items())]
        results = process_pool.map(_call_rpc, _proof_problems)

    return dict(zip(proof_problems, results, strict=True))


def arg_pair_of(
    fst_type: Callable[[str], T1], snd_type: Callable[[str], T2], delim: str = ','
) -> Callable[[str], tuple[T1, T2]]:
    def parse(s: str) -> tuple[T1, T2]:
        elems = s.split(delim)
        length = len(elems)
        if length != 2:
            raise ValueError(f'Expected 2 elements, found {length}')
        return fst_type(elems[0]), snd_type(elems[1])

    return parse


def byte_offset_to_lines(lines: Iterable[str], byte_start: int, byte_width: int) -> tuple[list[str], int, int]:
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
