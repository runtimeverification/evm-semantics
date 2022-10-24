from logging import Logger
from typing import Collection, Iterable, List, Optional, Tuple

from pyk.kast import KApply, KClaim, KDefinition, KFlatModule, KImport, KInner, KRule, KVariable
from pyk.kastManip import abstract_term_safely, is_anon_var, split_config_and_constraints, split_config_from, substitute
from pyk.ktool import KPrint, KProve


def KProve_prove_claim(  # noqa: N802
    kprove: KProve,
    claim: KClaim,
    claim_id: str,
    logger: Logger,
    depth: Optional[int] = None,
    lemmas: Iterable[KRule] = (),
) -> Tuple[bool, KInner]:
    logger.info(f'Proving claim: {claim_id}')
    prove_args = []
    if depth is not None:
        prove_args += ['--depth', str(depth)]
    result = kprove.prove_claim(claim, claim_id, args=prove_args, lemmas=lemmas)
    failed = False
    if type(result) is KApply and result.label.name == '#Top':
        logger.info(f'Proved claim: {claim_id}')
    else:
        logger.error(f'Failed to prove claim: {claim_id}')
        failed = True
    return failed, result


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
    return substitute(config, subst)
