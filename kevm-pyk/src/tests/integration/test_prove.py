from __future__ import annotations

import logging
import sys
from pathlib import Path
from typing import TYPE_CHECKING, NamedTuple

import pytest
from filelock import SoftFileLock
from pyk.kast.att import AttEntry, Atts, KAtt
from pyk.kast.outer import KClaim
from pyk.kdist import kdist
from pyk.prelude.ml import is_top
from pyk.proof.reachability import APRProof, APRProver
from pyk.proof.show import APRProofShow

from kevm_pyk import config
from kevm_pyk.__main__ import exec_prove
from kevm_pyk.cli import ProveOptions
from kevm_pyk.kevm import KEVM, KEVMSemantics, kevm_node_printer
from kevm_pyk.kompile import KompileTarget, kevm_kompile
from kevm_pyk.utils import initialize_apr_proof, legacy_explore

from ..utils import REPO_ROOT

if TYPE_CHECKING:
    from collections.abc import Callable
    from typing import Any, Final

    from pyk.utils import BugReport
    from pytest import LogCaptureFixture, TempPathFactory


sys.setrecursionlimit(10**8)

TEST_DIR: Final = REPO_ROOT / 'tests'
SPEC_DIR: Final = TEST_DIR / 'specs'

_LOGGER: Final = logging.getLogger(__name__)
_LOG_FORMAT: Final = '%(levelname)s %(asctime)s %(name)s - %(message)s'


# -------------------
# Test specifications
# -------------------


def spec_files(dir_name: str, glob: str) -> tuple[Path, ...]:
    test_dir = SPEC_DIR / dir_name
    res = tuple(test_dir.glob(glob))
    assert res
    return res


BENCHMARK_TESTS: Final = spec_files('benchmarks', '*-spec.k')
FUNCTIONAL_TESTS: Final = spec_files('functional', '*-spec.k')
ERC20_TESTS: Final = spec_files('erc20', '*/*-spec.k')
EXAMPLES_TESTS: Final = spec_files('examples', '*-spec.k') + spec_files('examples', '*-spec.md')
MCD_TESTS: Final = spec_files('mcd', '*-spec.k')
VAT_TESTS: Final = spec_files('mcd', 'vat*-spec.k')
NON_VAT_MCD_TESTS: Final = tuple(test for test in MCD_TESTS if test not in VAT_TESTS)
KONTROL_TESTS: Final = spec_files('kontrol', '*-spec.k')

ALL_TESTS: Final = sum(
    [
        BENCHMARK_TESTS,
        FUNCTIONAL_TESTS,
        ERC20_TESTS,
        EXAMPLES_TESTS,
        NON_VAT_MCD_TESTS,
        KONTROL_TESTS,
    ],
    (),
)


def exclude_list(exclude_file: Path) -> list[Path]:
    res = [REPO_ROOT / test_path for test_path in exclude_file.read_text().splitlines()]
    assert res
    return res


FAILING_PYK_TESTS: Final = exclude_list(TEST_DIR / 'failing-symbolic.pyk')
FAILING_BOOSTER_TESTS: Final = exclude_list(TEST_DIR / 'failing-symbolic.haskell-booster')
FAILING_BOOSTER_DEV_TESTS: Final = exclude_list(TEST_DIR / 'failing-symbolic.haskell-booster-dev')
FAILING_TESTS: Final = exclude_list(TEST_DIR / 'failing-symbolic.haskell')


# -----------
# Kompilation
# -----------


KOMPILE_MAIN_FILE: Final = {
    'benchmarks/functional-spec.k': 'functional-spec.k',
    'examples/solidity-code-spec.md': 'solidity-code-spec.md',
    'examples/erc20-spec.md': 'erc20-spec.md',
    'examples/erc721-spec.md': 'erc721-spec.md',
    'examples/storage-spec.md': 'storage-spec.md',
    'examples/sum-to-n-spec.k': 'sum-to-n-spec.k',
    'examples/sum-to-n-foundry-spec.k': 'sum-to-n-foundry-spec.k',
    'functional/infinite-gas-spec.k': 'infinite-gas-spec.k',
    'functional/evm-int-simplifications-spec.k': 'evm-int-simplifications-spec.k',
    'functional/int-simplifications-spec.k': 'int-simplifications-spec.k',
    'functional/lemmas-no-smt-spec.k': 'lemmas-no-smt-spec.k',
    'functional/lemmas-spec.k': 'lemmas-spec.k',
    'functional/abi-spec.k': 'abi-spec.k',
    'functional/merkle-spec.k': 'merkle-spec.k',
    'functional/storageRoot-spec.k': 'storageRoot-spec.k',
    'mcd/functional-spec.k': 'functional-spec.k',
}

KOMPILE_MAIN_MODULE: Final = {
    'benchmarks/functional-spec.k': 'FUNCTIONAL-SPEC-SYNTAX',
    'erc20/functional-spec.k': 'FUNCTIONAL-SPEC-SYNTAX',
    'mcd/functional-spec.k': 'FUNCTIONAL-SPEC-SYNTAX',
}


class Target(NamedTuple):
    main_file: Path
    main_module_name: str

    @property
    def id(self) -> str:
        """
        The target's id is the two trailing path segments and the main module name
        """
        return f'{self.main_file.parts[-2]}-{self.main_file.stem}-{self.main_module_name}'

    def __call__(self, output_dir: Path) -> Path:
        return kevm_kompile(
            output_dir=output_dir,
            target=KompileTarget.HASKELL,
            main_file=self.main_file,
            main_module=self.main_module_name,
            syntax_module=self.main_module_name,
            debug=True,
        )


@pytest.fixture(scope='module')
def target_dir(kompiled_targets_dir: Path | None, tmp_path_factory: TempPathFactory) -> Path:
    if kompiled_targets_dir:
        kompiled_targets_dir.mkdir(parents=True, exist_ok=True)
        return kompiled_targets_dir

    return tmp_path_factory.mktemp('kompiled')


@pytest.fixture(scope='module')
def kompiled_target_for(target_dir: Path) -> Callable[[Path], Path]:
    """
    Generate a function that returns a path to the kompiled defintion for a given K spec. Invoke `kompile` only if no kompiled directory is cached for the spec.
    """

    def kompile(spec_file: Path) -> Path:
        target = _target_for_spec(spec_file)
        lock_file = target_dir / f'{target.id}.lock'
        output_dir = target_dir / target.id
        with SoftFileLock(lock_file):
            if output_dir.exists():
                return output_dir
            return target(output_dir)

    return kompile


def _target_for_spec(spec_file: Path) -> Target:
    spec_file = spec_file.resolve()
    spec_id = str(spec_file.relative_to(SPEC_DIR))
    spec_root = SPEC_DIR / spec_file.relative_to(SPEC_DIR).parents[-2]
    main_file = spec_root / KOMPILE_MAIN_FILE.get(spec_id, 'verification.k')
    main_module_name = KOMPILE_MAIN_MODULE.get(spec_id, 'VERIFICATION')
    return Target(main_file, main_module_name)


@pytest.mark.parametrize(
    'spec_file',
    ALL_TESTS,
    ids=[str(spec_file.relative_to(SPEC_DIR)) for spec_file in ALL_TESTS],
)
def test_kompile_targets(
    spec_file: Path, kompiled_target_for: Callable[[Path], Path], kompiled_targets_dir: Path | None
) -> None:
    """
    This test function is intended to be used to pre-kompile all definitions,
    so that the actual proof tests do not need to do the actual compilation,
    which is disturbing performance measurment.

    To achieve the desired caching, this test should be run like this:
    pytest src/tests/integration/test_prove.py::test_kompile_targets --kompiled-targets-dir ./prekompiled

    This test will be skipped if no --kompiled-targets-dir option is given
    """
    if not kompiled_targets_dir or spec_file in FAILING_BOOSTER_TESTS:
        pytest.skip()

    kompiled_target_for(spec_file)


# ---------
# Pyk tests
# ---------


class TParams:
    main_claim_id: str | None
    leaf_number: int | None
    break_on_calls: bool

    def __init__(
        self, main_claim_id: str | None = None, leaf_number: int | None = None, break_on_calls: bool = False
    ) -> None:
        self.main_claim_id = main_claim_id
        self.leaf_number = leaf_number
        self.break_on_calls = break_on_calls


TEST_PARAMS: dict[str, TParams] = {
    'mcd/vat-slip-pass-rough-spec.k': TParams(
        main_claim_id='VAT-SLIP-PASS-ROUGH-SPEC.Vat.slip.pass.rough',
        leaf_number=1,
    ),
}


for KONTROL_TEST in KONTROL_TESTS:
    TEST_PARAMS[f'kontrol/{KONTROL_TEST.name}'] = TParams(break_on_calls=True)  # noqa: B909


def leaf_number(proof: APRProof) -> int:
    non_target_leaves = [nd for nd in proof.kcfg.leaves if not proof.is_target(nd.id)]
    return len(non_target_leaves) + len(proof.kcfg.predecessors(proof.target))


@pytest.mark.parametrize(
    'spec_file',
    ALL_TESTS,
    ids=[str(spec_file.relative_to(SPEC_DIR)) for spec_file in ALL_TESTS],
)
def test_pyk_prove(
    spec_file: Path,
    kompiled_target_for: Callable[[Path], Path],
    tmp_path: Path,
    caplog: LogCaptureFixture,
    no_use_booster: bool,
    use_booster_dev: bool,
    bug_report: BugReport | None,
    spec_name: str | None,
) -> None:
    caplog.set_level(logging.INFO)

    if (
        (no_use_booster and spec_file in FAILING_PYK_TESTS)
        or (use_booster_dev and spec_file in FAILING_BOOSTER_DEV_TESTS)
        or (not no_use_booster and not use_booster_dev and spec_file in FAILING_BOOSTER_TESTS)
    ):
        pytest.skip()

    if spec_name is not None and str(spec_file).find(spec_name) < 0:
        pytest.skip()

    # Given
    log_file = tmp_path / 'log.txt'
    use_directory = tmp_path / 'kprove'
    use_directory.mkdir()

    # When
    try:
        definition_dir = kompiled_target_for(spec_file)
        name = str(spec_file.relative_to(SPEC_DIR))
        break_on_calls = name in TEST_PARAMS and TEST_PARAMS[name].break_on_calls
        options = ProveOptions(
            {
                'spec_file': spec_file,
                'definition_dir': definition_dir,
                'includes': [str(include_dir) for include_dir in config.INCLUDE_DIRS],
                'save_directory': use_directory,
                'md_selector': 'foo',  # TODO Ignored flag, this is to avoid KeyError
                'use_booster': not no_use_booster,
                'use_booster_dev': use_booster_dev,
                'bug_report': bug_report,
                'break_on_calls': break_on_calls,
            }
        )
        exec_prove(options=options)
        if name in TEST_PARAMS:
            params = TEST_PARAMS[name]
            if params.leaf_number is not None and params.main_claim_id is not None:
                apr_proof = APRProof.read_proof_data(
                    proof_dir=use_directory,
                    id=params.main_claim_id,
                )
                expected_leaf_number = params.leaf_number
                actual_leaf_number = leaf_number(apr_proof)
                assert expected_leaf_number == actual_leaf_number
    except BaseException:
        raise
    finally:
        log_file.write_text(caplog.text)


def test_prove_optimizations(
    kompiled_target_for: Callable[[Path], Path],
    tmp_path: Path,
    caplog: LogCaptureFixture,
    use_booster_dev: bool,
    bug_report: BugReport | None,
) -> None:
    caplog.set_level(logging.INFO)

    def _get_optimization_proofs() -> list[APRProof]:
        _defn_dir = kdist.get('evm-semantics.haskell')
        _kevm = KEVM(_defn_dir)
        _optimization_rules = _kevm.definition.module('EVM-OPTIMIZATIONS').rules
        _claims = [
            KClaim(
                rule.body, requires=rule.requires, ensures=rule.ensures, att=KAtt([AttEntry(Atts.LABEL, rule.label)])
            )
            for rule in _optimization_rules
        ]
        return [APRProof.from_claim(kevm.definition, claim, {}) for claim in _claims]

    spec_file = REPO_ROOT / 'tests/specs/opcodes/evm-optimizations-spec.k'
    definition_dir = kompiled_target_for(spec_file)
    kevm = KEVM(definition_dir)

    kore_rpc_command = ('booster-dev',) if use_booster_dev else ('kore-rpc-booster',)

    with legacy_explore(
        kevm, kcfg_semantics=KEVMSemantics(allow_symbolic_program=True), kore_rpc_command=kore_rpc_command
    ) as kcfg_explore:
        prover = APRProver(
            kcfg_explore,
            execute_depth=20,
            terminal_rules=[],
            cut_point_rules=['EVM.pc.inc'],
            counterexample_info=False,
            always_check_subsumption=True,
            fast_check_subsumption=True,
        )
        for proof in _get_optimization_proofs():
            initialize_apr_proof(kcfg_explore.cterm_symbolic, proof)
            prover.advance_proof(proof, max_iterations=10)
            node_printer = kevm_node_printer(kevm, proof)
            proof_show = APRProofShow(kevm, node_printer=node_printer)
            proof_display = '\n'.join('    ' + line for line in proof_show.show(proof))
            _LOGGER.info(f'Proof {proof.id}:\n{proof_display}')
            assert proof.passed


def test_prove_dss(
    kompiled_target_for: Callable[[Path], Path],
    tmp_path: Path,
    caplog: LogCaptureFixture,
    bug_report: BugReport | None,
    spec_name: str | None,
    workers: int = 8,
) -> None:
    spec_file = Path('../tests/specs/mcd/vat-spec.k')
    caplog.set_level(logging.INFO)

    if spec_name is not None and str(spec_file).find(spec_name) < 0:
        pytest.skip()

    # Given
    log_file = tmp_path / 'log.txt'
    use_directory = tmp_path / 'kprove'
    use_directory.mkdir()

    # When
    try:
        definition_dir = kompiled_target_for(spec_file)
        options = ProveOptions(
            {
                'spec_file': spec_file,
                'definition_dir': definition_dir,
                'includes': [str(include_dir) for include_dir in config.INCLUDE_DIRS],
                'save_directory': use_directory,
                'md_selector': 'foo',  # TODO Ignored flag, this is to avoid KeyError
                'use_booster': True,
                'bug_report': bug_report,
                'break_on_calls': False,
                'workers': workers,
            }
        )
        exec_prove(options=options)
    except BaseException:
        raise
    finally:
        log_file.write_text(caplog.text)


# ------------
# Legacy tests
# ------------


PROVE_ARGS: Final[dict[str, Any]] = {
    'functional/lemmas-no-smt-spec.k': {
        'haskell_args': ['--smt=none'],
    },
}


@pytest.mark.parametrize(
    'spec_file',
    FAILING_PYK_TESTS,
    ids=[str(spec_file.relative_to(SPEC_DIR)) for spec_file in FAILING_PYK_TESTS],
)
def test_kprove_prove(
    spec_file: Path,
    kompiled_target_for: Callable[[Path], Path],
    tmp_path: Path,
    caplog: LogCaptureFixture,
    bug_report: BugReport | None,
) -> None:
    caplog.set_level(logging.INFO)

    if spec_file in FAILING_TESTS:
        pytest.skip()

    # Given
    spec_id = str(spec_file.relative_to(SPEC_DIR))
    args = PROVE_ARGS.get(spec_id, {})
    if 'haskell_args' not in args:
        args['haskell_args'] = []
    args['haskell_args'] += ['--smt-timeout', '300']
    args['haskell_args'] += ['--smt-retry-limit', '10']

    log_file = tmp_path / 'log.txt'
    use_directory = tmp_path / 'kprove'
    use_directory.mkdir()

    # When
    try:
        definition_dir = kompiled_target_for(spec_file)
        kevm = KEVM(definition_dir, use_directory=use_directory)
        actual = kevm.prove(spec_file=spec_file, include_dirs=list(config.INCLUDE_DIRS), **args)
    except BaseException:
        raise
    finally:
        log_file.write_text(caplog.text)

    # Then
    assert len(actual) == 1
    assert is_top(actual[0].kast, weak=True)
