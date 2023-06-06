from __future__ import annotations

import logging
import sys
from pathlib import Path
from typing import TYPE_CHECKING

import pytest
from pyk.prelude.ml import mlTop

from kevm_pyk import config
from kevm_pyk.__main__ import exec_prove
from kevm_pyk.kevm import KEVM
from kevm_pyk.kompile import KompileTarget, kevm_kompile

if TYPE_CHECKING:
    from typing import Any, Final

    from pytest import LogCaptureFixture


sys.setrecursionlimit(10**8)

REPO_ROOT: Final = Path(__file__).parents[4]
TEST_DIR: Final = REPO_ROOT / 'tests'
SPEC_DIR: Final = TEST_DIR / 'specs'


def spec_files(dir_name: str, glob: str) -> tuple[Path, ...]:
    test_dir = SPEC_DIR / dir_name
    res = tuple(test_dir.glob(glob))
    assert res
    return res


BENCHMARK_TESTS: Final = spec_files('benchmarks', '*-spec.k')
FUNCTIONAL_TESTS: Final = spec_files('functional', '*-spec.k')
OPCODES_TESTS: Final = spec_files('opcodes', '*-spec.k')
ERC20_TESTS: Final = spec_files('erc20', '*/*-spec.k')
BIHU_TESTS: Final = spec_files('bihu', '*-spec.k')
EXAMPLES_TESTS: Final = spec_files('examples', '*-spec.k') + spec_files('examples', '*-spec.md')
MCD_TESTS: Final = spec_files('mcd', '*-spec.k')
OPTIMIZATION_TESTS: Final = (SPEC_DIR / 'opcodes/evm-optimizations-spec.md',)

ALL_TESTS: Final = sum(
    [
        BENCHMARK_TESTS,
        FUNCTIONAL_TESTS,
        OPCODES_TESTS,
        ERC20_TESTS,
        BIHU_TESTS,
        EXAMPLES_TESTS,
        MCD_TESTS,
        OPTIMIZATION_TESTS,
    ],
    (),
)


def exclude_list(exclude_file: Path) -> list[Path]:
    res = [REPO_ROOT / test_path for test_path in exclude_file.read_text().splitlines()]
    assert res
    return res


FAILING_PYK_TESTS: Final = exclude_list(TEST_DIR / 'failing-symbolic.pyk')
SLOW_TESTS: Final = exclude_list(TEST_DIR / 'slow.haskell')
FAILING_TESTS: Final = exclude_list(TEST_DIR / 'failing-symbolic.haskell')


KOMPILE_MODULE: Final = {
    'benchmarks/functional-spec.k': 'FUNCTIONAL-SPEC-SYNTAX',
    'bihu/functional-spec.k': 'FUNCTIONAL-SPEC-SYNTAX',
    'erc20/functional-spec.k': 'FUNCTIONAL-SPEC-SYNTAX',
    'mcd/functional-spec.k': 'FUNCTIONAL-SPEC-SYNTAX',
    'opcodes/evm-optimizations-spec.md': 'EVM-OPTIMIZATIONS-SPEC-LEMMAS',
}

PROVE_ARGS: Final[dict[str, Any]] = {
    'functional/lemmas-no-smt-spec.k': {
        'haskell_args': ['--smt=none'],
    },
}


SKIPPED_PYK_TESTS: Final = set().union(SLOW_TESTS, FAILING_TESTS, FAILING_PYK_TESTS)


@pytest.mark.parametrize(
    'spec_file',
    ALL_TESTS,
    ids=[str(spec_file.relative_to(SPEC_DIR)) for spec_file in ALL_TESTS],
)
def test_pyk_prove(spec_file: Path, tmp_path: Path) -> None:
    if spec_file in SKIPPED_PYK_TESTS:
        pytest.skip()

    # Given
    spec_id = str(spec_file.relative_to(SPEC_DIR))
    definition_dir = tmp_path / 'kompiled'
    use_directory = tmp_path / 'kprove'
    use_directory.mkdir()

    # When
    module_name = KOMPILE_MODULE.get(spec_id, 'VERIFICATION')

    kevm_kompile(
        target=KompileTarget.HASKELL,
        main_file=spec_file,
        output_dir=definition_dir,
        main_module=module_name,
        syntax_module=module_name,
    )

    exec_prove(
        spec_file=spec_file,
        definition_dir=definition_dir,
        includes=[str(config.INCLUDE_DIR)],
        save_directory=use_directory,
        smt_timeout=125,
        smt_retry_limit=4,
        md_selector='foo',  # TODO Ignored flag, this is to avoid KeyError
    )


SKIPPED_LEGACY_TESTS: Final = set().union(SLOW_TESTS, FAILING_TESTS)


@pytest.mark.parametrize(
    'spec_file',
    FAILING_PYK_TESTS,
    ids=[str(spec_file.relative_to(SPEC_DIR)) for spec_file in FAILING_PYK_TESTS],
)
def test_legacy_prove(spec_file: Path, tmp_path: Path, caplog: LogCaptureFixture) -> None:
    caplog.set_level(logging.INFO)

    if spec_file in SKIPPED_LEGACY_TESTS:
        pytest.skip()

    # Given
    spec_id = str(spec_file.relative_to(SPEC_DIR))
    log_file = tmp_path / 'log.txt'
    definition_dir = tmp_path / 'kompiled'
    use_directory = tmp_path / 'kprove'
    use_directory.mkdir()

    # When
    module_name = KOMPILE_MODULE.get(spec_id, 'VERIFICATION')
    args = PROVE_ARGS.get(spec_id, {})

    try:
        kevm_kompile(
            target=KompileTarget.HASKELL,
            main_file=spec_file,
            output_dir=definition_dir,
            main_module=module_name,
            syntax_module=module_name,
        )

        kevm = KEVM(definition_dir, use_directory=use_directory)
        actual = kevm.prove(spec_file=spec_file, include_dirs=[config.INCLUDE_DIR], **args)
    except BaseException:
        raise
    finally:
        log_file.write_text(caplog.text)

    # Then
    assert actual == mlTop('K')
