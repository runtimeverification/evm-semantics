from __future__ import annotations

from distutils.dir_util import copy_tree
from typing import TYPE_CHECKING

import pytest
from pyk.utils import run_process

from kevm_pyk import config
from kevm_pyk.foundry import foundry_kompile, foundry_prove, foundry_show

from .utils import TEST_DATA_DIR

if TYPE_CHECKING:
    from pathlib import Path
    from typing import Final

    from pytest import TempPathFactory


FORGE_STD_REF: Final = '27e14b7'


@pytest.fixture(scope='module')  # TODO should reduce scope
def foundry_root(tmp_path_factory: TempPathFactory, use_booster: bool) -> Path:
    foundry_root = tmp_path_factory.mktemp('foundry')
    copy_tree(str(TEST_DATA_DIR / 'foundry'), str(foundry_root))

    run_process(['forge', 'install', '--no-git', f'foundry-rs/forge-std@{FORGE_STD_REF}'], cwd=foundry_root)
    run_process(['forge', 'build'], cwd=foundry_root)

    foundry_kompile(
        definition_dir=config.FOUNDRY_DIR,
        foundry_root=foundry_root,
        includes=(),
        requires=[str(TEST_DATA_DIR / 'lemmas.k')],
        imports=['LoopsTest:SUM-TO-N-INVARIANT'],
        llvm_library=use_booster,
    )

    return foundry_root


def test_foundry_kompile(foundry_root: Path, update_expected_output: bool, use_booster: bool) -> None:
    if use_booster:
        return
    # Then
    assert_or_update_k_output(
        foundry_root / 'out/kompiled/foundry.k',
        TEST_DATA_DIR / 'foundry.k.expected',
        update=update_expected_output,
    )
    assert_or_update_k_output(
        foundry_root / 'out/kompiled/contracts.k',
        TEST_DATA_DIR / 'contracts.k.expected',
        update=update_expected_output,
    )


def assert_or_update_k_output(k_file: Path, expected_file: Path, *, update: bool) -> None:
    assert k_file.is_file()
    assert expected_file.is_file()

    k_text = k_file.read_text()
    filtered_lines = (line for line in k_text.splitlines() if not line.startswith('    rule  ( #binRuntime ('))

    actual_text = '\n'.join(filtered_lines) + '\n'
    expected_text = expected_file.read_text()

    if update:
        expected_file.write_text(actual_text)
    else:
        assert actual_text == expected_text


ALL_PROVE_TESTS: Final = tuple((TEST_DATA_DIR / 'foundry-prove-all').read_text().splitlines())
SKIPPED_PROVE_TESTS: Final = set((TEST_DATA_DIR / 'foundry-prove-skip').read_text().splitlines())

SHOW_TESTS = set((TEST_DATA_DIR / 'foundry-show').read_text().splitlines())


@pytest.mark.parametrize('test_id', ALL_PROVE_TESTS)
def test_foundry_prove(test_id: str, foundry_root: Path, update_expected_output: bool, use_booster: bool) -> None:
    if test_id in SKIPPED_PROVE_TESTS:
        pytest.skip()

    # When
    prove_res = foundry_prove(
        foundry_root,
        tests=[test_id],
        simplify_init=False,
        smt_timeout=125,
        smt_retry_limit=4,
        use_booster=use_booster,
    )

    # Then
    assert_pass(test_id, prove_res)

    if test_id not in SHOW_TESTS or use_booster:
        return

    # And when
    show_res = foundry_show(
        foundry_root,
        test=test_id,
        to_module=True,
        sort_collections=True,
        omit_unstable_output=True,
        pending=True,
        failing=True,
        failure_info=True,
    )

    # Then
    assert_or_update_show_output(show_res, TEST_DATA_DIR / f'show/{test_id}.expected', update=update_expected_output)


FAIL_TESTS: Final = tuple((TEST_DATA_DIR / 'foundry-fail').read_text().splitlines())


@pytest.mark.parametrize('test_id', FAIL_TESTS)
def test_foundry_fail(test_id: str, foundry_root: Path, update_expected_output: bool, use_booster: bool) -> None:
    # When
    prove_res = foundry_prove(
        foundry_root,
        tests=[test_id],
        simplify_init=False,
        smt_timeout=125,
        smt_retry_limit=4,
        use_booster=use_booster,
    )

    # Then
    assert_fail(test_id, prove_res)

    if test_id not in SHOW_TESTS or use_booster:
        return

    # And when
    show_res = foundry_show(
        foundry_root,
        test=test_id,
        to_module=True,
        sort_collections=True,
        omit_unstable_output=True,
        pending=True,
        failing=True,
        failure_info=True,
    )

    # Then
    assert_or_update_show_output(show_res, TEST_DATA_DIR / f'show/{test_id}.expected', update=update_expected_output)


ALL_BMC_TESTS: Final = tuple((TEST_DATA_DIR / 'foundry-bmc-all').read_text().splitlines())
SKIPPED_BMC_TESTS: Final = set((TEST_DATA_DIR / 'foundry-bmc-skip').read_text().splitlines())


@pytest.mark.parametrize('test_id', ALL_BMC_TESTS)
def test_foundry_bmc(test_id: str, foundry_root: Path, use_booster: bool) -> None:
    if test_id in SKIPPED_BMC_TESTS:
        pytest.skip()

    # When
    prove_res = foundry_prove(
        foundry_root,
        tests=[test_id],
        bmc_depth=3,
        simplify_init=False,
        smt_timeout=125,
        smt_retry_limit=4,
        use_booster=use_booster,
    )

    # Then
    assert_pass(test_id, prove_res)


def assert_pass(test_id: str, prove_res: dict[str, tuple[bool, list[str] | None]]) -> None:
    assert test_id in prove_res
    passed, log = prove_res[test_id]
    if not passed:
        assert log
        pytest.fail('\n'.join(log))


def assert_fail(test_id: str, prove_res: dict[str, tuple[bool, list[str] | None]]) -> None:
    assert test_id in prove_res
    passed, log = prove_res[test_id]
    assert not passed
    assert log


def assert_or_update_show_output(show_res: str, expected_file: Path, *, update: bool) -> None:
    assert expected_file.is_file()

    filtered_lines = (
        line
        for line in show_res.splitlines()
        if not line.startswith(
            (
                '    src: ',
                '│   src: ',
                '┃  │   src: ',
                '   │   src: ',
            )
        )
    )
    actual_text = '\n'.join(filtered_lines) + '\n'
    expected_text = expected_file.read_text()

    if update:
        expected_file.write_text(actual_text)
    else:
        assert actual_text == expected_text
