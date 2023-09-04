from __future__ import annotations

from distutils.dir_util import copy_tree
from typing import TYPE_CHECKING

import pytest
from filelock import FileLock
from pyk.kore.rpc import kore_server
from pyk.proof import APRProof
from pyk.utils import run_process, single

from kontrol.foundry import (
    Foundry,
    foundry_kompile,
    foundry_merge_nodes,
    foundry_prove,
    foundry_remove_node,
    foundry_show,
    foundry_step_node,
)

from .utils import TEST_DATA_DIR

if TYPE_CHECKING:
    from collections.abc import Iterator
    from pathlib import Path
    from typing import Final

    from pyk.kore.rpc import KoreServer
    from pytest import TempPathFactory


FORGE_STD_REF: Final = '75f1746'


@pytest.fixture(scope='module')
def server(foundry_root: Path, use_booster: bool) -> Iterator[KoreServer]:
    foundry = Foundry(foundry_root)
    llvm_definition_dir = foundry.out / 'kompiled' / 'llvm-library' if use_booster else None
    kore_rpc_command = ('kore-rpc-booster',) if use_booster else ('kore-rpc',)

    yield kore_server(
        definition_dir=foundry.kevm.definition_dir,
        llvm_definition_dir=llvm_definition_dir,
        module_name=foundry.kevm.main_module,
        command=kore_rpc_command,
        smt_timeout=300,
        smt_retry_limit=10,
    )


@pytest.fixture(scope='session')
def foundry_root(tmp_path_factory: TempPathFactory, worker_id: str, use_booster: bool) -> Path:
    if worker_id == 'master':
        root_tmp_dir = tmp_path_factory.getbasetemp()
    else:
        root_tmp_dir = tmp_path_factory.getbasetemp().parent

    foundry_root = root_tmp_dir / 'foundry'
    with FileLock(str(foundry_root) + '.lock'):
        if not foundry_root.is_dir():
            copy_tree(str(TEST_DATA_DIR / 'foundry'), str(foundry_root))

            run_process(['forge', 'install', '--no-git', f'foundry-rs/forge-std@{FORGE_STD_REF}'], cwd=foundry_root)
            run_process(['forge', 'build'], cwd=foundry_root)

            foundry_kompile(
                foundry_root=foundry_root,
                includes=(),
                requires=[str(TEST_DATA_DIR / 'lemmas.k')],
                imports=['LoopsTest:SUM-TO-N-INVARIANT'],
            )

    session_foundry_root = tmp_path_factory.mktemp('foundry')
    copy_tree(str(foundry_root), str(session_foundry_root))
    return session_foundry_root


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
def test_foundry_prove(
    test_id: str, foundry_root: Path, update_expected_output: bool, use_booster: bool, server: KoreServer
) -> None:
    if test_id in SKIPPED_PROVE_TESTS or (update_expected_output and not test_id in SHOW_TESTS):
        pytest.skip()

    # When
    prove_res = foundry_prove(
        foundry_root, tests=[(test_id, None)], simplify_init=False, counterexample_info=True, port=server.port
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
        counterexample_info=True,
        port=server.port,
    )

    # Then
    assert_or_update_show_output(show_res, TEST_DATA_DIR / f'show/{test_id}.expected', update=update_expected_output)


FAIL_TESTS: Final = tuple((TEST_DATA_DIR / 'foundry-fail').read_text().splitlines())


@pytest.mark.parametrize('test_id', FAIL_TESTS)
def test_foundry_fail(
    test_id: str, foundry_root: Path, update_expected_output: bool, use_booster: bool, server: KoreServer
) -> None:
    # When
    prove_res = foundry_prove(
        foundry_root,
        tests=[(test_id, None)],
        simplify_init=False,
        counterexample_info=True,
        port=server.port,
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
        counterexample_info=True,
        port=server.port,
    )

    # Then
    assert_or_update_show_output(show_res, TEST_DATA_DIR / f'show/{test_id}.expected', update=update_expected_output)


ALL_BMC_TESTS: Final = tuple((TEST_DATA_DIR / 'foundry-bmc-all').read_text().splitlines())
SKIPPED_BMC_TESTS: Final = set((TEST_DATA_DIR / 'foundry-bmc-skip').read_text().splitlines())


@pytest.mark.parametrize('test_id', ALL_BMC_TESTS)
def test_foundry_bmc(test_id: str, foundry_root: Path, use_booster: bool, server: KoreServer) -> None:
    if test_id in SKIPPED_BMC_TESTS:
        pytest.skip()

    # When
    prove_res = foundry_prove(
        foundry_root,
        tests=[(test_id, None)],
        bmc_depth=3,
        simplify_init=False,
        port=server.port,
    )

    # Then
    assert_pass(test_id, prove_res)


def test_foundry_merge_nodes(foundry_root: Path, use_booster: bool, server: KoreServer) -> None:
    test = 'AssertTest.test_branch_merge(uint256)'

    foundry_prove(
        foundry_root,
        tests=[(test, None)],
        max_iterations=4,
        port=server.port,
    )
    check_pending(foundry_root, test, [6, 7])

    foundry_step_node(foundry_root, test, node=6, depth=49, port=server.port)
    foundry_step_node(foundry_root, test, node=7, depth=50, port=server.port)

    check_pending(foundry_root, test, [8, 9])

    foundry_merge_nodes(foundry_root=foundry_root, test=test, node_ids=[8, 9], include_disjunct=True)

    check_pending(foundry_root, test, [10])

    prove_res = foundry_prove(
        foundry_root,
        tests=[(test, None)],
        port=server.port,
    )
    assert_pass(test, prove_res)


def check_pending(foundry_root: Path, test: str, pending: list[int]) -> None:
    foundry = Foundry(foundry_root)
    proofs = foundry.proofs_with_test(test)
    apr_proofs: list[APRProof] = [proof for proof in proofs if type(proof) is APRProof]
    proof = single(apr_proofs)
    assert [node.id for node in proof.pending] == pending


def test_foundry_auto_abstraction(
    foundry_root: Path, update_expected_output: bool, server: KoreServer, use_booster: bool
) -> None:
    test_id = 'GasTest.testInfiniteGas()'
    foundry_prove(
        foundry_root,
        tests=[(test_id, None)],
        auto_abstract_gas=True,
        port=server.port,
        simplify_init=False,
    )

    if use_booster:
        return

    show_res = foundry_show(
        foundry_root,
        test=test_id,
        to_module=True,
        minimize=False,
        sort_collections=True,
        omit_unstable_output=True,
        pending=True,
        failing=True,
        failure_info=True,
        port=server.port,
    )

    assert_or_update_show_output(show_res, TEST_DATA_DIR / 'gas-abstraction.expected', update=update_expected_output)


def test_foundry_remove_node(foundry_root: Path, update_expected_output: bool, server: KoreServer) -> None:
    test = 'AssertTest.test_assert_true()'

    foundry = Foundry(foundry_root)

    prove_res = foundry_prove(
        foundry_root,
        tests=[(test, None)],
        port=server.port,
    )
    assert_pass(test, prove_res)

    foundry_remove_node(
        foundry_root=foundry_root,
        test=test,
        node=4,
    )

    proof = single(foundry.proofs_with_test(test))
    assert type(proof) is APRProof
    assert proof.pending

    prove_res = foundry_prove(
        foundry_root,
        tests=[(test, None)],
        port=server.port,
    )
    assert_pass(test, prove_res)


def assert_pass(test: str, prove_res: dict[tuple[str, str | None], tuple[bool, list[str] | None]]) -> None:
    id = id_for_test(test, prove_res)
    passed, log = prove_res[(test, id)]
    if not passed:
        assert log
        pytest.fail('\n'.join(log))


def assert_fail(test: str, prove_res: dict[tuple[str, str | None], tuple[bool, list[str] | None]]) -> None:
    id = id_for_test(test, prove_res)
    passed, log = prove_res[test, id]
    assert not passed
    assert log


def id_for_test(test: str, prove_res: dict[tuple[str, str | None], tuple[bool, list[str] | None]]) -> str:
    return single(_id for _test, _id in prove_res.keys() if _test == test and _id is not None)


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
                'module',
            )
        )
    )
    actual_text = '\n'.join(filtered_lines) + '\n'
    expected_text = expected_file.read_text()

    if update:
        expected_file.write_text(actual_text)
    else:
        assert actual_text == expected_text


def test_foundry_resume_proof(foundry_root: Path, update_expected_output: bool, server: KoreServer) -> None:
    foundry = Foundry(foundry_root)
    test = 'AssumeTest.test_assume_false(uint256,uint256)'

    prove_res = foundry_prove(
        foundry_root,
        tests=[(test, None)],
        auto_abstract_gas=True,
        max_iterations=4,
        reinit=True,
        port=server.port,
    )
    id = id_for_test(test, prove_res)

    proof = foundry.get_apr_proof(f'{test}:{id}')
    assert proof.pending

    prove_res = foundry_prove(
        foundry_root,
        tests=[(test, id)],
        auto_abstract_gas=True,
        max_iterations=6,
        reinit=False,
        port=server.port,
    )
    assert_fail(test, prove_res)
