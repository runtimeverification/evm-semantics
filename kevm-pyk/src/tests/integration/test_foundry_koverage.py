from __future__ import annotations

from distutils.dir_util import copy_tree

from pyk.utils import run_process

from kevm_pyk import config
from kevm_pyk.foundry import foundry_kompile, foundry_koverage, foundry_prove, foundry_show

from .test_foundry_prove import FORGE_STD_REF, assert_pass

import pytest
from os import listdir
from os.path import isfile
from pathlib import Path
from typing import TYPE_CHECKING

from .utils import TEST_DATA_DIR

if TYPE_CHECKING:
    from pathlib import Path
    from typing import Final

    from pytest import TempPathFactory


KOVERAGE_TESTS: Final = set([f.removesuffix('.expected') for f in listdir(TEST_DATA_DIR / 'koverage') if f.endswith('.expected')])


@pytest.fixture(scope='module')  # TODO should reduce scope
def foundry_root(tmp_path_factory: TempPathFactory) -> Path:
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
    )

    return foundry_root

@pytest.mark.parametrize('test_id', KOVERAGE_TESTS)
def test_foundry_koverage(test_id: str, foundry_root: Path, update_expected_output: bool) -> None:
    # When
    prove_res = foundry_prove(
        foundry_root,
        tests=[test_id],
        simplify_init=False,
        smt_timeout=125,
        smt_retry_limit=4,
    )

    # Then
    assert_pass(test_id, prove_res)

    # And when
    koverage_res = foundry_koverage(foundry_root, tests=[test_id])

    first_out = str(next(iter(koverage_res)))

    assert_or_update_koverage_output(first_out, TEST_DATA_DIR / f'koverage/{test_id}.expected', update=update_expected_output)

def assert_or_update_koverage_output(koverage_res: str, expected_file: Path, *, update: bool) -> None:
    assert expected_file.is_file()

    if update:
        expected_file.write_text(koverage_res)
    else:
        expected_text = expected_file.read_text()
        assert expected_text == koverage_res
