from __future__ import annotations

from distutils.dir_util import copy_tree
from typing import TYPE_CHECKING

import pytest
from pyk.utils import run_process

from kevm_pyk import config
from kevm_pyk.foundry import foundry_kompile, foundry_prove

from .utils import TEST_DATA_DIR

if TYPE_CHECKING:
    from pathlib import Path
    from typing import Final

    from pytest import TempPathFactory


FORGE_STD_REF: Final = '27e14b7'

ALL_TESTS: Final = tuple((TEST_DATA_DIR / 'foundry-prove-all').read_text().splitlines())
SKIPPED_TESTS: Final = set((TEST_DATA_DIR / 'foundry-prove-skip').read_text().splitlines())


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
    )
    return foundry_root


@pytest.mark.parametrize('test_id', ALL_TESTS)
def test_foundry_prove(test_id: str, foundry_root: Path) -> None:
    if test_id in SKIPPED_TESTS:
        pytest.skip()

    # When
    res = foundry_prove(
        foundry_root,
        tests=[test_id],
        simplify_init=False,
        smt_timeout=125,
        smt_retry_limit=4,
    )

    # Then
    assert res == {test_id: (True, None)}
