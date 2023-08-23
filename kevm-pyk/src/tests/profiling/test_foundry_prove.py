from __future__ import annotations

import sys
from distutils.dir_util import copy_tree
from typing import TYPE_CHECKING

from pyk.utils import run_process

from kontrol.foundry import foundry_kompile, foundry_prove

from .utils import TEST_DATA_DIR

if TYPE_CHECKING:
    from pathlib import Path
    from typing import Final

    from pyk.testing import Profiler


sys.setrecursionlimit(10**7)


FORGE_STD_REF: Final = '27e14b7'


def test_foundy_prove(profile: Profiler, use_booster: bool, tmp_path: Path) -> None:
    foundry_root = tmp_path / 'foundry'

    _forge_build(foundry_root)

    with profile('kompile.prof', sort_keys=('cumtime', 'tottime'), limit=15):
        foundry_kompile(
            foundry_root=foundry_root,
            includes=(),
            llvm_library=use_booster,
        )

    with profile('prove.prof', sort_keys=('cumtime', 'tottime'), limit=100):
        foundry_prove(
            foundry_root,
            tests=[('AssertTest.test_revert_branch', None)],
            simplify_init=False,
            smt_timeout=300,
            smt_retry_limit=10,
            counterexample_info=True,
            use_booster=use_booster,
        )


def _forge_build(target_dir: Path) -> None:
    copy_tree(str(TEST_DATA_DIR / 'foundry'), str(target_dir))
    run_process(['forge', 'install', '--no-git', f'foundry-rs/forge-std@{FORGE_STD_REF}'], cwd=target_dir)
    run_process(['forge', 'build'], cwd=target_dir)
