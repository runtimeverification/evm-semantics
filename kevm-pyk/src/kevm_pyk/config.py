from __future__ import annotations

import os
from pathlib import Path
from subprocess import CalledProcessError
from typing import TYPE_CHECKING

from pyk.cli.utils import check_dir_path
from pyk.utils import run_process

import kevm_pyk

if TYPE_CHECKING:
    from typing import Final


def _kevm_lib() -> Path:
    kevm_lib: Path

    env = os.getenv('KEVM_LIB')
    if env is not None:
        kevm_lib = Path(env).resolve()
        check_dir_path(kevm_lib)
        return kevm_lib
    else:
        try:
            which_kevm = run_process(('which', 'kevm'), pipe_stderr=True).stdout.strip()
        except CalledProcessError:
            raise RuntimeError(
                "Couldn't locate KEVM libraries. Either set the KEVM_LIB environment variable, or put kevm on PATH."
            ) from None

        kevm_path = Path(which_kevm).resolve()
        kevm_lib = kevm_path.parents[1] / 'lib/kevm'

    check_dir_path(kevm_lib)
    return kevm_lib


MODULE_DIR: Final = Path(kevm_pyk.__file__).parent
KPROJ_DIR: Final = MODULE_DIR / 'kproj'
EVM_SEMANTICS_DIR: Final = KPROJ_DIR / 'evm-semantics'
PLUGIN_DIR: Final = KPROJ_DIR / 'plugin'


INCLUDE_DIRS: Final = (EVM_SEMANTICS_DIR, PLUGIN_DIR)


NIX_LIBS: Final = os.getenv('NIX_LIBS')
KEVM_LIB: Final = _kevm_lib()


LLVM_DIR: Final = KEVM_LIB / 'llvm'
HASKELL_DIR: Final = KEVM_LIB / 'haskell'
HASKELL_STANDALONE_DIR: Final = KEVM_LIB / 'haskell-standalone'
FOUNDRY_DIR: Final = KEVM_LIB / 'foundry'
