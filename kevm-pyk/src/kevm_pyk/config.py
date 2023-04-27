from __future__ import annotations

import os
from pathlib import Path
from typing import TYPE_CHECKING

from pyk.cli_utils import check_dir_path

if TYPE_CHECKING:
    from typing import Final


def _env_or_raise(var: str) -> str:
    env = os.getenv(var)
    if env is None:
        raise ValueError(f'Environment variable not set: {var}')
    return env


NIX_BUILD: Final = bool(os.getenv('NIX_BUILD'))

KEVM_LIB: Final = Path(_env_or_raise('KEVM_LIB')).resolve()
check_dir_path(KEVM_LIB)

INCLUDE_DIR: Final = KEVM_LIB / 'include/kframework'
check_dir_path(INCLUDE_DIR)

LLVM_DIR: Final = KEVM_LIB / 'llvm'
HASKELL_DIR: Final = KEVM_LIB / 'haskell'
NODE_DIR: Final = KEVM_LIB / 'node'
FOUNDRY_DIR: Final = KEVM_LIB / 'foundry'
