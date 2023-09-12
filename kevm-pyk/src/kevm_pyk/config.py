from __future__ import annotations

import os
from pathlib import Path
from typing import TYPE_CHECKING

import kevm_pyk

if TYPE_CHECKING:
    from typing import Final


MODULE_DIR: Final = Path(kevm_pyk.__file__).parent
KPROJ_DIR: Final = MODULE_DIR / 'kproj'
EVM_SEMANTICS_DIR: Final = KPROJ_DIR / 'evm-semantics'
PLUGIN_DIR: Final = KPROJ_DIR / 'plugin'


INCLUDE_DIRS: Final = (EVM_SEMANTICS_DIR, PLUGIN_DIR)


NIX_LIBS: Final = os.getenv('NIX_LIBS')
