from __future__ import annotations

import os
from typing import TYPE_CHECKING

if TYPE_CHECKING:
    from typing import Final


NIX_BUILD: Final = bool(os.getenv('NIX_BUILD'))
