from __future__ import annotations

import json
from typing import TYPE_CHECKING

from ..utils import REPO_ROOT

if TYPE_CHECKING:
    from pyk.testing import Profiler


GST_FILE = REPO_ROOT / 'tests/ethereum-tests/BlockchainTests/GeneralStateTests/stEIP1559/intrinsic.json'


def test_gst_to_kore(profile: Profiler) -> None:
    with GST_FILE.open() as f:
        gst_data = json.load(f)

    with profile(sort_keys=('cumtime', 'tottime'), limit=30):
        from kevm_pyk.gst_to_kore import gst_to_kore

        gst_to_kore(gst_data, 'DEFAULT', 'VMTESTS', 1)
