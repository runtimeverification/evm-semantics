from __future__ import annotations

import json
from pathlib import Path
from typing import TYPE_CHECKING

if TYPE_CHECKING:
    from pyk.testing import Profiler


REPO_ROOT = Path(__file__).parents[4]
GST_FILE = REPO_ROOT / 'tests/ethereum-tests/BlockchainTests/GeneralStateTests/stEIP1559/intrinsic.json'


def test_gst_to_kore(profile: Profiler) -> None:
    with GST_FILE.open() as f:
        gst_data = json.load(f)

    with profile(sort_keys=('cumtime', 'tottime'), limit=30):
        from kevm_pyk.gst_to_kore import gst_to_kore

        gst_to_kore(gst_data, 'DEFAULT', 'VMTESTS', 1)
