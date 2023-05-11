from __future__ import annotations

from typing import TYPE_CHECKING

from pyk.cli_utils import run_process
from pyk.kore.parser import KoreParser

from . import config
from .gst_to_kore import gst_to_kore

if TYPE_CHECKING:
    from typing import Any

    from pyk.kore.syntax import Pattern


def interpret(gst_data: Any, schedule: str, mode: str, chainid: int) -> Pattern:
    interpreter = config.LLVM_DIR / 'interpreter'

    init_kore = gst_to_kore(gst_data, schedule, mode, chainid)
    proc_res = run_process([str(interpreter), '/dev/stdin', '-1', '/dev/stdout'], input=init_kore.text)
    final_kore = KoreParser(proc_res.stdout).pattern()

    return final_kore
