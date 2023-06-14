from __future__ import annotations

from typing import TYPE_CHECKING

from pyk.kore.parser import KoreParser
from pyk.utils import run_process

from . import config
from .gst_to_kore import gst_to_kore

if TYPE_CHECKING:
    from subprocess import CompletedProcess
    from typing import Any

    from pyk.kore.syntax import Pattern


def interpret(gst_data: Any, schedule: str, mode: str, chainid: int, *, check: bool = True) -> Pattern:
    proc_res = _interpret(gst_data, schedule, mode, chainid)

    if check:
        proc_res.check_returncode()

    kore = KoreParser(proc_res.stdout).pattern()
    return kore


def _interpret(gst_data: Any, schedule: str, mode: str, chainid: int) -> CompletedProcess:
    interpreter = config.LLVM_DIR / 'interpreter'
    init_kore = gst_to_kore(gst_data, schedule, mode, chainid)
    proc_res = run_process([str(interpreter), '/dev/stdin', '-1', '/dev/stdout'], input=init_kore.text, check=False)
    return proc_res
