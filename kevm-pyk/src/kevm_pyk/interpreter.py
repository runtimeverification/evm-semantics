from __future__ import annotations

from typing import TYPE_CHECKING

from pyk.kdist import kdist
from pyk.kore.parser import KoreParser
from pyk.utils import run_process_2

from .gst_to_kore import filter_gst_keys, gst_to_kore

if TYPE_CHECKING:
    from subprocess import CompletedProcess
    from typing import Any

    from pyk.kore.syntax import Pattern


def interpret(gst_data: Any, schedule: str, mode: str, chainid: int, usegas: bool, *, check: bool = True) -> Pattern:
    proc_res = _interpret(gst_data, schedule, mode, chainid, usegas)

    if check:
        proc_res.check_returncode()

    if len(proc_res.stderr) > 0:
        raise Exception(proc_res.stderr)

    kore = KoreParser(proc_res.stdout).pattern()
    return kore


def _interpret(gst_data: Any, schedule: str, mode: str, chainid: int, usegas: bool) -> CompletedProcess:
    gst_data_filtered = filter_gst_keys(gst_data)
    interpreter = kdist.get('evm-semantics.llvm') / 'interpreter'
    init_kore = gst_to_kore(gst_data_filtered, schedule, mode, chainid, usegas)
    proc_res = run_process_2([str(interpreter), '/dev/stdin', '-1', '/dev/stdout'], input=init_kore.text, check=False)
    return proc_res
