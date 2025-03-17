from __future__ import annotations

from subprocess import CalledProcessError
from typing import TYPE_CHECKING

from pyk.kdist import kdist
from pyk.kore.parser import KoreParser
from pyk.ktool.krun import llvm_interpret_raw
from pyk.utils import run_process_2

from .gst_to_kore import filter_gst_keys, gst_to_kore

if TYPE_CHECKING:
    from subprocess import CompletedProcess
    from typing import Any

    from pyk.kore.syntax import Pattern


def interpret(gst_data: Any, schedule: str, mode: str, chainid: int, usegas: bool, *, check: bool = True) -> Pattern:
    try:
        res = _interpret(gst_data, schedule, mode, chainid, usegas, check)
    except CalledProcessError as err:
        raise RuntimeError(f'Interpreter failed with status {err.returncode}: {err.stderr}') from err

    if res.stdout == '':
        raise RuntimeError(f'Interpreter returned empty stdout: {res.stderr}')

    return KoreParser(res.stdout).pattern()


def _interpret(gst_data: Any, schedule: str, mode: str, chainid: int, usegas: bool, check: bool) -> CompletedProcess:
    gst_data_filtered = filter_gst_keys(gst_data)
    init_kore = gst_to_kore(gst_data_filtered, schedule, mode, chainid, usegas)
    return llvm_interpret_raw(kdist.get('evm-semantics.llvm-summary'), init_kore.text, check=check)
