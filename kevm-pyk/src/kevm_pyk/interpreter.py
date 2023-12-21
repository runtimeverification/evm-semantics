from __future__ import annotations

from typing import TYPE_CHECKING

from pyk.kdist import kdist
from pyk.kllvm import importer
from pyk.kore.parser import KoreParser
from pyk.utils import run_process

from .gst_to_kore import gst_to_kore

if TYPE_CHECKING:
    from subprocess import CompletedProcess
    from typing import Any, Final

    from pyk.kore.syntax import Pattern


importer.import_kllvm(kdist.get('evm-semantics.kllvm'))
from pyk.kllvm.convert import llvm_to_pattern, pattern_to_llvm

runtime: Final = importer.import_runtime(kdist.get('evm-semantics.kllvm-runtime'))


def interpret(gst_data: Any, schedule: str, mode: str, chainid: int, usegas: bool, *, check: bool = True) -> Pattern:
    proc_res = _interpret(gst_data, schedule, mode, chainid, usegas)

    if check:
        proc_res.check_returncode()

    kore = KoreParser(proc_res.stdout).pattern()
    return kore


def _interpret(gst_data: Any, schedule: str, mode: str, chainid: int, usegas: bool) -> CompletedProcess:
    interpreter = kdist.get('evm-semantics.llvm') / 'interpreter'
    init_kore = gst_to_kore(gst_data, schedule, mode, chainid, usegas)
    proc_res = run_process([str(interpreter), '/dev/stdin', '-1', '/dev/stdout'], input=init_kore.text, check=False)
    return proc_res


def kllvm_interpret(gst_data: Any, schedule: str, mode: str, chainid: int, usegas: bool) -> Pattern:
    init_kore = gst_to_kore(gst_data, schedule, mode, chainid, usegas)
    init_llvm = pattern_to_llvm(init_kore).desugar_associative()
    final_llvm = runtime.run(init_llvm)
    final_kore = llvm_to_pattern(final_llvm)
    return final_kore
