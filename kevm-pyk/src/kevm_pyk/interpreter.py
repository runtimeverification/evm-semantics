from __future__ import annotations

from typing import TYPE_CHECKING

from pyk.kdist import kdist
from pyk.ktool.krun import llvm_interpret

from .gst_to_kore import filter_gst_keys, gst_to_kore

if TYPE_CHECKING:
    from collections.abc import Iterator
    from typing import Any

    from pyk.kore.syntax import Pattern


def iterate_gst(gst_data: Any, skipped_keys: frozenset[str] = frozenset()) -> Iterator[tuple[str, dict]]:
    for test_name, test in gst_data.items():
        if test_name in skipped_keys:
            continue
        yield test_name, filter_gst_keys(test)


def interpret(gst_data: Any, schedule: str, mode: str, chainid: int, usegas: bool, *, check: bool = True) -> Pattern:
    """Interpret the given GST data using the LLVM backend."""
    init_kore = gst_to_kore(filter_gst_keys(gst_data), schedule, mode, chainid, usegas)
    return llvm_interpret(kdist.get('evm-semantics.llvm'), init_kore, check=check)
