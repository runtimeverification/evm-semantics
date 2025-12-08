from __future__ import annotations

from typing import TYPE_CHECKING

from pyk.kdist import kdist
from pyk.ktool.krun import llvm_interpret

from .gst_to_kore import filter_gst_keys, gst_to_kore

if TYPE_CHECKING:
    from collections.abc import Iterator
    from typing import Any

    from pyk.kore.syntax import App, Pattern


def iterate_gst(
    gst_data: dict, schedule: str, mode: str, chainid: int, usegas: bool, skipped_keys: frozenset[str] = frozenset()
) -> Iterator[tuple[str, App]]:
    """Yield (test_name, kore_pattern) for each test in GST data after filtering discarded keys."""
    for test_name, test in gst_data.items():
        if test_name in skipped_keys:
            continue
        gst_filtered = {test_name: filter_gst_keys(test)}
    yield test_name, gst_to_kore(gst_filtered, schedule, mode, chainid, usegas)


def interpret(init_kore: Any, *, check: bool = True) -> Pattern:
    """Interpret the given GST data using the LLVM backend."""
    return llvm_interpret(kdist.get('evm-semantics.llvm'), init_kore, check=check)
