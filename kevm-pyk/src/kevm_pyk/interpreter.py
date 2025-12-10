from __future__ import annotations

from typing import TYPE_CHECKING, Final

from pyk.kdist import kdist
from pyk.ktool.krun import llvm_interpret

from .gst_to_kore import SCHEDULE_MAPPING, filter_gst_keys, gst_to_kore

if TYPE_CHECKING:
    from collections.abc import Iterator
    from typing import Any

    from pyk.kore.syntax import App, Pattern


DEFAULT_SCHEDULE: Final[str] = 'PRAGUE'


def iterate_gst(
    gst_data: dict,
    mode: str,
    chainid: int,
    usegas: bool,
    skipped_keys: frozenset[str] = frozenset(),
    schedule: str | None = None,
) -> Iterator[tuple[str, App]]:
    """Yield (test_name, kore_pattern) for each test in GST data after filtering discarded keys."""
    for test_name, test in gst_data.items():
        if test_name in skipped_keys:
            continue
        test_schedule = _resolve_schedule(test, test_name, schedule)
        gst_filtered = {test_name: filter_gst_keys(test)}
        yield test_name, gst_to_kore(gst_filtered, test_schedule, mode, chainid, usegas)


def _resolve_schedule(test: dict, test_name: str, fallback: str | None) -> str:
    """Return schedule from test's network field, falling back to provided schedule or DEFAULT_SCHEDULE."""
    network = test.get('network')
    if network is not None:
        if network not in SCHEDULE_MAPPING:
            raise ValueError(f'Unknown network {network!r} in test {test_name!r}')
        return SCHEDULE_MAPPING[network]
    return fallback or DEFAULT_SCHEDULE


def interpret(init_kore: Any, *, check: bool = True) -> Pattern:
    """Interpret the given GST data using the LLVM backend."""
    return llvm_interpret(kdist.get('evm-semantics.llvm'), init_kore, check=check)
