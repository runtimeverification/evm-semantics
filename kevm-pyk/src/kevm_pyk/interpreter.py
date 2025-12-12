from __future__ import annotations

from typing import TYPE_CHECKING

from pyk.kdist import kdist
from pyk.ktool.krun import llvm_interpret

from .config import DEFAULT_SCHEDULE
from .gst_to_kore import SCHEDULE_MAPPING, filter_gst_keys, gst_to_kore

if TYPE_CHECKING:
    from collections.abc import Iterator
    from typing import Any

    from pyk.kore.syntax import App, Pattern


def iterate_gst(
    gst_data: dict,
    mode: str,
    chainid: int,
    usegas: bool,
    skipped_keys: frozenset[str] = frozenset(),
    schedule: str | None = None,
) -> Iterator[tuple[str, App, tuple[bool, bool]]]:
    """Yield (test_name, kore_pattern, metadata) for each test in GST data."""
    for test_name, test in gst_data.items():
        if test_name in skipped_keys:
            continue
        exception_metadata = _resolve_exception(test)
        test_schedule = _resolve_schedule(test, schedule)
        gst_filtered = {test_name: filter_gst_keys(test)}
        yield test_name, gst_to_kore(gst_filtered, test_schedule, mode, chainid, usegas), exception_metadata


def _resolve_exception(test: dict) -> tuple[bool, bool]:
    """Parse the 'blocks' field of a GST test and check if 'expectException' and 'hasBigInt' fields are present."""
    exception_expected = False
    has_big_int = False
    for block in test.get('blocks', []):
        exception_expected = exception_expected or 'expectException' in block
        has_big_int = has_big_int or 'hasBigInt' in block
        if exception_expected and has_big_int:
            break
    return (exception_expected, has_big_int)


def _resolve_schedule(test: dict, fallback: str | None) -> str:
    """Return schedule from test's network field, falling back to provided schedule or DEFAULT_SCHEDULE."""
    network = test.get('network')
    if network is not None:
        if network not in SCHEDULE_MAPPING:
            raise ValueError(f'Unknown network {network}.')
        return SCHEDULE_MAPPING[network]
    return fallback or DEFAULT_SCHEDULE


def interpret(init_kore: Any, *, check: bool = True) -> Pattern:
    """Interpret the given GST data using the LLVM backend."""
    return llvm_interpret(kdist.get('evm-semantics.llvm'), init_kore, check=check)
