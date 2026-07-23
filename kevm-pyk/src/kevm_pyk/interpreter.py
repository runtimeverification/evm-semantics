from __future__ import annotations

from typing import TYPE_CHECKING

from pyk.kdist import kdist
from pyk.ktool.krun import llvm_interpret

from .config import DEFAULT_SCHEDULE
from .gst_to_kore import ScheduleTriple, filter_gst_keys, gst_to_kore, resolve_network

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
) -> Iterator[tuple[str, App]]:
    """Yield (test_name, kore_pattern) for each test in GST data after filtering discarded keys."""
    for test_name, test in gst_data.items():
        if test_name in skipped_keys:
            continue
        triple = _resolve_schedule(test, schedule)
        gst_filtered = {test_name: filter_gst_keys(test)}
        yield test_name, gst_to_kore(
            gst_filtered, triple.schedule, mode, chainid, usegas, triple.next_schedule, triple.fork_time
        )


def _resolve_schedule(test: dict, fallback: str | None) -> ScheduleTriple:
    """Resolve the schedule triple from the test's network field, falling back to the provided schedule.

    Blockchain tests on a transition network switch schedules at the fork timestamp; state tests
    have no block loop, so a transition network collapses to the single schedule selected by the
    test environment's timestamp.
    """
    network = test.get('network')
    if network is None:
        schedule = fallback or DEFAULT_SCHEDULE
        return ScheduleTriple(schedule, schedule, 0)
    triple = resolve_network(network)
    if triple.fork_time and 'blocks' not in test:
        env_ts = test['env']['currentTimestamp']
        ts = int(env_ts, 16) if isinstance(env_ts, str) else int(env_ts)
        schedule = triple.next_schedule if ts >= triple.fork_time else triple.schedule
        return ScheduleTriple(schedule, schedule, 0)
    return triple


def interpret(init_kore: Any, *, check: bool = True) -> Pattern:
    """Interpret the given GST data using the LLVM backend."""
    return llvm_interpret(kdist.get('evm-semantics.llvm'), init_kore, check=check)
