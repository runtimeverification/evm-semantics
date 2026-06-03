#!/usr/bin/env python3
"""Compare two proof-suite runs (e.g. two haskell-backend builds) from JUnit XML.

Two subcommands:

  max-time <junit.xml>
      Print, to stdout, the ceiling (in whole seconds) of the longest per-test
      ``time`` in a JUnit report.  Used to set the booster-dev ``--timeout`` to
      "however long the longest-running normal booster test takes" -- so a
      booster-dev spec is only ever counted as failing on a real abort, never
      for merely being slow.

  compare --baseline-dir D --escalate-dir D -o report.md
      Read ``normal.junit.xml`` / ``boosterdev.junit.xml`` (and the matching
      ``*.wallclock`` files) from each run directory and emit an aligned-markdown
      comparison plus a ``.json`` sidecar.  Reports per-test timing deltas, total
      wall-clock and sum-of-per-test for each mode, and the booster-dev
      pass-rate diff (newly-passing and regressed specs).

Kompile time is never part of these inputs by construction -- kompilation is a
separate, untimed step that does not write a JUnit report.

Pure standard library; run via ``uv --project kevm-pyk/ run python``.
"""

from __future__ import annotations

import argparse
import json
import math
import sys
from dataclasses import dataclass
from pathlib import Path
from typing import TYPE_CHECKING
from xml.etree.ElementTree import parse

if TYPE_CHECKING:
    from xml.etree.ElementTree import Element

# Outcome precedence for a single testcase.  A testcase passes iff it has no
# failure/error/skipped child element.

PASS = 'pass'
FAIL = 'fail'
ERROR = 'error'
SKIPPED = 'skipped'
TIMEOUT = 'timeout'


@dataclass
class Case:
    """One parametrised proof test: its spec key, wall ``time`` and outcome."""

    key: str
    time: float
    outcome: str


@dataclass
class RunData:
    """A single backend's two timed runs, loaded from its ``perf-runs/<tag>`` dir."""

    normal: dict[str, Case]
    boosterdev: dict[str, Case]
    normal_wall: float | None
    boosterdev_wall: float | None

    @staticmethod
    def load(run_dir: Path) -> RunData:
        return RunData(
            normal=parse_junit(run_dir / 'normal.junit.xml'),
            boosterdev=parse_junit(run_dir / 'boosterdev.junit.xml'),
            normal_wall=read_wallclock(run_dir / 'normal.wallclock'),
            boosterdev_wall=read_wallclock(run_dir / 'boosterdev.wallclock'),
        )

    def cases(self, mode: str) -> dict[str, Case]:
        return self.normal if mode == 'normal' else self.boosterdev

    def wall(self, mode: str) -> float | None:
        return self.normal_wall if mode == 'normal' else self.boosterdev_wall


def _spec_key(classname: str, name: str) -> str:
    """Derive a stable per-spec key that matches across runs.

    pytest names proof tests like ``test_prove_rules[mcd/vat-spec.k]``; the spec
    identity is the bracketed parameter.  Fall back to ``classname::name`` for
    any non-parametrised case so nothing is silently dropped.
    """
    lb, rb = name.find('['), name.rfind(']')
    if lb != -1 and rb != -1 and rb > lb:
        return name[lb + 1 : rb]
    return f'{classname}::{name}'


def _classify(case_el: Element) -> str:
    """Map a ``<testcase>`` element to one of the outcome constants.

    pytest-timeout surfaces a timeout as a ``<failure>``/``<error>`` whose
    message mentions "timeout"; we split that out so a killed-for-slowness spec
    is not conflated with a genuine proof failure.
    """
    for tag, outcome in (('skipped', SKIPPED), ('error', ERROR), ('failure', FAIL)):
        el = case_el.find(tag)
        if el is not None:
            blob = ' '.join(filter(None, (el.get('message', ''), el.text or ''))).lower()
            if 'timeout' in blob or 'timed out' in blob:
                return TIMEOUT
            return outcome
    return PASS


def parse_junit(path: Path) -> dict[str, Case]:
    """Parse a JUnit XML file into ``{spec_key: Case}``.

    Returns an empty mapping (rather than raising) for a missing file so the
    comparison degrades gracefully when a run did not complete.
    """
    if not path.is_file():
        return {}
    root = parse(path).getroot()
    cases: dict[str, Case] = {}
    for case_el in root.iter('testcase'):
        key = _spec_key(case_el.get('classname', ''), case_el.get('name', ''))
        time = float(case_el.get('time', '0') or '0')
        cases[key] = Case(key=key, time=time, outcome=_classify(case_el))
    return cases


def read_wallclock(path: Path) -> float | None:
    """Read a ``*.wallclock`` file (integer seconds written by the run wrapper)."""
    if not path.is_file():
        return None
    text = path.read_text().strip()
    try:
        return float(text)
    except ValueError:
        return None


# --------------------------------------------------------------------------- #
# max-time
# --------------------------------------------------------------------------- #


def cmd_max_time(args: argparse.Namespace) -> int:
    cases = parse_junit(Path(args.junit))
    if not cases:
        print('no testcases found', file=sys.stderr)
        return 1
    longest = max(cases.values(), key=lambda c: c.time)
    print(int(math.ceil(longest.time)))
    print(f'longest: {longest.key} = {longest.time:.1f}s', file=sys.stderr)
    return 0


# --------------------------------------------------------------------------- #
# compare
# --------------------------------------------------------------------------- #


def _md_table(headers: list[str], rows: list[list[str]]) -> str:
    """Render an aligned (column-padded) GitHub-markdown table."""
    widths = [len(h) for h in headers]
    for row in rows:
        for i, cell in enumerate(row):
            widths[i] = max(widths[i], len(cell))

    def fmt(cells: list[str]) -> str:
        return '| ' + ' | '.join(c.ljust(widths[i]) for i, c in enumerate(cells)) + ' |'

    sep = '| ' + ' | '.join('-' * widths[i] for i in range(len(headers))) + ' |'
    return '\n'.join([fmt(headers), sep, *(fmt(r) for r in rows)])


def _delta(base: float, esc: float) -> tuple[str, str]:
    """Format an absolute and percentage delta (escalate relative to baseline)."""
    d = esc - base
    pct = (d / base * 100.0) if base > 0 else float('nan')
    pct_s = f'{pct:+.1f}%' if base > 0 else 'n/a'
    return f'{d:+.1f}', pct_s


def _timing_section(title: str, base: dict[str, Case], esc: dict[str, Case]) -> tuple[str, list[dict]]:
    """Per-test timing table for specs that PASS in both runs (like-for-like)."""
    keys = sorted(k for k in base.keys() & esc.keys() if base[k].outcome == PASS and esc[k].outcome == PASS)
    rows, records = [], []
    base_sum = esc_sum = 0.0
    for k in keys:
        b, e = base[k].time, esc[k].time
        base_sum += b
        esc_sum += e
        dabs, dpct = _delta(b, e)
        rows.append([k, f'{b:.1f}', f'{e:.1f}', dabs, dpct])
        records.append({'spec': k, 'baseline_s': b, 'escalate_s': e, 'delta_s': e - b})
    if not rows:
        return f'### {title}\n\n_No specs passed in both runs._\n', records
    sd_abs, sd_pct = _delta(base_sum, esc_sum)
    rows.append(['**sum-of-per-test**', f'{base_sum:.1f}', f'{esc_sum:.1f}', sd_abs, sd_pct])
    table = _md_table(['spec', 'baseline (s)', 'escalate (s)', 'Δ (s)', 'Δ %'], rows)
    return f'### {title}\n\n{table}\n', records


def cmd_compare(args: argparse.Namespace) -> int:
    runs = {
        'baseline': RunData.load(Path(args.baseline_dir)),
        'escalate': RunData.load(Path(args.escalate_dir)),
    }

    out: list[str] = ['# haskell-backend comparison: baseline (stock) vs escalate (escalate-partial-match)\n']

    # ---- Totals overview (wall-clock + sum-of-per-test) ------------------- #
    overview_rows = []
    for mode in ('normal', 'boosterdev'):
        for tag in ('baseline', 'escalate'):
            cases = runs[tag].cases(mode)
            sum_pt = sum(c.time for c in cases.values())
            wall = runs[tag].wall(mode)
            wall_s = f'{wall:.0f}' if wall is not None else 'n/a'
            n_pass = sum(1 for c in cases.values() if c.outcome == PASS)
            overview_rows.append([mode, tag, str(len(cases)), str(n_pass), f'{sum_pt:.1f}', wall_s])
    out.append('## Totals\n')
    out.append(
        _md_table(
            ['mode', 'backend', '# tests', '# pass', 'sum-of-per-test (s)', 'wall-clock (s)'],
            overview_rows,
        )
    )
    out.append('')

    # ---- booster-dev pass-rate diff --------------------------------------- #
    bd_b, bd_e = runs['baseline'].boosterdev, runs['escalate'].boosterdev
    keys = sorted(bd_b.keys() | bd_e.keys())
    newly_pass, regressed, diff_rows, bd_records = [], [], [], []
    for k in keys:
        ob = bd_b[k].outcome if k in bd_b else 'absent'
        oe = bd_e[k].outcome if k in bd_e else 'absent'
        bd_records.append({'spec': k, 'baseline': ob, 'escalate': oe})
        if ob != PASS and oe == PASS:
            newly_pass.append(k)
        if ob == PASS and oe != PASS:
            regressed.append(k)
        if ob != oe:
            diff_rows.append([k, ob, oe])
    out.append('## booster-dev pass rate (pure booster, no kore fallback)\n')
    out.append(f'- Specs run: baseline {len(bd_b)}, escalate {len(bd_e)}')
    out.append(
        f'- Passing: baseline {sum(1 for c in bd_b.values() if c.outcome == PASS)}, '
        f'escalate {sum(1 for c in bd_e.values() if c.outcome == PASS)}'
    )
    out.append(f'- **Newly passing (fail/timeout → pass): {len(newly_pass)}**')
    out.append(f'- **Regressed (pass → fail/timeout): {len(regressed)}**\n')
    if diff_rows:
        out.append('### Specs whose booster-dev outcome changed\n')
        out.append(_md_table(['spec', 'baseline', 'escalate'], diff_rows))
        out.append('')
    else:
        out.append('_No booster-dev outcome changed between backends._\n')

    # ---- Timing sections -------------------------------------------------- #
    out.append('## Timing (per-test, like-for-like)\n')
    sec_n, rec_n = _timing_section('Normal mode (kore-rpc-booster)', runs['baseline'].normal, runs['escalate'].normal)
    sec_d, rec_d = _timing_section('booster-dev mode', runs['baseline'].boosterdev, runs['escalate'].boosterdev)
    out.append(sec_n)
    out.append(sec_d)

    report = '\n'.join(out) + '\n'
    out_path = Path(args.output)
    out_path.parent.mkdir(parents=True, exist_ok=True)
    out_path.write_text(report)

    sidecar = out_path.with_suffix(out_path.suffix + '.json')
    sidecar.write_text(
        json.dumps(
            {
                'totals': overview_rows,
                'boosterdev_pass_diff': {
                    'newly_passing': newly_pass,
                    'regressed': regressed,
                    'per_spec': bd_records,
                },
                'normal_timing': rec_n,
                'boosterdev_timing': rec_d,
                'wallclock': {
                    tag: {m: runs[tag].wall(m) for m in ('normal', 'boosterdev')} for tag in ('baseline', 'escalate')
                },
            },
            indent=2,
        )
    )

    print(f'wrote {out_path}')
    print(f'wrote {sidecar}')
    print(f'newly-passing under booster-dev: {len(newly_pass)}; regressed: {len(regressed)}')
    return 0


def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    sub = ap.add_subparsers(dest='cmd', required=True)

    mt = sub.add_parser('max-time', help='print ceil(longest per-test time) in seconds')
    mt.add_argument('junit', help='path to a JUnit XML file')
    mt.set_defaults(func=cmd_max_time)

    cmp_ = sub.add_parser('compare', help='compare baseline vs escalate run directories')
    cmp_.add_argument('--baseline-dir', required=True)
    cmp_.add_argument('--escalate-dir', required=True)
    cmp_.add_argument('-o', '--output', required=True, help='markdown report path (.json sidecar alongside)')
    cmp_.set_defaults(func=cmd_compare)

    args = ap.parse_args()
    return args.func(args)


if __name__ == '__main__':
    raise SystemExit(main())
