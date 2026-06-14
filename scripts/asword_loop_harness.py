#!/usr/bin/env python3
"""Loop-regression harness for functional simplification specs.

Motivation
----------
Some simplification lemmas (e.g. `asWord-eq-false`, evm-semantics #2859) are not
loop-safe: on certain term shapes they recurse forever in the Kore simplifier, so
a single `simplify`/`execute` RPC request never returns. A non-terminating request
cannot be caught by the usual per-request Haskell-backend log bundle (that file is
only written when the request *completes*), so the robust signal is wall-clock: run
each claim under a hard timeout and classify by how the prover exits.

This harness runs every claim of a spec in isolation against a pre-kompiled
definition, bounds each with a timeout, reaps any leftover Kore server, and reports
a per-claim outcome:

    LOOP    prover killed at the timeout       -> the simplification did not terminate
    PASS    prover exited 0                     -> claim proved (term simplified as expected)
    FAILED  prover exited non-zero, under bound -> claim did not prove but did terminate
                                                   (e.g. left "stuck": loop fixed but the
                                                   expected RHS is no longer derivable)

The three-way split is the point: a fix that stops the loop can land a claim in
either PASS (still proves the expected result) or FAILED (terminates but can no
longer prove it), and those demand different follow-ups. See the header comment of
`tests/specs/functional/asword-eq-false-loop-spec.k` for the worked example.

The definition is an *input* (kompile separately, never timed here): the lemma under
test is part of the kompiled definition, so each lemma variant -- buggy, guarded,
[smt-lemma], dropped -- is its own `--definition` dir, and comparing variants is just
re-running this harness against each.

Usage
-----
    uv --project kevm-pyk/ run python scripts/asword_loop_harness.py \
        --spec tests/specs/functional/asword-eq-false-loop-spec.k \
        --definition /tmp/asword-exp/buggy-kompiled \
        --timeout 120 \
        --out /tmp/asword-loop-report.md

`--claims a,b` restricts to specific labels; default is every `claim [label]:` in
the spec. `--spec-module` defaults to the file stem upper-cased (the kevm
convention), matching how the file's module is named.
"""

from __future__ import annotations

import argparse
import json
import os
import re
import signal
import subprocess
import sys
import time
from dataclasses import asdict, dataclass
from pathlib import Path

REPO_ROOT = Path(__file__).resolve().parent.parent
INCLUDES = (
    REPO_ROOT / 'kevm-pyk/src/kevm_pyk/kproj/evm-semantics',
    REPO_ROOT / 'kevm-pyk/src/kevm_pyk/kproj/plugin',
    # So a loop spec under functional/loops/ keeps the standard `requires "verification.k"`
    # (resolved here via -I) and needs no edit when it later moves up into functional/.
    REPO_ROOT / 'tests/specs/functional',
)

# kevm prove server selection; the harness injects the matching flags.
SERVER_FLAGS = {
    'booster': (),  # kore-rpc-booster (fallback on) -- the default, the CSE config
    'kore': ('--no-use-booster',),  # pure kore-rpc -- loops directly, no booster layer
    'booster-dev': ('--use-booster-dev',),  # booster only, no kore fallback
}

# Kore/booster server process names to reap after each claim (matched with pgrep -x,
# never pkill -f, so we never match this script's own command line).
SERVER_PROCS = ('kore-rpc-booster', 'booster-dev', 'kore-rpc')


@dataclass
class ClaimResult:
    claim: str
    outcome: str  # LOOP | PASS | FAILED
    exit_code: int
    seconds: float
    log: str


def parse_claim_labels(spec: Path) -> list[str]:
    """Every `claim [label]:` in source order."""
    labels = re.findall(r'claim\s*\[([A-Za-z0-9._-]+)\]', spec.read_text())
    if not labels:
        raise SystemExit(f'No `claim [label]:` found in {spec}')
    return labels


def reap_servers() -> None:
    for name in SERVER_PROCS:
        # pgrep -x: exact process-name match only; avoids killing the harness/shell.
        pids = subprocess.run(['pgrep', '-x', name], capture_output=True, text=True).stdout.split()
        for pid in pids:
            subprocess.run(['kill', '-9', pid], stderr=subprocess.DEVNULL)


def run_claim(
    spec: Path,
    definition: Path,
    spec_module: str,
    claim: str,
    timeout_s: int,
    server_mode: str,
    eq_max_local_steps: int | None,
    workdir: Path,
) -> ClaimResult:
    save_dir = workdir / f'save-{claim}'
    log_path = workdir / f'run-{claim}.log'
    cmd = [
        'uv', '--project', str(REPO_ROOT / 'kevm-pyk'), 'run', 'kevm', 'prove',
        str(spec),
        '--definition', str(definition),
        '--spec-module', spec_module,
        '--claim', f'{spec_module}.{claim}',
        '--save-directory', str(save_dir), '--reinit',
        *SERVER_FLAGS[server_mode],
        '--verbose',
    ]  # fmt: skip
    for inc in INCLUDES:
        cmd += ['-I', str(inc)]
    if eq_max_local_steps is not None:
        cmd += ['--equation-max-local-steps', str(eq_max_local_steps)]

    # Bound the run in-process: start the child in its own session (process group) so a
    # timeout can SIGKILL the *whole tree* -- uv, kevm, and the Kore server it spawned --
    # in one shot. Relying on the `timeout` coreutil leaves grandchild Kore servers behind
    # (the loop is server-side) and its exit code is awkward to read back through Python.
    start = time.monotonic()
    timed_out = False
    with log_path.open('w') as fh:
        proc = subprocess.Popen(cmd, stdout=fh, stderr=subprocess.STDOUT, start_new_session=True)
        try:
            proc.communicate(timeout=timeout_s)
        except subprocess.TimeoutExpired:
            timed_out = True
            os.killpg(os.getpgid(proc.pid), signal.SIGKILL)
            proc.wait()
    elapsed = time.monotonic() - start
    reap_servers()  # belt-and-suspenders for any server that escaped the process group

    if timed_out:
        outcome = 'LOOP'
    elif proc.returncode == 0:
        outcome = 'PASS'
    else:
        outcome = 'FAILED'
    return ClaimResult(claim, outcome, proc.returncode, round(elapsed, 1), str(log_path))


def render_table(results: list[ClaimResult], header: dict[str, str]) -> str:
    lines = [f'# asWord loop harness -- {header["spec_module"]}', '']
    for k, v in header.items():
        lines.append(f'- {k}: {v}')
    lines.append('')
    rows = [('claim', 'outcome', 'exit', 'seconds')]
    rows += [(r.claim, r.outcome, str(r.exit_code), f'{r.seconds:.1f}') for r in results]
    widths = [max(len(row[i]) for row in rows) for i in range(len(rows[0]))]
    for n, row in enumerate(rows):
        lines.append('| ' + ' | '.join(c.ljust(widths[i]) for i, c in enumerate(row)) + ' |')
        if n == 0:
            lines.append('|' + '|'.join('-' * (widths[i] + 2) for i in range(len(row))) + '|')
    return '\n'.join(lines) + '\n'


def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument('--spec', type=Path, required=True, help='Functional spec .k file.')
    ap.add_argument('--definition', type=Path, required=True, help='Pre-kompiled definition dir.')
    ap.add_argument('--spec-module', help='Spec module name (default: file stem upper-cased).')
    ap.add_argument('--claims', help='Comma-separated claim labels (default: all in spec).')
    ap.add_argument('--timeout', type=int, default=120, help='Per-claim wall-clock bound, seconds (default 120).')
    ap.add_argument('--server-mode', choices=tuple(SERVER_FLAGS), default='booster')
    ap.add_argument('--equation-max-local-steps', type=int, default=None, help='Booster local-step budget.')
    ap.add_argument('--workdir', type=Path, default=Path('/tmp/asword-exp/runs'), help='Where save dirs and logs land.')
    ap.add_argument('--out', type=Path, help='Write the markdown report here (and a .json sidecar).')
    args = ap.parse_args()

    spec_module = args.spec_module or args.spec.stem.upper()
    claims = args.claims.split(',') if args.claims else parse_claim_labels(args.spec)
    args.workdir.mkdir(parents=True, exist_ok=True)

    header = {
        'spec': str(args.spec),
        'spec_module': spec_module,
        'definition': str(args.definition),
        'server_mode': args.server_mode,
        'equation_max_local_steps': str(args.equation_max_local_steps),
        'timeout_s': str(args.timeout),
    }
    print(
        f'Running {len(claims)} claim(s) against {args.definition} [{args.server_mode}, timeout {args.timeout}s]',
        file=sys.stderr,
    )

    results: list[ClaimResult] = []
    for claim in claims:
        print(f'  {claim} ...', end='', flush=True, file=sys.stderr)
        r = run_claim(
            args.spec,
            args.definition,
            spec_module,
            claim,
            args.timeout,
            args.server_mode,
            args.equation_max_local_steps,
            args.workdir,
        )
        print(f' {r.outcome} ({r.seconds:.0f}s, exit {r.exit_code})', file=sys.stderr)
        results.append(r)

    report = render_table(results, header)
    print('\n' + report)
    if args.out:
        args.out.parent.mkdir(parents=True, exist_ok=True)
        args.out.write_text(report)
        args.out.with_suffix('.json').write_text(
            json.dumps({'header': header, 'results': [asdict(r) for r in results]}, indent=2) + '\n'
        )
        print(f'Wrote {args.out} and {args.out.with_suffix(".json")}', file=sys.stderr)

    # Exit non-zero if any claim looped, so the harness is CI-usable.
    return 1 if any(r.outcome == 'LOOP' for r in results) else 0


if __name__ == '__main__':
    raise SystemExit(main())
