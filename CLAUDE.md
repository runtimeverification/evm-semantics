# evm-semantics

K-based formal semantics of the EVM, plus the `kevm-pyk` Python toolchain that drives compilation, execution, and proof.

## Repository layout

```
kevm-pyk/src/kevm_pyk/kproj/evm-semantics/   K source (*.md, *.k) — the semantics
kevm-pyk/src/kevm_pyk/                        Python toolchain (kevm_pyk package)
kevm-pyk/src/tests/                           Python test suite
tests/specs/                                  K proof specs, organised by suite
```

## Build toolchain

All Python commands run through `uv` from the repo root or inside `kevm-pyk/`:

```bash
# from repo root:
uv --project kevm-pyk/ run <command>

# equivalent, from inside kevm-pyk/:
uv run <command>
```

Build the Python package (creates wheel/sdist, installs into the local venv):

```bash
make -C kevm-pyk/ build
# equivalent:
uv --project kevm-pyk/ build
```

Before running any proof, the K definitions must be compiled into kdist targets.
These are cached under `~/.cache/kdist-<hash>/`; the hash changes whenever any `.k`/`.md`
file in `kproj/` changes, so a rebuild is required after every semantics edit.

```bash
# via the kevm-kdist CLI (recommended):
uv --project kevm-pyk/ run kevm-kdist build evm-semantics.plugin
uv --project kevm-pyk/ run kevm-kdist build evm-semantics.haskell

# parallel build of all targets:
uv --project kevm-pyk/ run kevm-kdist build --jobs 8
```

## Linting and static analysis (Python)

```bash
make -C kevm-pyk/ check          # all checks: flake8, mypy, autoflake, isort, black
make -C kevm-pyk/ format         # auto-fix:   autoflake, isort, black

# individual tools via uv:
uv --project kevm-pyk/ run flake8 src
uv --project kevm-pyk/ run mypy   src
uv --project kevm-pyk/ run black  --check src
uv --project kevm-pyk/ run isort  --check src
```

**Every commit must pass `make -C kevm-pyk/ check` and `make -C kevm-pyk/ test-unit`.**

## Unit tests (fast, no K runtime required)

```bash
make -C kevm-pyk/ test-unit
# equivalent:
uv --project kevm-pyk/ run pytest src/tests/unit --numprocesses=8 --dist=worksteal
```

These test pure Python logic (AST helpers, KEVM class methods, etc.) and finish in seconds.

## Integration / proof tests

### Make targets (recommended)

```bash
make -C kevm-pyk/ test-integration PYTEST_ARGS+="-k <filter>"
```

The Makefile defaults to `--numprocesses=8 --dist=worksteal --maxfail=1`.
Override parallelism or failure tolerance:

```bash
make -C kevm-pyk/ test-integration PYTEST_PARALLEL=4 PYTEST_ARGS+="-k test_prove_functional"
make -C kevm-pyk/ test-integration PYTEST_MAXFAIL=10 PYTEST_ARGS+="-k test_prove_functional"
```

### Direct pytest (same options, more control)

```bash
uv --project kevm-pyk/ run pytest src/tests/integration \
    --numprocesses=8 --dist=worksteal \
    -k "test_prove_functional"

# run a single named spec:
uv --project kevm-pyk/ run pytest src/tests/integration \
    --numprocesses=1 \
    -k "test_prove_functional and compute-valid-jump-dests"
```

### Proof test suites

| Make target (from repo root) | pytest `-k` filter | Spec directory | Notes |
|---|---|---|---|
| `make test-prove-functional` | `test_prove_functional` | `tests/specs/functional/` | Pure-function/lemma proofs; fast per spec |
| `make test-prove-rules` | `test_prove_rules` | `tests/specs/{benchmarks,erc20,examples,mcd,mcd-structured,kontrol}/` | Full EVM contract proofs |
| `make test-prove-optimizations` | `test_prove_optimizations` | `tests/specs/opcodes/` | EVM opcode optimisation proofs |
| `make test-prove-dss` | `test_prove_dss` | `tests/specs/mcd/vat*.k` | DSS/MakerDAO VAT proofs (very slow, CI only) |
| `make test-conformance` | `test_conformance` | — | Ethereum execution-spec conformance |

Top-level convenience targets delegate to `make -C kevm-pyk/ test-integration PYTEST_ARGS+=...`.

### Running the prover directly (for timing / debugging a single spec)

Useful when you want wall-time measurements or verbose RPC logs without pytest overhead.
The definition must be kompiled first (≈40 s), then reused across runs:

```bash
uv --project kevm-pyk/ run kevm kompile-spec \
    tests/specs/functional/my-spec.k \
    --main-module VERIFICATION --syntax-module VERIFICATION \
    --output-definition /tmp/my-spec-kompiled \
    --backend haskell \
    -I kevm-pyk/src/kevm_pyk/kproj/evm-semantics \
    -I kevm-pyk/src/kevm_pyk/kproj/plugin

time uv --project kevm-pyk/ run kevm prove \
    tests/specs/functional/my-spec.k \
    --definition /tmp/my-spec-kompiled \
    --spec-module MY-SPEC \
    --use-booster \
    --save-directory /tmp/my-spec-save \
    -I kevm-pyk/src/kevm_pyk/kproj/evm-semantics \
    -I kevm-pyk/src/kevm_pyk/kproj/plugin \
    --verbose
```

`--verbose` shows per-RPC-call timing (simplify / execute / implies).
`--save-directory` persists the proof KCFG; omit `--reinit` on reruns to resume.
Running `kevm prove` this way drops a `<spec-name>.json` claim-parse cache next to the spec — do not commit it.

## Proof timing anatomy

With `--verbose`, the key RPC phases are:

| Phase | What it does | Where time is spent |
|---|---|---|
| `kprove --dry-run` | Parse spec to kore | ≈22 s cold, ≈0.3 s if JSON cache is fresh |
| `KoreServer` startup | Load `definition.kore` + LLVM lib | ≈7 s |
| `simplify` #1 | Definedness constraint `#Ceil(initial_config)` | **Evaluates K functions symbolically — often the bottleneck** |
| `simplify` #3 | Simplify initial/target nodes | **Same; also evaluates K function terms in the config** |
| `execute` | Reachability proof step | Runs the symbolic execution |
| `implies` | Subsumption check | Checks final state ⊆ target spec |

`kevm` reports `Proof timing: Xs` which starts from `add-module` (excludes server startup and claim parsing).
For benchmarking a definition change, compare individual `simplify` and `execute` durations, not just total wall time — the simplify calls are often where K function definitions dominate.

## Functional simplification tests

`tests/specs/functional/` contains `runLemma`/`doneLemma` style specs that test pure K functions and simplification lemmas in isolation, using the Haskell prover but without the overhead of full EVM execution.

**When to add one:** Any time a simplification you expect to fire is not going through in a larger proof, add a functional spec that targets exactly that simplification.
A small focused claim will tell you immediately whether the rule fires under the right conditions, whether the preconditions are too strong, and whether the definition is efficient enough.
Functional specs are also the right place for performance regression tests — a claim with a partially symbolic input (e.g. `#buf(32, INT_VAR)`) forces Haskell symbolic evaluation and exposes O(N) overhead in recursive definitions that concrete execution would hide.

Existing specs to use as models:
- `lemmas-no-smt-spec.k` — imports `evm.md`; tests arithmetic and bytes lemmas; no SMT needed
- `lemmas-spec.k` — imports `edsl.md` + lemmas; tests `#hashedLocation`, ranges, etc.
- `compute-valid-jump-dests-spec.k` — performance benchmark with symbolic input tail

To register a new spec, add one line to `KOMPILE_MAIN_FILE` in
`kevm-pyk/src/tests/integration/test_prove.py`:

```python
'functional/my-spec.k': 'my-spec.k',
```

The glob `spec_files('functional', '*-spec.k')` picks it up automatically.
`KOMPILE_MAIN_MODULE` defaults to `'VERIFICATION'`; only override it if your spec uses a different top module name.

## Comparing haskell-backend builds (perf + booster-dev pass rate)

Use this to measure how a haskell-backend change (a branch/commit) affects both proof **performance** and the **booster-dev pass rate** — how many specs prove under the pure `booster-dev` binary (no kore-rpc fallback) — while holding the K version fixed at `deps/k_release`.
The driving question is usually "does this backend make more specs pass purely in booster-dev, and at what speed cost?".

Install a backend with `kup` (see [`docs/kup-override.md`](docs/kup-override.md) for the override mechanics).
The stock build is `kup install k.openssl.procps --version v<deps/k_release>`; an override build replaces just the backend, e.g. `--override haskell-backend github:runtimeverification/haskell-backend/<commit>` (or a local checkout / isolated `git worktree` if a github ref is rejected).

**The procedure, per backend:**

1. **Install** the backend, then `uv --project kevm-pyk/ sync` (only needed when the K version changes; an override leaves pyk untouched).
2. **Kompile separately and do not time it** — kompile time is never part of the comparison. Pre-kompile the suite into a per-backend dir so the two builds' definitions stay isolated:
   ```bash
   uv --project kevm-pyk/ run pytest kevm-pyk/src/tests/integration -k "test_kompile_targets" \
       --kompiled-targets-dir /tmp/hb-exp/<tag>-kompiled --numprocesses 4
   ```
3. **Normal-mode run** (kore-rpc-booster, fallback on) — the real proof-timing baseline. Wrap with `$SECONDS` to capture total wall-clock; `--junitxml` captures per-test time and outcome:
   ```bash
   start=$SECONDS
   uv --project kevm-pyk/ run pytest kevm-pyk/src/tests/integration \
       -k "test_prove_functional or test_prove_rules or test_prove_optimizations or test_prove_dss" \
       --kompiled-targets-dir /tmp/hb-exp/<tag>-kompiled --numprocesses 8 \
       --junitxml=perf-runs/<tag>/normal.junit.xml > perf-runs/<tag>/normal.log 2>&1
   echo $((SECONDS-start)) > perf-runs/<tag>/normal.wallclock
   ```
   `--numprocesses 8` is safe — multiple K servers do not contend here. Use no `--maxfail` (you want the complete map).
4. **Derive the booster-dev timeout** from the normal run, so a booster-dev spec is only ever counted as failing on a real abort, never for being slow:
   ```bash
   T=$(uv --project kevm-pyk/ run python scripts/compare-junit-runs.py max-time perf-runs/<tag>/normal.junit.xml)
   ```
   `T` = ceil of the longest normal-mode per-test time for that backend.
5. **booster-dev run** with `--use-booster-dev --timeout "$T"`. To *discover* newly-passing specs, the `tests/failing-symbolic.haskell-booster-dev` skip-list (which the harness `pytest.skip()`s under `--use-booster-dev`) must be neutralised. Do **not** empty the file — `exclude_list()` asserts it is non-empty, so an empty file crashes collection; instead write a single sentinel path that matches no real spec, then git-restore afterward:
   ```bash
   cp tests/failing-symbolic.haskell-booster-dev /tmp/hb-exp/failing-list.bak
   echo '__none__' > tests/failing-symbolic.haskell-booster-dev
   start=$SECONDS
   uv --project kevm-pyk/ run pytest kevm-pyk/src/tests/integration \
       -k "test_prove_functional or test_prove_rules or test_prove_optimizations or test_prove_dss" \
       --use-booster-dev --timeout "$T" --timeout-method=thread \
       --kompiled-targets-dir /tmp/hb-exp/<tag>-kompiled --numprocesses 8 \
       --junitxml=perf-runs/<tag>/boosterdev.junit.xml > perf-runs/<tag>/boosterdev.log 2>&1
   echo $((SECONDS-start)) > perf-runs/<tag>/boosterdev.wallclock
   git checkout -- tests/failing-symbolic.haskell-booster-dev
   ```

**Compare** the two backends' run directories (`perf-runs/baseline`, `perf-runs/escalate`):

```bash
uv --project kevm-pyk/ run python scripts/compare-junit-runs.py compare \
    --baseline-dir perf-runs/baseline --escalate-dir perf-runs/escalate \
    -o docs/experiment-logs/<timestamp>-<name>.md
```

`scripts/compare-junit-runs.py` (committed tooling) emits an aligned-markdown report plus a `.json` sidecar: a totals table (sum-of-per-test **and** wall-clock per mode/backend), the booster-dev pass-rate diff (newly-passing fail→pass and any pass→fail regressions), and per-test timing deltas for specs passing in both runs.
Raw JUnit/logs live under `perf-runs/` (gitignored); commit only the generated report under `docs/experiment-logs/`.

## Commit discipline

- Every commit must be **atomic and self-contained** — the project must build and fast tests must pass at each commit.
- Fast gate before every commit: `make -C kevm-pyk/ check` and `make -C kevm-pyk/ test-unit`.
- After editing any `.k`/`.md` file, kdist targets are stale; rebuild with `kevm-kdist build` before running proofs.
- Proof tests (`test_prove_*`) take minutes per spec; run the relevant suite before marking a PR ready, not on every commit.
