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

All Python commands run through `uv` from inside `kevm-pyk/`:

```bash
uv --project kevm-pyk/ run <command>
# or, from inside kevm-pyk/:
uv run <command>
```

Before running proofs the K definitions must be compiled (kdist targets):

```bash
uv --project kevm-pyk/ run python3 -m pyk.kdist build evm-semantics.plugin
uv --project kevm-pyk/ run python3 -m pyk.kdist build evm-semantics.haskell
```

These are cached under `~/.cache/kdist-<hash>/`.
The hash changes when the K source files change, so rebuilding is required after editing `evm.md` or any other `.k`/`.md` file in `kproj/`.

## Linting and static analysis (Python)

All checks live in `kevm-pyk/`:

```bash
make -C kevm-pyk/ check          # run all checks (flake8, mypy, autoflake, isort, black)
make -C kevm-pyk/ format         # auto-format (autoflake, isort, black)
```

Individual tools:
```bash
uv --project kevm-pyk/ run flake8 src
uv --project kevm-pyk/ run mypy   src
uv --project kevm-pyk/ run black  --check src
uv --project kevm-pyk/ run isort  --check src
```

**Every commit must pass `make -C kevm-pyk/ check` and `make -C kevm-pyk/ test-unit`.**

## Unit tests (fast, no K runtime required)

```bash
make -C kevm-pyk/ test-unit
# or directly:
uv --project kevm-pyk/ run pytest src/tests/unit
```

These test pure Python logic (AST helpers, KEVM class methods, etc.) and finish in seconds.

## Integration / proof tests

All proof tests use `pytest` via `make -C kevm-pyk/ test-integration PYTEST_ARGS+="-k <filter>"` or directly with `uv --project kevm-pyk/ run pytest src/tests/integration`.

| Make target | pytest `-k` filter | What it covers |
|---|---|---|
| `make test-prove-functional` | `test_prove_functional` | Pure-function lemmas & simplification benchmarks (`tests/specs/functional/`) |
| `make test-prove-rules` | `test_prove_rules` | Full EVM opcode / contract specs (`tests/specs/{benchmarks,erc20,examples,mcd,mcd-structured,kontrol}/`) |
| `make test-prove-optimizations` | `test_prove_optimizations` | EVM opcode optimisation proofs (`tests/specs/opcodes/`) |
| `make test-prove-dss` | `test_prove_dss` | DSS/MakerDAO VAT proofs (very slow, run in CI only) |
| `make test-conformance` | `test_conformance` | Ethereum execution-spec conformance tests |

To run a single spec file by name:

```bash
make -C kevm-pyk/ test-integration PYTEST_ARGS+="-k test_prove_functional and compute-valid-jump-dests"
```

To run the prover directly (useful for timing/debugging a single spec):

```bash
# 1. Kompile the spec once (≈40 s):
uv --project kevm-pyk/ run kevm kompile-spec \
    tests/specs/functional/my-spec.k \
    --main-module VERIFICATION --syntax-module VERIFICATION \
    --output-definition /tmp/my-spec-kompiled \
    --backend haskell \
    -I kevm-pyk/src/kevm_pyk/kproj/evm-semantics \
    -I kevm-pyk/src/kevm_pyk/kproj/plugin

# 2. Run the proof (reuses the compiled definition):
time uv --project kevm-pyk/ run kevm prove \
    tests/specs/functional/my-spec.k \
    --definition /tmp/my-spec-kompiled \
    --spec-module MY-SPEC \
    --use-booster \
    --save-directory /tmp/my-spec-save \
    -I kevm-pyk/src/kevm_pyk/kproj/evm-semantics \
    -I kevm-pyk/src/kevm_pyk/kproj/plugin
```

Add `--verbose` to see per-RPC-call timing (simplify / execute / implies phases).
The `--save-directory` path persists the proof KCFG; rerun without `--reinit` to resume.

Running `kevm prove` directly generates a `<spec-name>.json` file next to the spec.
That file is a claim-parse cache; **do not commit it** (add to `.gitignore` if it keeps appearing).

## Proof timing anatomy

When `--verbose` is used, the key phases visible in the log are:

| Log message | Phase | Notes |
|---|---|---|
| `claim_loader - Generating claim modules` + `kprove --dry-run` | Spec parsing | ≈22 s cold, ≈0.3 s cached (JSON hit) |
| `Starting KoreServer` … `KoreServer started` | Booster startup | ≈7 s, loads `definition.kore` |
| `simplify` request #1 | Definedness constraint | Evaluates `#Ceil(initial_config)` |
| `simplify` requests #3/4 | Node simplification | Evaluates function terms in the initial/target config — **this is where K function definitions (e.g. `#computeValidJumpDests`) are symbolically reduced** |
| `execute` request | Proof step | Actual reachability search |
| `implies` request | Subsumption check | Checks final state ⊆ target |

kevm reports `Proof timing: Xs` which covers only from `add-module` onward (not server startup or claim parsing).

## How to add a functional simplification test

Functional tests live in `tests/specs/functional/`.
They test pure K functions — lemmas, simplification rules, helper functions — using the Haskell prover but without setting up the full EVM execution context.

### Step 1 — Write the spec file

Each spec is a self-contained K file.
Model it on `tests/specs/functional/lemmas-no-smt-spec.k` (imports `evm.md`) or on `lemmas-spec.k` (imports `edsl.md` + lemmas).

```k
requires "evm.md"
requires "lemmas/lemmas.k"

module VERIFICATION
    imports EVM
    imports LEMMAS

    syntax StepSort ::= Bytes | Int | Bool
 // --------------------------------------

    syntax KItem ::= runLemma ( StepSort ) [symbol(runLemma)]
                   | doneLemma( StepSort )
 // --------------------------------------
    rule <k> runLemma( T ) => doneLemma( T ) ... </k>

endmodule

module MY-SIMPLIFICATION-SPEC
    imports VERIFICATION

    // Concrete claim: prove a specific simplification holds.
    claim [my-lemma]:
        <k> runLemma( myFunction(concreteArg1, concreteArg2) )
         => doneLemma( expectedResult )
        ... </k>

    // Symbolic claim: prove it holds for all values satisfying a constraint.
    claim [my-lemma-symbolic]:
        <k> runLemma( myFunction(X, #buf(32, INT_VAR)) )
         => doneLemma( ?_:Bytes )      // ?_ = existential wildcard
        ... </k>
      requires #rangeUInt(256, INT_VAR)

endmodule
```

Key points:
- The `VERIFICATION` module must be named exactly `VERIFICATION` (it is the default `KOMPILE_MAIN_MODULE`).
- `runLemma`/`doneLemma` wrap the term under test; the single rule `runLemma(T) => doneLemma(T)` fires once to expose the term and the prover then simplifies it.
- `?_:Sort` in the RHS is an existential — proves the function returns *some* value of that sort. Use it when the result is too complex to describe concretely (e.g. symbolic input).
- The `<k> ... ... </k>` pattern matches within the full EVM configuration; the `...` elides all other cells.
- For inputs with symbolic tails (e.g. `+Bytes #buf(32, X)`), the Haskell backend must evaluate the function symbolically. This is the regime where definition efficiency matters most.

### Step 2 — Register the spec in the test runner

Open `kevm-pyk/src/tests/integration/test_prove.py` and add one line to `KOMPILE_MAIN_FILE`:

```python
KOMPILE_MAIN_FILE: Final = {
    ...
    'functional/my-simplification-spec.k': 'my-simplification-spec.k',
    ...
}
```

The spec is then automatically picked up by `FUNCTIONAL_TESTS = spec_files('functional', '*-spec.k')` and run by `test_prove_functional`.
No other changes are needed; `KOMPILE_MAIN_MODULE` defaults to `'VERIFICATION'`.

To override workers for a parallel-friendly spec:

```python
TEST_PARAMS: dict[str, TParams] = {
    ...
    'functional/my-simplification-spec.k': TParams(workers=8),
}
```

### Step 3 — Test locally

```bash
make -C kevm-pyk/ test-integration PYTEST_ARGS+="-k test_prove_functional and my-simplification"
```

## Commit discipline

- Every commit must be **atomic and self-contained** — the project must build and all fast tests must pass at each commit.
- `make -C kevm-pyk/ check` and `make -C kevm-pyk/ test-unit` are the fast gate; run before every commit.
- After any change to `.k`/`.md` source files, the kdist targets become stale.
  Rebuild before running proofs: `uv --project kevm-pyk/ run python3 -m pyk.kdist build evm-semantics.plugin` (and `.haskell` if needed).
- Proof tests (`test_prove_*`) are slow (minutes per spec); run them before marking a PR ready, not on every commit.
