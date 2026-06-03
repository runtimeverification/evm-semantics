# Testing a Local Haskell Backend with kup

`kup` can install K (or any managed package) with one of its Nix flake inputs replaced by a local checkout.
This is the right way to test a local haskell-backend change against a full kevm proof without modifying the project's flake.

---

## How overrides work

Every package managed by `kup` is a Nix flake with declared inputs.
`kup install <pkg> --override <input-path> <local-dir>` tells Nix to use the local directory's `flake.nix` in place of the upstream input when building.

The input path follows the flake input tree shown by `kup list <pkg> --inputs`.
For `k.openssl.procps`:

```
k.openssl.procps
├── haskell-backend - github:runtimeverification/haskell-backend (bf7eaa5)
├── llvm-backend    - github:runtimeverification/llvm-backend     (618f530)
└── rv-nix-tools    - github:runtimeverification/rv-nix-tools     (854d4f0)
```

Top-level inputs (like `haskell-backend` here) are specified by name alone.
Nested inputs use slash-separated paths (e.g. `k-framework/llvm-backend` in the kevm tree where llvm-backend is under k-framework).

`kup list <pkg> --inputs` shows the current input tree and their pinned hashes.
Any input labelled `follows <path>` is an alias; override the `<path>` instead.

---

## Installing K with a local haskell-backend

```bash
# See the current input tree first:
kup list k.openssl.procps --inputs

# Install the same K version but replace haskell-backend with a local checkout:
kup install k.openssl.procps \
    --version v7.1.323 \
    --override haskell-backend ~/src/haskell-backend
```

`--version v7.1.323` pins K itself to the same tag/commit already installed, so only the haskell-backend changes.
Omit `--version` to also upgrade K to the latest available.

Nix builds the haskell-backend from source, which takes several minutes the first time (subsequent builds with the same source hash are cached).
The installed K will have `-dirty` appended to its version string if the local checkout has uncommitted changes.

### Overriding with a remote branch/commit

To test a backend revision without a local checkout, pass a **bare git ref** (branch, tag, or commit) — kup constructs the `github:<org>/<repo>/<ref>` URL for that input itself:

```bash
kup install k.openssl.procps \
    --version v7.1.329 \
    --override haskell-backend 35a6746c5
```

Do **not** pass a full `github:` URL as the override value — kup prepends the input's own `github:runtimeverification/haskell-backend/` prefix, so a full URL is doubled and rejected (`'…/35a6746c5' is not a branch/tag name`).
A remote ref override also yields a `-dirty` K version string.

---

## Reverting to the stock version

```bash
# Re-install without any override to restore the upstream haskell-backend:
kup install k.openssl.procps --version v7.1.323
```

---

## After installation: rebuild kdist

The kdist targets are compiled against the K installation.
After changing K (including its haskell-backend), the compiled definitions are stale and must be rebuilt:

```bash
# In evm-semantics:
uv --project kevm-pyk/ run kevm-kdist build evm-semantics.haskell
```

The new `definition.kore` and LLVM library are placed under `~/.cache/kdist-<new-hash>/` automatically.

---

## Observed install behaviour

During the install, kup emits two deprecation warnings:

```
warning: '--update-input' is a deprecated alias for 'flake update' and will be
removed in a future version.
warning: not writing modified lock file of flake '...'
```

These are internal to kup's Nix invocation and are harmless.
The install proceeds normally.

The progress output shows each derivation being built: individual binaries (`kore-exec`, `kore-rpc`, `kore-rpc-booster`, `booster-dev`, etc.) each get their own `.drv` build step.
Building the haskell-backend from source takes several minutes.

A successful install ends with:

```
✅ Successfully updated 'k' version <pkg-url> (v7.1.323).
```

The installed K version string will have `-dirty` appended if the local checkout has uncommitted changes.

## What kup actually does

Internally `kup install --override` runs something equivalent to:

```
nix build github:runtimeverification/k/<commit> \
    --override-input haskell-backend path:/home/dev/src/haskell-backend \
    --impure
```

The `--impure` flag is required for local path overrides (because local paths are not reproducible from the lock file alone).
kup handles all of this transparently; you never need to call `nix` directly.

---

## Useful kup commands

| Command | What it does |
|---|---|
| `kup list` | Show all installed/available packages |
| `kup list <pkg> --inputs` | Show the flake input tree for a package |
| `kup install <pkg> --version <v>` | Install a specific version |
| `kup install <pkg> --override <input> <path>` | Install with a local input override |
| `kup install <pkg>` | Upgrade to the latest available version |
