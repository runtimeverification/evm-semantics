Verification Instructions for KEVM
==================================

We assume that KEVM is installed, and the [K tutorial] has been completed.
This document provides instructions for kompiling and running claims using KEVM.

In `tests/specs/examples`, you can find a few examples to get you started on proving with kevm.

example 1: Sum to N
-------------------
Have a look at the [sum-to-n-spec.k] file.
It has two modules:
  - `VERIFICATION` - containing the EVM program 
 and a few `simplification` rules.
  - `SUM-TO-N-SPEC` - containing the claims which will be executed.

The first step is kompiling the `.k` file with the below command.

```
kevm kompile sum-to-n-spec.k --pyk --backend haskell --syntax-module VERIFICATION --main-module VERIFICATION --definition sum-to-n-spec/haskell
```

In this example, the arguments used are:
  - `—-pyk`: a flag that enables the pyk library.
  - `—-backend haskell`: used to kompile the definition with the Haskell backend, enabling the symbolic execution ([more about it here]).
  - `--syntax-module VERIFICATION`: explicitly state the syntax module.
  - `--main-module VERIFICATION`: explicitly state the main module.
  - `--definition sum-to-n-spec/haskell`: the path where the kompiled definition is stored.

Next, run the prover with:

```
kevm prove sum-to-n-spec.k --backend haskell --definition sum-to-n-spec/haskell
```

The expected output is `#top` which represents that all the claims have been proven.

example 2: Faulty ERC20
-----------------------
```
kevm solc-to-k ERC20.sol ERC20 --pyk --main-module ERC20-VERIFICATION > erc20-bin-runtime.k 
```

- `solc-to-k` will parse a Solidity contract and generate a helper K module.
    -`--main-module` is used to set the name of the module.

```
kevm kompile erc20-spec.md --pyk --backend haskell --syntax-module VERIFICATION --main-module VERIFICATION --definition erc20-spec/haskell

kevm prove erc20-spec.md --backend haskell  --definition erc20-spec/haskell --pyk --claim ERC20-SPEC.decimals
```


example 3: benchmark address 0
------------------------------

- `kevm view-kcfg [save_directory] [spec_file] [--claim claim_label] ...` command takes the same basic arguments as `kevm prove --pyk ...` does, including:
  - `save_directory` must be passed as where the KCFGs have been saved (by a previous call to `kevm prove --pyk --save-directory save_directory ...`
  - `spec_file` is the file to look in for specifications. This file is read the same way as with `kevm prove —pyk …`; the `KProve.get_claims` is called, invoking the frontend.
  - `--claim claim_label` option is added, but unlike `kevm prove --pyk ...`, you can only repeat it once. This option lets you select an individual claim out of the `spec_file`; if not supplied, it’s assumed that only one spec is present.
  - `--spec-module spec_module` is also an inherited option.
- Updates the `tests/failing-symbolic.pyk` list to remove a bunch of working on RPC prover.

This allows running a KEVM test specification and getting visualization working with these commands:

```
mkdir kcfgs
kevm kompile --pyk --backend haskell tests/specs/benchmarks/verification.k --definition tests/specs/benchmarks/verification/haskell --main-module VERIFICATION --syntax-module VERIFICATION
kevm prove tests/specs/benchmarks/address00-spec.k --definition tests/specs/benchmarks/verification/haskell --pyk --verbose --save-directory kcfgs
kevm view-kcfg --verbose kcfgs tests/specs/benchmarks/address00-spec.k --definition tests/specs/benchmarks/verification/haskell
```


[sum-to-n-spec.k]: <./tests/specs/examples/sum-to-n-spec.k>
[erc20-spec.md]: <./tests/specs/examples/erc20-spec.md>
[K tutorial]: <https://github.com/runtimeverification/k/tree/master/k-distribution/k-tutorial>
[more about it here]: <https://github.com/runtimeverification/k/tree/master/k-distribution/k-tutorial/1_basic/20_backends#k-backends>