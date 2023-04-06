Verification Instructions for KEVM
==================================

We assume that KEVM is installed, and the [K tutorial] has been completed.
This document provides instructions for kompiling and running claims using KEVM.

In `tests/specs/examples`, you can find a few examples to get you started on proving with kevm.

Example 1: Sum to N
-------------------

Have a look at the [sum-to-n-spec.k] file.
It has two modules:

  - `VERIFICATION` - containing the EVM program and a few `simplification` rules.
  - `SUM-TO-N-SPEC` - containing the claims which will be executed.

The first step is kompiling the `.k` file with the below command.

```sh
kevm kompile sum-to-n-spec.k --pyk --backend haskell --syntax-module VERIFICATION --main-module VERIFICATION --definition sum-to-n-spec/haskell
```

In this example, the arguments used are:

  - `—-pyk`: a flag that enables the pyk library.
  - `—-backend haskell`: used to kompile the definition with the Haskell backend, enabling the symbolic execution ([more about it here]).
  - `--syntax-module VERIFICATION`: explicitly state the syntax module.
  - `--main-module VERIFICATION`: explicitly state the main module.
  - `--definition sum-to-n-spec/haskell`: the path where the kompiled definition is stored.

Next, run the prover with:

```sh
kevm prove sum-to-n-spec.k --backend haskell --definition sum-to-n-spec/haskell
```

The expected output is `#Top` which represents that all the claims have been proven.

Example 2: Faulty ERC20
-----------------------

This example will describe the process of running claims for an ERC20 contract.
Have a look at [erc20-spec.md].
It contains claims for a few basic ERC20 properties and the helper modules required to run the proofs.
The ERC20 Solidity contract that is tested is [ERC20.sol].

In this example, we rely on a helper module, `ERC20-VERIFICATION`, which must be generated from the [ERC20.sol] Solidity contract.
The module is generated using the following `solc-to-k` command.

```sh
kevm solc-to-k ERC20.sol ERC20 --pyk --main-module ERC20-VERIFICATION > erc20-bin-runtime.k
```

- `solc-to-k` will parse a Solidity contract and generate a helper K module.
- `--main-module` is used to set the name of the module.

The generated `erc20-bin-runtime.k` file contains K rules and productions for the contract’s bytecode, storage indexes for the state variables, and function selectors, among others.
These rules are then used in the claims. As an example, the `#binRuntime(ERC20)` production, which is found in the `<program>` cell, will rewrite to `#parseByteStack (contractBytecode)`, parsing the hexadecimal string into a `ByteStack`.

Following this, we can compile the Markdown file with:

```sh
kevm kompile erc20-spec.md --pyk --backend haskell --syntax-module VERIFICATION --main-module VERIFICATION --definition erc20-spec/haskell
```

Next, run the prover with:

```sh
kevm prove erc20-spec.md --backend haskell  --definition erc20-spec/haskell --pyk --claim ERC20-SPEC.decimals
```

Here, `--claim` tells the prover to run only the `decimals` spec from the `ERC20-SPEC` module.

More to know
------------

To prove one of the specifications:

```sh
kevm prove tests/specs/erc20/ds/transfer-failure-1-a-spec.k --definition tests/specs/erc20/verification/haskell
```

You can also debug proofs interactively:

```sh
kevm prove tests/specs/erc20/ds/transfer-failure-1-a-spec.k --definition tests/specs/erc20/verification/haskell --debugger
```

In addition to this, you can use `kevm show-kcfg ...` or `kevm view-kcfg ...` to get a visualization.

`kevm view-kcfg [spec_file] [--save-directory save_directory] [--claim claim_label] ...` command takes the same basic arguments as `kevm prove --pyk ...` does, including:
  - `spec_file` is the file to look in for specifications. This file is read like with `kevm prove —pyk …`; the `KProve.get_claims` invokes the frontend.
  - `--save_directory` must be passed as where the KCFGs have been saved (by a previous call to `kevm prove --pyk --save-directory save_directory ...`
  - `--claim claim_label` option is added, but unlike the `kevm prove --pyk ...`, you can only repeat it once. This option lets you select an individual claim out of the `spec_file`; if not supplied, it’s assumed that only one spec is present.
  - `--spec-module spec_module` is also an inherited option.

The interactive KCFG (`view-kcfg`) puts your terminal in *application mode*. To select text in this mode, hold the modifier key provided by your terminal emulator (typically SHIFT or OPTION) while clicking and dragging. Refer to the [Textualize documentation](https://github.com/Textualize/textual/blob/main/FAQ.md#how-can-i-select-and-copy-text-in-a-textual-app) for more information.

A running example:

```sh
mkdir kcfgs
kevm kompile --pyk --backend haskell tests/specs/benchmarks/verification.k --definition tests/specs/benchmarks/verification/haskell --main-module VERIFICATION --syntax-module VERIFICATION
kevm prove tests/specs/benchmarks/address00-spec.k --definition tests/specs/benchmarks/verification/haskell --pyk --verbose --save-directory kcfgs
kevm view-kcfg --verbose kcfgs tests/specs/benchmarks/address00-spec.k --definition tests/specs/benchmarks/verification/haskell
```

[sum-to-n-spec.k]: <./tests/specs/examples/sum-to-n-spec.k>
[erc20-spec.md]: <./tests/specs/examples/erc20-spec.md>
[ERC20.sol]: <./tests/specs/examples/ERC20.sol>
[K tutorial]: <https://github.com/runtimeverification/k/tree/master/k-distribution/k-tutorial>
[more about it here]: <https://github.com/runtimeverification/k/tree/master/k-distribution/k-tutorial/1_basic/20_backends#k-backends>
