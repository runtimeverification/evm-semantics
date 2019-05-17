---
title: 'K Workshop'
subtitle: 'Understanding the K Prover'
author:
-   Everett Hildenbrandt
institute:
-   Runtime Verification
-   ConsenSys
date: '\today'
theme: metropolis
fontsize: 8pt
---

Overview
--------

-   Install KEVM and KLab on your machine
-   Simple uses of the `./kevm` script
-   (Brief) introduction to KEVM
-   Verification examples: KEVM lemma proofs, ERC20 `transfer` function
-   Open verification challenge

Install KEVM
------------

### KEVM

-   Branch `kevm-lemmas` of KEVM: <https://github.com/kframework/evm-semantics>
-   Build instructions in README.

    ```sh
    make deps
    make build-java
    make build-ocaml
    ```

-   Should be able to run:

    ```sh
    make test-prove-verified
    make test-prove-gen -j3
    ```

. . .

### KLab

-   Branch `master` of KLab: <https://github.com/dapphub/klab>
-   Build instructions in README.

    ```sh
    make deps-npm
    ```

-   Should be able to run (in KEVM repo with `klab/bin` on your `PATH`):

    ```sh
    make tests/specs/verified/kevm-lemmas-spec.k
    ./kevm klab-prove tests/specs/verified/kevm-lemmas-spec.k --boundary-cells k,pc
    ```

`./kevm help`
-------------

```sh
$ ./kevm help

usage: ./kevm (run|kast)       [--backend (ocaml|java|llvm|haskell)] <pgm>  <K args>*
       ./kevm interpret        [--backend (ocaml|llvm)]              <pgm>
       ./kevm prove            [--backend (java|haskell)]            <spec> <K args>*
       ./kevm klab-(run|prove)                                       <spec> <K args>*

   ./kevm run       : Run a single EVM program
   ./kevm interpret : Run JSON EVM programs without K Frontend (external parser)
   ./kevm prove     : Run an EVM K proof
   ./kevm klab-(run|prove) : Run or prove a spec and launch KLab on the execution graph.

   Note: <pgm> is a path to a file containing an EVM program/test.
         <spec> is a K specification to be proved.
         <K args> are any arguments you want to pass to K when executing/proving.

   KLab: Make sure that the 'klab/bin' directory is on your PATH to use this option.
```

`./kevm` examples
-----------------

> -   Run a test: `MODE=... SCHEDULE=... ./kevm run tests/etheremu-tests/...`
> -   Interpret a test (fast): `MODE=... SCHEDULE=... ./kevm interpret tests/etheremu-tests/...`
> -   Run a proof: `./kevm prove tests/specs/*-spec.k`
> -   Run a test under KLab: `MODE=... SCHEDULE=... ./kevm klab-run tests/ethereum-tests/...`
> -   Run a proof under KLab: `./kevm klab-prove tests/ethereum-tests/...`

Introduction to KEVM
--------------------

-   File [data.md](../data.md) defines data-structures of EVM.
-   File [evm.md](../evm.md) defines the semantics itself.
-   File [driver.md](../driver.md) defines the testing harness.
-   File [edsl.md](../edsl.md) defines a DSL for aiding specification for proofs.

Verification Examples
---------------------

### KEVM Lemmas

-   File [kevm-lemmas-spec.md](../kevm-lemmas-spec.k)
-   Summaries of the "positive" cases of arithmetic opcodes and push
-   Work through how to use KLab to discover preconditions
-   Complete the push, push, add specification

```sh
make test-prove-verified
```

. . .

### ERC20 `transfer` functions

-   Run proof.

    ```sh
    make test-prove-gen
    ```

-   Explain ini file format of [ds-token-erc20-spec.ini](../tests/specs/ds-token-erc20/ds-token-erc20-spec.ini)
-   Delete all except the `transfer` blocks
-   Remove `requires` clauses to explore result in KLab

Open Verification Challenge
---------------------------

Rest of time.

-   Work on `transferFrom` function?
-   Try to setup your own contract?

Thanks!
-------

-   ConsenSys for hosting us!
-   You all for attending!
