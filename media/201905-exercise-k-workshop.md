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
-   KEVM lemma proofs
-   ERC20 `transfer` functions
-   Open verification challenge

Install KEVM
------------

### KEVM

-   Branch `kevm-lemmas` of KEVM: <https://github.com/kframework/evm-semantics>
-   Build instructions in README.

    ```sh
    make deps
    make build-java
    ```

-   Should be able to run:

    ```sh
    make test-prove-gen test-prove-kevm-lemmas -j3
    ```

. . .

### KLab

-   Branch `master` of KLab: <https://github.com/dapphub/klab>
-   Build instructions in README.

    ```sh
    make deps-npm
    ```
