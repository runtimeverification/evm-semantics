---
title: 'K/KEVM Formal Verification Workshop'
subtitle: 'Understanding the K Prover and Runtime Verification'
author:
-   Everett Hildenbrandt
-   Grigore Rosu
institute:
-   Runtime Verification
date: '\today'
theme: metropolis
fontsize: 8pt
---

Overview
--------

-   Install KEVM and KLab on your machine
-   Simple uses of the `./kevm` script
-   (Brief) introduction to KEVM
-   Verification examples: Single opcode (`ADD`), ERC20 `transfer` function
-   LTL runtime verification example

Install KEVM: Docker Way
------------------------

### Get Docker Container

```sh
docker login
# it will ask for username and password
# email will NOT work, they need their dockerhub USERNAME
# Proxy user: ehildenbproxy
# Proxy pass: ehildenb-proxy

docker run -it -u user -w /home/user/evm-semantics  \
    runtimeverificationinc/evm-semantics:trufflecon
```

### Setup Environment

```sh
cd ../
eval $(cat env)
cd evm-semantics
which klab
```

Install KEVM: From Source
-------------------------

### KEVM

-   Branch `trufflecon` of KEVM: <https://github.com/kframework/evm-semantics>
-   Build instructions in README.

    ```sh
    make llvm-deps
    make build-java
    ```

. . .

### KLab

-   Branch `master` of KLab: <https://github.com/dapphub/klab>
-   Build instructions in README.

    ```sh
    make deps-npm
    ```

-   Patch KLab (comment lines 90 - 94 of `lib/behavior.js`).
-   Should be able to run (in KEVM repo with `klab/bin` on your `PATH`):

    ```sh
    ./kevm klab-prove add-spec.k
    ./kevm klab-view  add-spec.k
    ```

`./kevm help`
-------------

```sh
usage: ./kevm run        [--backend (ocaml|java|llvm|haskell)] <pgm>  <K arg>*
       ./kevm interpret  [--backend (ocaml|llvm)]              <pgm>  <interpreter arg>*
       ./kevm kast       [--backend (ocaml|java)]              <pgm>  <output format> <K arg>*
       ./kevm prove      [--backend (java|haskell)]            <spec> <K arg>* -m <def_module>
       ./kevm search     [--backend (java|haskell)]            <pgm>  <pattern> <K arg>*
       ./kevm klab-run                                         <pgm>  <K arg>*
       ./kevm klab-prove                                       <spec> <K arg>* -m <def_module>
       ./kevm klab-view                                        <spec>

   ./kevm run       : Run a single EVM program
   ./kevm interpret : Run JSON EVM programs without K Frontend (external parser)
   ./kevm kast      : Parse an EVM program and output it in a supported format
   ./kevm prove     : Run an EVM K proof
   ./kevm search    : Search for a K pattern in an EVM program execution
   ./kevm klab-(run|prove) : Run program or prove spec and dump StateLogs which KLab can read
   ./kevm klab-view : View the statelog associated with a given program or spec

   Note: <pgm> is a path to a file containing an EVM program/test.
         <spec> is a K specification to be proved.
         <K arg> is an argument you want to pass to K.
         <interpreter arg> is an argument you want to pass to the derived interpreter.
         <output format> is the format for Kast to output the term in.
         <pattern> is the configuration pattern to search for.
         <def_module> is the module to take as axioms when doing verification.

   klab-view: Make sure that the 'klab/bin' directory is on your PATH to use this option.
```

`./kevm` examples
-----------------

-   Run a test: `./kevm run tests/etheremu-tests/...`
-   Interpret a test (fast): `./kevm interpret tests/etheremu-tests/...`
-   Run a proof: `./kevm prove tests/specs/*-spec.k`
-   Run a test under KLab: `./kevm klab-run tests/ethereum-tests/...`
-   Run a proof under KLab: `./kevm klab-prove tests/ethereum-tests/...`

-   Environment variables `MODE` and `SCHEDULE` control how KEVM executes.
-   `MODE` can be `NORMAL` or `VMTESTS`.
-   `SCHEDULE` can be `DEFAULT`, `FRONTIER`, `HOMESTEAD`, `TANGERINE_WHISTLE`, `SPURIOUS_DRAGON`, `BYZANTIUM`, `CONSTANTINOPLE`, or `PETERSBURG`.

Introduction to KEVM
--------------------

-   [data.md](../data.md) defines data-structures of EVM.
-   [network.md](../network.md) defines the EVMC status codes.
-   [evm.md](../evm.md) defines the semantics itself.
-   [driver.md](../driver.md) defines the testing harness.
-   [edsl.md](../edsl.md) defines a DSL for aiding specification for proofs.
-   [evm-node.md](../evm-node.md) defines the protobuf interface to use KEVM over RPC.

Understanding the K Prover: Single Opcode
-----------------------------------------

File `add-spec.k`:

```k
requires "evm.k"

module ADD-SPEC
    imports EVM

    rule <k> #next [ ADD ] => . ... </k>
         <schedule> SCHEDULE </schedule>
         <wordStack> W0 : W1 : WS => chop(W0 +Int W1) : WS </wordStack>
         <pc> PCOUNT => PCOUNT +Int 1 </pc>
         <gas> G => G -Int Gverylow < SCHEDULE > </gas>
      requires G >=Int Gverylow < SCHEDULE >
       andBool notBool ( #stackUnderflow ( W0 : W1 : WS , ADD )
                  orBool #stackOverflow  ( W0 : W1 : WS , ADD )
                       )
endmodule
```

. . .

-   `./kevm prove      add-spec.k --def-module EVM`
-   `./kevm klab-prove add-spec.k --def-module EVM`
-   `./kevm klab-view  add-spec.k --def-module EVM`

. . .

-   Try with side-conditions removed.

LTL Runtime Verification
------------------------

-   Compile semantics with `media/201908-trufflecon/kevm-ltl.md`, which instruments semantics (*without* modifying it).
-   Build definition:

    ```sh
    cp media/201908-trufflecon/kevm-ltl.md kevm-ltl.md
    make MAIN_MODULE=KEVM-LTL MAIN_DEFN_FILE=kevm-ltl build-llvm
    ```

-   Try verifying a property:

    ```sh
    ./kevm run --backend llvm media/201908-trufflecon/addition.evm -cLTLFORMULA='eventually revert'
    ./kevm run --backend llvm media/201908-trufflecon/addition.evm -cLTLFORMULA='always ((~ overflow) \/ eventually revert)'
    ```

Thanks!
-------

-   TruffleCon for hosting us!
-   You all for attending!
