---
title: 'Firefly'
subtitle: 'Solidity testing using KEVM'
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

-   (Brief) Introduction to KEVM
-   Introduction to Firefly
-   Firefly Demo
-   Future Directions

(Brief) Introduction to KEVM
----------------------------

-   Repository: <https://github.com/kframework/evm-semantics>
-   Considered the canonical spec of EVM: <https://ethereum-magicians.org/t/jello-paper-as-canonical-evm-spec/2389>
-   All K tooling is derived automatically:
    -   Reference EVM interpreter
    -   Symbolic execution engine
    -   EVM bytecode formal verification engine
    -   Several EVM bytecode debugger options

Introduction to Firefly
-----------------------

-   `npm` package here: <https://www.npmjs.com/package/kevm-ganache-cli>.
-   Drop-in replacement for `ganache-cli`, can be used directly by Truffle.

    Instead of:

    ```sh
    npx ganache-cli
    ```

    run:

    ```sh
    npx kevm-ganache-cli
    ```

. . .

### Why??

-   Higher confidence in results (run tests with both!).
-   More features to come:
    -   Test coverage metrics.
    -   Automated property verification.
    -   Test generation.
    -   Contract symbolic execution.
    -   ... your ideas??

Firefly Demo - Setup
--------------------

Instructions from <https://www.npmjs.com/package/kevm-ganache-cli>:

. . .

### Install KEVM (once)

**TODO**: Update release URL.

```sh
sudo apt install nodejs npm curl git
curl --location 'https://github.com/kframework/evm-semantics/releases/download/v1.0.0-a47e4b2/kevm_1.0.0_amd64.deb' \
     --output kevm_1.0.0_amd64.deb
sudo apt install ./kevm_1.0.0_amd64.deb
```

. . .

### Install `npx` (once)

```sh
sudo npm install -g npx
```

Firefly Demo - Run OpenZeppelin Tests
-------------------------------------

### Start `kevm-ganache-cli`

```sh
npx kevm-ganache-cli                                                                                         \
    --gasLimit 0xfffffffffff                                                                                 \
    --account="0x2bdd21761a483f71054e14f5b827213567971c676928d9a1808cbfa4b7501200,1000000000000000000000000" \
    --account="0x2bdd21761a483f71054e14f5b827213567971c676928d9a1808cbfa4b7501201,1000000000000000000000000" \
    --account="0x2bdd21761a483f71054e14f5b827213567971c676928d9a1808cbfa4b7501202,1000000000000000000000000" \
    --account="0x2bdd21761a483f71054e14f5b827213567971c676928d9a1808cbfa4b7501203,1000000000000000000000000" \
    --account="0x2bdd21761a483f71054e14f5b827213567971c676928d9a1808cbfa4b7501204,1000000000000000000000000" \
    --account="0x2bdd21761a483f71054e14f5b827213567971c676928d9a1808cbfa4b7501205,1000000000000000000000000" \
    --account="0x2bdd21761a483f71054e14f5b827213567971c676928d9a1808cbfa4b7501206,1000000000000000000000000" \
    --account="0x2bdd21761a483f71054e14f5b827213567971c676928d9a1808cbfa4b7501207,1000000000000000000000000" \
    --account="0x2bdd21761a483f71054e14f5b827213567971c676928d9a1808cbfa4b7501208,1000000000000000000000000" \
    --account="0x2bdd21761a483f71054e14f5b827213567971c676928d9a1808cbfa4b7501209,1000000000000000000000000"
```

. . .

### Run OpenZeppelin tests

```sh
git clone 'https://github.com/OpenZeppelin/openzeppelin-contracts.git'
cd openzeppelin-contracts
git checkout b8c8308
npm install
npx truffle test test/token/ERC20/ERC20.test.js
```

Firefly Demo - Catching Arithmetic Overflow
-------------------------------------------

### Instrumented Rule

```k
    syntax LTLEvent ::= "overflow"
 // ------------------------------
    rule <k> ADD W0 W1 ... </k>
         <events> EVENTS (.Set => SetItem(overflow)) </events>
      requires notBool overflow in EVENTS
       andBool W0 +Word W1 =/=Int W0 +Int W1
      [priority(24)]
```

-   `#end EVMC_CUSTOM ...` is a custom error message which halts execution there.
-   We record the program counter for source map back to Solidity.
-   `W0 +Word W1` is modulo $2^256$, `W0 +Int W1` is unbounded.
-   `priority(25)` instructs KEVM to prefer this rule when it applies.

Firefly Demo - Catching Arithmetic Overflow
-------------------------------------------

-   Currently causes `kevm-ganache-cli` to crash if there is an overflow violation.
-   Should handle this more gracefully.

Firefly Demo - Arithmetic Overflow should `REVERT`
--------------------------------------------------

### Instrument Semantics

```k
    configuration
      ...
      <temporal-formula> .Formula </temporal-formula>
      <log> .List </log>
      ...

    syntax Formula ::= ".Formula"
                     | "overflow" | "revert"
                     | "E" Formula | Formula "->" Formula
 // -----------------------------------------------------
    rule <k> ADD W0 W1 => W0 +Word W1 ~> #push ... </k>
      requires W0 +Word W1 ==Int W0 +Int W1

    rule <k> ADD W0 W1 => W0 +Word W1 ~> #push ... </k>
         <pc> PCOUNT </pc>
         <temporal-formula> overflow => . ... </temporal-formula>
      requires W0 +Word W1 =/=Int W0 +Int W1
      [priority(25)]
```

### Run Test

```k

```
