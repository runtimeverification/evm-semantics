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

KEVM Extensions - Event Monitoring
----------------------------------

Compile semantics with additional file `media/201908-trufflecon/kevm-ltl.md`.

```k
    syntax LTLEvent ::= "overflow"
 // ------------------------------
    rule <k> ADD W0 W1 ... </k>
         <events> EVENTS (.Set => SetItem(overflow)) </events>
      requires notBool overflow in EVENTS
       andBool W0 +Word W1 =/=Int W0 +Int W1
      [priority(24)]

    syntax LTLEvent ::= "revert"
 // ----------------------------
    rule <k> REVERT _ _ ... </k>
         <events> EVENTS (.Set => SetItem(revert)) </events>
      requires notBool revert in EVENTS
      [priority(24)]
```

-   Monitors built-in to the KEVM semantics as an extension.
-   Can build arbitrary LTL formula over the monitors.

KEVM Extensions - LTL Model Checking
------------------------------------

### Input file `addition.evm`

```evm
load { "gas"  : 10000000
  // Query: always ((~ overflow) \/ eventually revert)
  // , "code" : UNSAFEADD(100        , 100) // True
  // , "code" : UNSAFEADD(maxUInt256 , 100) // False
  // , "code" :   SAFEADD(100        , 100) // True
     , "code" :   SAFEADD(maxUInt256 , 100) // True
     }

start
```

. . .

### Query

```sh
./kevm run --backend llvm media/201908-trufflecon/addition.evm -cLTLFORMULA='always (overflow -> eventually revert)'
```

Truffle Firefly Plugin
----------------------

-   Developed with help from Truffle devs today as plugin!
-   Modified OpenZeppelin test-suite which links to `truffle-plugin-firefly`.

```sh
npx truffle run firefly SafeMath 'always (overflow -> eventually revert)'
```

