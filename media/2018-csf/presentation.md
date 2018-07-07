---
title: 'KEVM: A Complete Formal Semantics of the Ethereum Virtual Machine'
subtitle: 'K, EVM, Now, and the Future'
author:
-   Everett Hildenbrandt
-   Manasvi Saxena
-   Nishant Rodrigues
-   Lucas Peña
-   TODO remaining authors
institute:
-   University of Illinois, Urbana-Champaign
-   Runtime Verification, Inc.
date: '\today'
theme: metropolis
fontsize: 8pt
header-includes:
-   \newcommand{\K}{\ensuremath{\mathbb{K}}}
---

Overview
--------

1.  \K{} Framework
2.  Ethereum Virtual Machine
3.  KEVM uses and future work

\K{} Framework
==============

The Vision: Language Independence
---------------------------------

Separate development of PL software into two tasks:

. . .

### The Programming Language

PL expert builds rigorous and formal spec of the language in a high-level human-readable semantic framework.

. . .

### The Tooling

Build each tool *once*, and apply it to every language, eg:

-   Parser
-   Interpreter
-   Debugger
-   Compiler
-   Model Checker
-   Program Verifier

The Vision: Language Independence
---------------------------------

![K Tooling Overview](k-overview.png)

**TODO**: Use new bubble diagram based on RV logo.

Current Semantics
-----------------

Many languages have full or partial \K{} semantics, this lists some notable ones (and their primary usage).

-   [C](https://github.com/kframework/c-semantics): detecting undefined behavior
-   [Java](https://github.com/kframework/java-semantics): detecting racy code
-   [EVM](https://github.com/kframework/evm-semantics): verifying smart contracts
-   [LLVM](https://github.com/kframework/llvm-semantics): compiler validation (to x86)
-   [JavaScript](https://github.com/kframework/javascript-semantics): finding disagreements between JS engines
-   [P4](https://github.com/kframework/p4-semantics): SDN data-layer verification
-   many others ...

\K{} Specifications: Syntax
---------------------------

Concrete syntax built using EBNF style:

```k
    syntax Exp ::= Int | Id | "(" Exp ")" [bracket]
                 | Exp "*" Exp
                 > Exp "+" Exp // looser binding

    syntax Stmt ::= Id ":=" Exp
                  | Stmt ";" Stmt
                  | "return" Exp
```

. . .

This would allow correctly parsing programs like:

```imp
    a := 3 * 2;
    b := 2 * a + 5;
    return b
```

\K{} Specifications: Configuration
----------------------------------

Tell \K{} about the structure of your execution state.
For example, a simple imperative language might have:

```k
    configuration <k>     $PGM:Program </k>
                  <env>   .Map         </env>
                  <store> .Map         </store>
```

. . .

> -   `<k>` will contain the initial parsed program
> -   `<env>` contains bindings of variable names to store locations
> -   `<store>` conaints bindings of store locations to integers

\K{} Specifications: Transition Rules
-------------------------------------

Using the above grammar and configuration:

. . .

### Variable lookup

```k
    rule <k> X:Id => V ... </k>
         <env>   ...  X |-> SX ... </env>
         <store> ... SX |-> V  ... </store>
```

. . .

### Variable assignment

```k
    rule <k> X := I:Int => . ... </k>
         <env>   ...  X |-> SX       ... </env>
         <store> ... SX |-> (V => I) ... </store>
```

Example Execution
-----------------

### Program

```imp
    a := 3 * 2;
    b := 2 * a + 5;
    return b
```

### Initial Configuration

```k
    <k>     a := 3 * 2 ; b := 2 * a + 5 ; return b </k>
    <env>   a |-> 0    b |-> 1 </env>
    <store> 0 |-> 0    1 |-> 0 </store>
```

Example Execution (cont.)
-------------------------

### Variable assignment

```k
    rule <k> X := I:Int => . ... </k>
         <env>   ...  X |-> SX       ... </env>
         <store> ... SX |-> (V => I) ... </store>
```

### Next Configuration

```k
    <k>     a := 6 ~> b := 2 * a + 5 ; return b </k>
    <env>   a |-> 0    b |-> 1 </env>
    <store> 0 |-> 0    1 |-> 0 </store>
```

Example Execution (cont.)
-------------------------

### Variable assignment

```k
    rule <k> X := I:Int => . ... </k>
         <env>   ...  X |-> SX       ... </env>
         <store> ... SX |-> (V => I) ... </store>
```

### Next Configuration

```k
    <k>               b := 2 * a + 5 ; return b </k>
    <env>   a |-> 0    b |-> 1 </env>
    <store> 0 |-> 6    1 |-> 0 </store>
```

Example Execution (cont.)
-------------------------

### Variable lookup

```k
    rule <k> X:Id => V ... </k>
         <env>   ...  X |-> SX ... </env>
         <store> ... SX |-> V  ... </store>
```

### Next Configuration

```k
    <k>     a ~> b := 2 * [] + 5 ; return b </k>
    <env>   a |-> 0    b |-> 1 </env>
    <store> 0 |-> 6    1 |-> 0 </store>
```

Example Execution (cont.)
-------------------------

### Variable lookup

```k
    rule <k> X:Id => V ... </k>
         <env>   ...  X |-> SX ... </env>
         <store> ... SX |-> V  ... </store>
```

### Next Configuration

```k
    <k>     6 ~> b := 2 * [] + 5 ; return b </k>
    <env>   a |-> 0    b |-> 1 </env>
    <store> 0 |-> 6    1 |-> 0 </store>
```

Example Execution (cont.)
-------------------------

### Variable lookup

```k
    rule <k> X:Id => V ... </k>
         <env>   ...  X |-> SX ... </env>
         <store> ... SX |-> V  ... </store>
```

### Next Configuration

```k
    <k>          b := 2 * 6 + 5 ; return b </k>
    <env>   a |-> 0    b |-> 1 </env>
    <store> 0 |-> 6    1 |-> 0 </store>
```

Example Execution (cont.)
-------------------------

### Variable assignment

```k
    rule <k> X := I:Int => . ... </k>
         <env>   ...  X |-> SX       ... </env>
         <store> ... SX |-> (V => I) ... </store>
```

### Next Configuration

```k
    <k>     b := 17 ~> return b </k>
    <env>   a |-> 0    b |-> 1 </env>
    <store> 0 |-> 6    1 |-> 0 </store>
```

Example Execution (cont.)
-------------------------

### Variable assignment

```k
    rule <k> X := I:Int => . ... </k>
         <env>   ...  X |-> SX       ... </env>
         <store> ... SX |-> (V => I) ... </store>
```

### Next Configuration

```k
    <k>                return b </k>
    <env>   a |-> 0    b |-> 1  </env>
    <store> 0 |-> 6    1 |-> 17 </store>
```

Ethereum Virtual Machine
========================

**TODO**: Add citations.

Blockchain
----------

-   Append-only ledger of user-submitted transactions.
-   Can be simple transfers of value (eg. Bitcoin).
-   Miners select next block of transactions to include in ledger using consensus algorithm.[^notThisTalk]
-   Ethereum adds:
    -   New currency! (Ether)
    -   Accounts have an associated *storage* and *code* which only transactions by that account can read/modify (onchain).
    -   Transactions can have associated *programs* written in EVM (Ethereum Virtual Machine).
    -   Miners execute transaction code to calculate the new world state (new account balances, storage, code, etc...)

[^notThisTalk]: This talk is not about the consensus algorithms.

EVM (Ethereum Virtual Machine)
------------------------------

Is a stack-based bytecode over 256-bit words.

Example program (sum 0 - 10):

```evm
  PUSH(1, 0)  ; PUSH(1, 0)  ; MSTORE
; PUSH(1, 10) ; PUSH(1, 32) ; MSTORE
; JUMPDEST
; PUSH(1, 0) ; PUSH(1, 32) ; MLOAD ; GT
; ISZERO ; PUSH(1, 43) ; JUMPI
; PUSH(1, 32) ; MLOAD ; PUSH(1, 0)  ; MLOAD ; ADD ; PUSH(1, 0)  ; MSTORE
; PUSH(1, 1)          ; PUSH(1, 32) ; MLOAD ; SUB ; PUSH(1, 32) ; MSTORE
; PUSH(1, 10) ; JUMP
; JUMPDEST
; PUSH(1, 0) ; MLOAD ; PUSH(1, 0) ; SSTORE
; .OpCodes
```

Enforcing Termination (Gas)
---------------------------

-   User submitted transactions could be problematic, what if they have infinite loops?
-   Now miners are stuck trying to execute infinite transaction, instead of deciding consensus of the ledger for us!
-   Solution:
    -   Each opcode costs some *gas*, which is paid for in Ether before execution.
    -   Gas spent for execution is converted back to Ether and paid to the miner.
    -   Gas not spent for execution is converted back to Ether and refunded to the original account.

Notes:

-   Tuning gas costs is an ongoing challenge, it's important to charge according to actual compute resources used (storage, memory, and CPU time).
-   New hardware means that there could be attack vectors on current gas costs; tuning is an *ongoing* effort.
-   Occasional hardfork updates to the network correct the gas costs (but also often complicate the gas logic!).

Intercontract Executions (and the ABI)
--------------------------------------

-   Contracts can call other contracts, which could even call the original contract again (reentrancy!!).
-   Payload to other contract is a raw string of bytes called `callData`.
-   *External* to the EVM, the Ethereum ABI has been developed:
-   Specifies:
    -   Calling conventions (how to interpret `callData` correctly).
    -   Some high-level types (and their mapping to EVM base types).

EVM Nuicances (**TODO**: Spelling)
-------------

-   256-bit words: lots of use for crypto, but a pain for mapping cleanly to commodity hardware.
-   8-bit word-array local memory: complicates symbolic reasoning, 256-bit word expressions must be chopped up into 32 8-bit word expressions.
-   No built-in calling conventions: ABI is declared external to EVM.
-   **TODO**: More nuicances.

KEVM: Status and Current Uses
=============================

Correctness and Performance
---------------------------

-   Pass the VMTests and GeneralStateTests of the [Ethereum Test Suite](https://github.com/ethereum/tests).
-   Roughly an order of magnitude slower than cpp-ethereum (reference implementation in C++).

**TODO**: Include performance chart.

As Execution Engine
-------------------

[Mantis client](**TODO**: cite) has integration with KEVM, can run it as a node on the KEVM testnet.

For Formal Verification
-----------------------

-   Runtime Verification, Inc. offers audits as a service, typical process is:
    1.  Specify high-level business logic in English, confirm with customer.[^usuallyNotDone]
    2.  Refine to a mathematical definition of logic, conferm with customer.
    3.  Refine to a set of Reachability Claims to be discharged by the K prover.
    4.  Fix bugs in contract and specification until the K prover is satisfied.
    5.  Send all documents generated and list of issues found to customer.

-   Some other independent groups also using K prover to verify their smart contract stack (eg. [DappHub](https://github.com/kframework/dapphub)).
    -   We assist as we can, fix bugs as we can (all of these tools are open source).

[^usuallyNotDone]: Surprisingly, usually smart contract developers don't have a high-level specification of their contracts.

Future Work
-----------

-   **TODO**

Conclusion
==========

Sponsors
--------

-   IOHK: Grants to both UIUC group (Formal Systems Lab), and to Runtime Verification, Inc.
-   Ethereum Foundation: Grant to Runtime Verification, Inc.
-   NSF: **TODO** list any NSF grants we have put down.
-   **TODO**: list any other grants we should here.

Questions?
----------

Thanks for listening!
