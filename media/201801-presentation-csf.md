---
title: 'KEVM: A Complete Formal Semantics of the Ethereum Virtual Machine [@hildenbrandt-saxena-zhu-rodrigues-daian-guth-moore-zhang-park-rosu-2018-csf]'
subtitle: 'K, EVM, and KEVM'
author:
-   Everett Hildenbrandt
-   Manasvi Saxena
-   Nishant Rodrigues
-   Xiaoran Zhu
-   Philip Daian
-   Dwight Guth
-   Brandon Moore
-   Daejun Park
-   Yi Zhang
-   Andrei \c{S}tef\u{a}nescu
-   Grigore Ro\c{s}u
institute:
-   University of Illinois, Urbana-Champaign
-   Runtime Verification, Inc.
-   Cornell Tech, IC3
-   East China Normal University
date: '\today'
theme: metropolis
fontsize: 10pt
header-includes:
-   \newcommand{\K}{\ensuremath{\mathbb{K}}}
---

Overview
--------

1.  \K{} Framework
2.  Ethereum Virtual Machine
3.  KEVM Uses

### Links

-   KEVM Repository: <https://github.com/kframework/evm-semantics>
-   K Repository: <https://github.com/kframework/k>
-   Runtime Verification: <https://runtimeverification.com>
-   Verified smart contracts: <https://github.com/runtimeverification/verified-smart-contracts>

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

Build each tool *once*, and apply it to every language, eg.:

-   Parser
-   Interpreter
-   Debugger
-   Compiler
-   Model Checker
-   Program Verifier

The Vision: Language Independence
---------------------------------

![K Tooling Overview](media/images/k-overview.png)

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

-   `<k>` will contain the initial parsed program
-   `<env>` contains bindings of variable names to store locations
-   `<store>` contains bindings of store locations to integers

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

Blockchain
----------

-   Append-only ledger of user-submitted transactions.
-   Mostly simple transfers of value.
-   Miners select next block of transactions using consensus algorithm.[^notThisTalk]
-   Ethereum adds:
    -   New currency! (Ether)
    -   Accounts have an associated *storage* and *code* which only transactions by that account can read/modify (onchain).
    -   Transactions can have associated *programs* written in EVM (Ethereum Virtual Machine).[^smartContracts]
    -   Miners execute transaction code to calculate the new world state (new account balances, storage, code, etc...).

[^notThisTalk]: This talk is not about the consensus algorithms.
[^smartContracts]: Cool kids call these programs *smart contracts*, or *contracts*.

EVM (Ethereum Virtual Machine)
------------------------------

Is a stack-based bytecode over 256-bit words.

Example program (sum 0 - 10):

\footnotesize

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

\normalsize

Enforcing Termination (Gas)
---------------------------

-   User submitted transactions could have infinite loops (DoS attacks!).
-   Solution:
    -   Each opcode costs some *gas*, paid for in Ether.
    -   Spent gas awarded to miner, remaining refunded to account.

Notes:

-   It's important to charge according to actual used compute resources.
-   Tuning gas costs is an *ongoing* challenge.
    -   New hardware available $\rightarrow$ new gas model.
-   Hardforks update the gas constants/rules.

Intercontract Executions (and the ABI)
--------------------------------------

-   Contracts can call other contracts (re-entrancy!).
-   Payload to other contract is a raw string of bytes called `callData`.
-   *External* to the EVM, the Ethereum ABI has been developed:
-   Specifies:
    -   Calling conventions (how to interpret `callData` correctly).
    -   Some high-level types (and their mapping to EVM words).

EVM Nuisances
-------------

-   Unstructured controlflow: dynamically calculable jump destinations.
-   256-bit words: useful for crypto, pain for hardware.
-   8-bit word-array local memory: complicates symbolic reasoning.
-   No built-in calling conventions: ABI is declared external to EVM.
-   `eval` capability: copying bytes as code and running is bad for analysis.

KEVM: Status and Current Uses
=============================

Correctness and Performance
---------------------------

-   Pass the VMTests and GeneralStateTests of the [Ethereum Test Suite](https://github.com/ethereum/tests).

. . .

-   Roughly an order of magnitude slower than cpp-ethereum (reference implementation in C++).

    **Test Set** (no. tests)   **KEVM**  **cpp-ethereum**
    ------------------------- --------- -----------------
    VMAll (40683)                 99:41              4:42
    GSNormal (22705)              35:00              1:30

. . .

-   (Non-empty) lines of code comparison:

    KEVM: 2644

    cpp-ethereum: 4588

Assertion Violation Checker
---------------------------

-   EVM has designated `INVALID` opcode, halts and discards gas.
-   Has been used to specify "assertion failure" in HLLs.[^hlls]
-   Symbolically execute and look for paths ending in `INVALID`.

. . .

-   Co-invariant checking - "`INVALID` never happens".
-   Very little tooling effort needed after building semantics.
-   Similar techniques used to find undefined behaviour in C programs.

[^hlls]: High-level languages (which compile to EVM).

Reachibility Logic Prover [@stefanescu-ciobaca-mereuta-moore-serbanuta-rosu-2014-rta]
-------------------------------------------------------------------------------------

-   Takes operational semantics as input (no axiomatic semantics).[^inthiscaseK]
-   Generalization of Hoare Logic:
    -   Hoare triple: $\{\textit{Pre}\} \textit{Code} \{\textit{Post}\}$
    -   Reachability claim: $\widehat{\textit{Code}} \land \widehat{\textit{Pre}} \Rightarrow \epsilon \land \widehat{\textit{Post}}$
    -   "Any instance of $\widehat{\textit{Code}}$ which satisfies $\widehat{Pre}$ either does not terminate or reaches an instance of $\epsilon$ (empty program) which satisfies $\widehat{Post}$".
    No need for end state in RL to be $\epsilon$ though.
-   See paper for example claims.

. . .

-   Reachability claims are fed to \K{} prover as normal \K{} rules.
-   Functional correctness directly specifiable as set reachability claims.
-   Correctness bugs often lead to security bugs.

[^inthiscaseK]: In this case, we use \K{} to specify the operational semantics.

Reachability Logic Inference System [@stefanescu-ciobaca-mereuta-moore-serbanuta-rosu-2014-rta]
-----------------------------------------------------------------------------------------------

![RL Inference System](media/images/proof-system.png)

Case Study: ERC20
-----------------

-   "Hello world" of Ethereum smart contracts.
-   First full contract we verified.
-   Key-value store of addresses to token balances.
-   Simple methods for purchasing/transferring/selling tokens.

. . .

### ERC20 Uses

-   Codify ownership distribution of a company (tokenizing equity).
-   Tokenize pink-slips/deeds (eg. tokenizing houses, cars).
-   Ponzi schemes.

Case Study: ERC20 - Scaling Verification
----------------------------------------

-   First ERC20 verification took several person-months.

. . .

-   Define state abstractions directly in \K{} itself.
    -   `nthbyteof` for storing symbolic word (256-bits) as 32 bytes (when written to `localMem`).
    -   `#abiCallData` allows using actual function name/signature in call instead of packed bytes representation.

. . .

-   Modular specifications
    -   Re-use same specs for different implementations, only need delta.
    -   Have 5 verified implementations of ERC20, all different behaviors.[^verifiedSmartContracts]

. . .

-   Now, can verify a (reasonable) ERC20 in about a day.

[^verifiedSmartContracts]: See our audited ERC20s (and other contracts) at <https://github.com/runtimeverification/verified-smart-contracts>.

Tool-Assisted Security Audits
-----------------------------

-   Runtime Verification, Inc. offers audits as a service, typical process:
    1.  Specify high-level business logic in English, confirm with customer.[^usuallyNotDone]
    2.  Refine to a mathematical definition, confirm with customer.
    3.  Refine to a set of K Reachability Claims, confirm with customer.
    4.  Fix bugs in contract and specification until the K prover is satisfied.
    5.  Send all documents generated and list of issues found to customer.

-   Independent groups also using KEVM to verify contract stack (eg. [DappHub](https://github.com/kframework/dapphub)).

[^usuallyNotDone]: Surprisingly, many smart contract developers don't have a high-level specification of their contracts.

Thanks!
=======

Conclusion
----------

-   \K{} used to specify semantics of Ethereum Virtual Machine (EVM).
-   Commercial verification efforts carried out with \K{} prover.

Sponsors
--------

The work presented in this paper was supported in part by
the Boeing grant on "Formal Analysis Tools for Cyber Security" 2016-2017,
the NSF grants CCF-1318191, CCF-1421575, CNS-1330599, CNS-1514163, and IIP-1660186,
the NSF Graduate Fellowship under Grant No. DGE-1650441,
an IOHK gift,
and a grant from the Ethereum Foundation.
