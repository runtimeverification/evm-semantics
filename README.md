KEVM: Semantics of EVM in K
===========================

[ ![Codeship Status for kframework/evm-semantics](https://app.codeship.com/projects/d3ce9a40-343d-0135-d1d4-02553a1f9242/status?branch=master)](https://app.codeship.com/projects/226792)

In this repository we provide a model of the EVM in K.

### Technical Report

See [our technical report on KEVM 1.0](http://hdl.handle.net/2142/97207) for more expository explanation of KEVM.
The paper is a good starting point for people wishing to dive into reading the semantics/other tools here (especially sections 3 and 5).

### Structure

The file [data.md](data.md) explains the basic data of EVM (including the 256 bit words and some datastructures over them).
This data is defined functionally.

[evm.md](evm.md) is the file containing the semantics of KEVM.
This file contains the **configuration** (a map of the state), and a simple imperative execution machine which the EVM lives on top of.
It deals with the semantics of opcodes, the gas cost of execution, and parsing/unparsing/assembling/disassembling.

### Gas Analysis

We have defined one analysis tool so far; a *very very* simple gas analysis tool.
This gas analysis tool should *be improved* before being used for anything significant.
We will collect developed analysis tools in [analysis.md](analysis.md).

### Proofs

Any proofs we perform will be documented in [proofs/README.md].
These proofs are also run as tests of UIUC-K, though they take quite a while.
The file [verification.md](verification.md) contains some helper-macros for writing down reachability claims.

### Testing

[ethereum.md](ethereum.md) loads test-files from the [Ethereum Test Set](https://github.com/ethereum/tests) and executes them, checking that the output is correct.
If the output is correct, the entire configuration is cleared.
If any check fails, the configuration retains the failed check at the top of the `<k>` cell.

Using the Definition
--------------------

There are two versions of K available, [RV-K](https://github.com/runtimeverification/k) and [UIUC-K](https://github.com/kframework/k).
This repository contains the build-products for both versions of K (there are slight differences) in `.build/$K_VERSION/`.
Use RV-K for fast concrete execution, and UIUC-K for any symbolic reasoning.
Make sure that you have set the `K_VERSION` environment variable in your shell (add `export K_VERSION=uiuck` or `export K_VERSION=rvk` to your `.bashrc` or equivalent).

The script `Build` supplied in this repository will build and run the definition (see `./Build help` to see usage information).

-   To `kompile` the definition, run `./Build` or `./Build make-build`.
-   Use `./Build run <file>` and `./Build test <file>` to run/test a file, respectively.
-   To run the tests, do `./Build test-<test-list>` (`./Build partest-<test-list>` to run them in parallel using [GNU parallel](https://www.gnu.org/software/parallel/)).
    The output of `./Build help` contains the available `<test-list>`.

Running any proofs or symbolic reasoning requires UIUC-K.

To run in a different mode (eg. in `GASANALYZE` mode), do `export cMODE=<OTHER_MODE>` before calling `./Build`.
To run with a different fee schedule (eg. `HOMESTEAD` instead of `DEFAULT`), do `export cSCHEDULE=<OTHER_SCHEDULE>` before calling `./Build`.

### Dependencies

For using the `./Build` command and tests, we depend on `xmllint` (on Ubuntu via the package `libxml2-utils`).
For developing, we depend on [`pandoc-tangle`](https://github.com/ehildenb/pandoc-tangle).

### Interesting Branches

These branches (off of `master`) are various interesting/useful changes to the semantics.

-   `perf` and `performance` are changes which improve performance of concrete execution but cannot do symbolic reasoning.
-   `tutorial` removes parts of the semantics and places `TODO` markers for a user to fill in.

Contributing
------------

We do our development directly in the Markdown files and build the definition files (`*.k`) from them using [pandoc-tangle](https://github.com/ehildenb/pandoc-tangle).
Not everyone wants to install `pandoc-tangle` or `pandoc`, so the build products are kept in the repository for people who just want to experiment quickly.
Any changes back upstream must be made to both the Markdown and the build products with an eye to self-documenting literate programming.

Writing tests is **always** appreciated.
Tests can come in the form of proofs done over contracts too :).

Unfinished
----------

### Network vs. EVM

Ethereum state consists of two parts, the network state and the EVM execution state.
Right now the semantics declares the configuration for both of these components together, and many rules reach between these two subconfigurations.
Separating the two subconfigurations and declaring an API for the network dynamics would provide a better understanding of the "necessary ingredients" for a consensus-driven distributed store.
This would also allow us to experiment with alternative programming languages to EVM for future blockchain systems.

### Full Transaction Execution

Right now we are passing the VMTests, but haven't run tests on entire transactions.
To have confidence in our semantics, we need to run the tests involving entire transactions (not just chunks of VM code).
We are working on running the GeneralStateTests now as well.

### TODOs

More local problems are defined with a small *TODO* next to them in the semantics.

Resources
=========

-   [EVM Yellowpaper](https://github.com/ethereum/yellowpaper): Original specification of EVM.
-   [LEM Semantics of EVM](https://github.com/pirapira/eth-isabelle)
-   [Ethereum Test Set](https://github.com/ethereum/tests)

For more information about [The K Framework](http://kframework.org), refer to these sources:

-   [The K Tutorial](https://github.com/kframework/k/tree/master/k-distribution/tutorial)
-   [Semantics-Based Program Verifiers for All Languages](http://fsl.cs.illinois.edu/index.php/Semantics-Based_Program_Verifiers_for_All_Languages)
-   [Reachability Logic Resources](http://fsl.cs.illinois.edu/index.php/Reachability_Logic_in_K)
-   [Matching Logic Resources](http://fsl.cs.illinois.edu/index.php/Matching_Logic)
-   [Logical Frameworks](http://dl.acm.org/citation.cfm?id=208700): Discussion of logical frameworks.
