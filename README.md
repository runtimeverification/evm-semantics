SEMANTICS OF EVM IN K
=====================

[ ![Codeship Status for kframework/evm-semantics](https://app.codeship.com/projects/d3ce9a40-343d-0135-d1d4-02553a1f9242/status?branch=master)](https://app.codeship.com/projects/226792)

In this repository we provide a model of the EVM in K.

-   [ethereum.md](ethereum.md): Driver for semantics of EVM (for loading tests, running simulations).
-   [evm.md](evm.md): Top level EVM semantics file (including local execution and network dynamics).
-   [data.md](data.md): Specifies the basic data of EVM execution, including the 256 bit words and some datastructures over them.

We are continuously testing our implementation against the [Ethereum Test Set](https://github.com/ethereum/tests).
The above marker only checks for a subset of the tests (those in [our codeship list](tests/passing.expected)), though many more of the tests than those listed there are passing.

Building and Running
--------------------

There are two versions of K available, [RV-K](https://github.com/runtimeverification/k) and [UIUC-K](https://github.com/kframework/k).
The files in `k/*.k` in this repository work with UIUC-K, so install that first.

The script `Build` supplied in this repository will build an run the definition (use `./Build help` to see usage information).
First `kompile` the definition with `./Build build`; to clone and split the tests run `make split-tests`.

To run JSON input (or JSON with our extended "pretty" syntax for input) in file `tests/VMTests/vmArithmeticTest/add0.json` for example (after splitting the tests):

```sh
$ ./Build build
...
$ make split-tests
...
$ krun --directory k/ --debug \
       -cMODE=NORMAL -cSCHEDULE=DEFAULT \
       tests/VMTests/vmArithmeticTest/add0.json
```

To run a gas analysis of the program, instead supply `-cMODE=GASANALYZE`.
To run with the Homestead fee schedule instead (or any of the other schedules), instead supply `-cSCHEDULE=HOMESTEAD`.


Verification
------------

Along with improving our semantics, we continue to use them to verify
smart contracts using K's verification infrastructure. We maintain a
[summary of our verification effors](tests/proofs/README.md).

Issues
------

We are curating a list of [things we wish were different about EVM](issues.md).

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

### TODOs

More local problems are defined with a small *TODO* next to them in the semantics.

Resources
=========

-   [EVM Yellowpaper](https://github.com/ethereum/yellowpaper): Original specification of EVM.
-   [Logical Frameworks](http://dl.acm.org/citation.cfm?id=208700): Discussion of logical frameworks.
-   [LEM Semantics of EVM](https://github.com/pirapira/eth-isabelle)

For more information about [The K Framework](http://kframework.org), refer to these sources:

-   [The K Tutorial](https://github.com/kframework/k/tree/master/k-distribution/tutorial)
-   [Semantics-Based Program Verifiers for All Languages](http://fsl.cs.illinois.edu/index.php/Semantics-Based_Program_Verifiers_for_All_Languages)
-   [Reachability Logic Resources](http://fsl.cs.illinois.edu/index.php/Reachability_Logic_in_K)
-   [Matching Logic Resources](http://fsl.cs.illinois.edu/index.php/Matching_Logic)
