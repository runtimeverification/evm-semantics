Analysis of EVM Programs
========================

K allows analysis tools to be developed independently of the programming language.
This allows programming language experts to provide semantics to their languages and formal methods experts to provide the analysis tools independently.
This modular approach to formal analysis also ensures that the analysis tools are "kept honest", in that they cannot have special hard-coded hacks for each language.

Semantics-Based Program Verifier [@oopsla-2016].
------------------------------------------------

One particularly useful formal analysis tool developed for K is the Reachability Logic prover [@oopsla-2016].
This prover accepts as input a K definition and a set of reachability theorems to be proven.
It will then automatically attempt to prove the reachability theorems using the K definition.

A reachability theorem is of the form $\phi \reaches \psi$, where $\phi$ are $\psi$ are formulas in the static logic (in the case of K, a fragment of Matching Logic [@matching-logic]).
This states that every state in the set of states represented by the Matching Logic formula $\phi$ will either reach a state in $\psi$ or will not terminate.
Matching Logic allows representing code as data (algebraically), so the formula's $\phi$ and $\psi$ can contain code.
This means that a Hoare Logic triple $\{P\} C \{Q\}$ can be written as the reachability theorem $P \land C \reaches Q \land \eps$, where $\eps$ is the empty program.

In Hoare Logic, it's quite common that a loop invariant must be supplied to move the verification over looping behavior.
In Reachability Logic, this is generalized to a language indpendent notion called a "circularity".[^circularity]
As in Hoare Logic, the circularities must be supplied ahead of time (or inferred automatically, which our tool does not do yet).

[^circularity]: These are called circularities because they are directly related to application of the Circularity inference rule in Reachability Logic.

### Complexity Analysis

Many interesting properties can be formed as reachability queries, including functional correctness.
The query made is $\phi \land C \reaches \psi \land \eps$, which $C$ is the code to be executed (potentially containing symbolic values and subject to the constraint $\phi$), and $\psi$ is a formula stating "the correct answer was computed".
If it's proven using the Reachability Logic proof system, that means that any terminating execution of $C$ setup in initial state $\phi$ will eventually reach a state in $\psi$.

In K, tracking the complexity of a computation can be done by adding an extra cell to the configuration which increments each time the rule it's tracking is used.
As an example, we'll provide a rough sketch of tracking the number of integer multiplications in a definition.

-   First add a cell `numMults` to the configuration tracking the number of multiplications.

```{.k, .paper}
    configuration ...
                  <numMults> 0 </numMults>
                  ...
```

-   Modify the rule which calls the builtin multiplication `_*Int_` to increment the multiplication counter.

```{.k, .paper}
    rule <k> I:Int *IExp I':Int => I *Int I' ... </k>
         <numMults> N => N +Int 1 </numMults>
```

-   Prove the following reachability theorem (where `f` is the "multiplication complexity" you want to prove):

```{.k, .paper}
    rule <k> CODE => . </k>
         <numMults> N:Int => M:Int </numMults>
         ...
      requires M ==Int f(N)
```

Other complexity metricts can be tracked by adding to the associated rules (or weighing each associated rule and adding all the results in a single cell).

### EVM Gas Usage Analysis

In the EVM, we do have one specific quantity people are interested in tracking: the gas consumed during execution.
The semantics must already track the gas in the `gas` cell because it affects execution.
In addition, proving that no more than a certain amount of gas will be consumed during execution would allow for confidence that a contract won't fail due to running out of gas.

Here, we prove a reachability claim about the program `PUSH(1, 3) ; PUSH(1, 7) ; ADD ; .OpCodes`.
We have the pre-condition that the size of the word-stack is initially low enough that there will not be a stack overflow.
The post-condition states that no more than 9 gas is consumed executing these opcodes.
The cell `pc` ensures that we only consider the pre-condition in states before execution, and post-conditions in states after executing.

```{.k, .paper, .spec1}
module GAS-PROOF

    rule <k> #next => . </k>
         <gas> N => M </gas>
         <pc>  0 => 5 </pc>
         <program> #asMapOpCodes( PUSH(1, 3) ; PUSH(1, 7) ; ADD ; .OpCodes ) </program>
         <wordStack> WS </wordStack>
      requires (N -Int M) <=Int 9 andBool #sizeWordStack(WS) <Int 1020

endmodule
```

### Standard Token

???

Resources
---------

-   [Semantics-Based Program verifiers for All Languages](http://fsl.cs.illinois.edu/FSL/papers/2016/stefanescu-park-yuwen-li-rosu-2016-oopsla-public.pdf)
