EVM Modeling
============

[ ![Codeship Status for kframework/evm-semantics](https://app.codeship.com/projects/d3ce9a40-343d-0135-d1d4-02553a1f9242/status?branch=master)](https://app.codeship.com/projects/226792)

In this repository we provide a model of the EVM in K.

-   [ethereum.md](ethereum.md): Driver for semantics of EVM (for loading tests, running simulations).
-   [evm.md](evm.md): Top level EVM semantics file (including local execution and network dynamics).
-   [evm-dasm.md](evm-dasm.md): Dissasembler (and assembler!) for EVM so that JSON test files can be read directly.
-   [data.md](data.md): Specifies the basic data of EVM execution, including the 256 bit words and some datastructures over them.

Unfinished
----------

### Network vs. EVM

Ethereum state consists of two parts, the network state and the EVM execution state.
Right now the semantics declares the configuration for both of these components together, and many rules reach between these two subconfigurations.
Separating the two subconfigurations and declaring an API for the network dynamics would provide a better understanding of the "necessary ingredients" for a consensus-driven distributed store.
This would also allow us to experiment with alternative programming languages to EVM for future blockchain systems.

### `CREATE`

Right now the opcode `CREATE` has not been given any semantics.
It probably should be given some.

### Gas Semantics

Right now the gas calculation is not in good shape.
Someone should shape it up.
It's at the end of the [EVM semantics file](evm.md).

### Disassembler/Assembler

We ran across an EVM program that has "junk" bytes in it.
We're not sure if it's considered a valid EVM program, but it seems plausible that putting extra data directly into the program for immutability would be good.
The disassembler/assembler doesn't account for this, but should.

### TODOs

More local problems are defined with a small *TODO* next to them.

Comments on EVM
===============

EVM is an assembly-ish byte-code language [@yellowpaper].
This emulates how current computer hardware works now, which makes it easier to "play" with the gas mechanic to reflect advances and difficulties in hardware.
It also discourages innovation to support more advanced languages directly in hardware, and provides a blueprint of how to build hardware that runs it efficiently.
EVM is deterministic, meaning that verifying a "solution" to a program (the final state) is as difficult as finding the "solution" (in both cases you just execute the program).

Program Representation
----------------------

Programs in EVM are byte-arrays; each byte has a mnemonic to make it easier to discuss and visualize EVM programs.
This means that an EVM program can be used as a piece of data, and the opcodes `*CODECOPY` will copy a specified portion of a program into local memory.
In our semantics, this means we must have an assembler around to pack our representation of programs back into a byte-array.
This packing process hinders abstractions, and it seems to be unnecessary.

Allowing the program to be represented as data means that any abstraction of the language must maintain a map back to the original program so that it can reason about it.
For example, say we wanted to reason directly over the control-flow graph of an EVM program where basic-blocks were summarized directly as their updates to the state.
We would need to maintain a copy of the actual original program; even though that data has nothing to do with the control-flow based summary of the program.

Deterministic vs. Nondeterministic (and Proof of Work)
------------------------------------------------------

Because EVM is deterministic, it takes as long to verify a computation as it takes to run a computation.
In both cases, the entire program must be executed; there is no choice about what the next step to take is.

In a nondeterministic language, execution is finding one execution path among many which "solves" the program.
For example, any logical language where there are several possible next inference steps is nondeterministic (eg. Prolog, Maude, K, Coq).
However, once a solution is found, presenting it is telling which choices were made at each nondeterministic step; verifying it is following that same sequence of steps.
If at each step there are a choice from $M$ inference rules, and it takes $n$ steps to reach a solution, then the speedup in verifying is $M^n$.

One of the goals in a consensus-driven distributed store is scalability, which means as more resources are added to the network the network gets stronger.
Using a deterministic language means that we lose at least one dimension of this scalability; everyone verifying the state of the world must do as much work as it took to compute the state of the world.
Even many functional languages, by having evaluation strategies settled ahead of time, are deterministic (though they may have elegant ways of encoding nondeterministic systems).

On the other hand, what secures many of these blockchain-consensus systems is proof of work.
Proof of work is the ultimate non-deterministic programming language; the programs are the block (before adding the nonce), and the solutions are the nonce added to the block so that it hashes low enough.
When using a nonce of size $2^N$, there are exactly $M = 2^N$ next "inference steps", and they all must be searched uniformly to find a solution ($n = 1$).
If instead the underlying programming language had some nondeterminism, some of the proof of work could be done **just by executing the transactions going into the block**.
Perhaps the two can be used to augment each other, allowing for some of the proof of work to be provided via finding a solution to the program and the rest via hashing.

If such a system were implemented, it may be important to incentivize miners to supply solutions to programs/proofs on the blockchain.
Perhaps a system where the time between when a specification/theorem is submitted to the blockchain and when it is solved determines the reward for the computation could be used.
Natural incentive to place proofs of theorems on the blockchain would be provided in the form of the reward; this means it's against the miners interests to ignore transactions.
The hard part is incentivizing placing theorems on the blockchain early (as it may be adventageous to hoard theorems so that you can submit solutions early to collect the reward).

Termination
-----------

The gas mechanic in EVM is designed to ensure that every program terminates so that users can't DOS the miners by submitting infinite computations.
However, there is no such guarantee that the proof of work computation done by miners terminates; there may be no combination of ordering of transactions and a nonce that yields a solution (though this is incredibly improbable).
Instead, we can leave it up to the miner to decide if pursuing a computation is worth the time lost in the pursuit.
Indeed, this directly increases the amount of work possible behind a proof of work, as much more useless work has been added to the system (via computations that don't terminate).

In many sufficiently powerful nondeterministic languages, there will be plenty of execution search paths which do not terminate.
However, automated provers (execution engines) for these languages don't throw up their hands, instead they design better search tactics for the language.
It's not clear that leaving the burden of which transactions to attempt to the miner is entirely bad, especially when coupled with a system which rewards more for longer-standing transactions.

Language Independence
---------------------

Language independence is difficult to achieve in a distributed system because everyone must agree on how programs are to be executed.
Two approaches are the **language-building language** approach and the **consensus-based** approach.

In the language-building language approach, the underlying language of the blockchain is a language-building language.
Thus, contracts are free to introduce new languages simply as specifications (programs) in the underlying language, and other contracts may use those languages by referring to the language definition contract.

The consensus-based approach is more flexible in the interpretation of "correct" executions of programs.
Essentially, everyone would vote on which execution is correct by rejecting ill-formed blocks (ill-formed here includes blocks which do not report a correct execution).
This lets the definition of the underlying languages evolve out of band; major changes to the semantics would essentially require widespread network agreement or a fork.
Indeed, the only thing that should be stored on the blockchain would be a hash of the program.

These two techniques could be combined.

Logical Frameworks
------------------

Logical frameworks provide both **language independence** and **nondeterminism**.
Because logical frameworks are designed to have many other logics and languages map into them, it is easy to both specify other programming languages and programs in other languages directly.
In addition, because they are logics themselves, logical frameworks will have a nondeterministic calculus based on selecting from a pool of inference rules.
As such, they are suitable for a proof of work based consensus-driven distributed computer.

Resources
=========

-   [EVM Yellowpaper](???): Original specification of EVM.
-   [Logical Frameworks](???): Discussion of logical frameworks.
