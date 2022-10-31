EVM Design Issues
=================

The EVM was the first successful general-purpose distributed programmable blockchain platform, but that doesn't make it without fault.
There are several issues with both the specification of the EVM (in the Yellow Paper), and with the general design of the EVM.
Most of these issues are written from the perspective of someone trying to do formal verification of the EVM.

Issues with description of EVM
------------------------------

These can be ambiguities/confusing wording in the [Yellow Paper](https://github.com/ethereum/yellowpaper).

-   In section 9.4.2, exceptions are described as if they are all catchable before an opcode is executed.
    While you may be able to implement EVM in this way, it's not clear that it's best (you have to duplicate computation), and we also are pretty sure no implementation even does this (including the C++ one).
    Instead they throw exceptions when they happen and roll-back the state (which is what you would expect to happen).
    Our original implementation tried to do it the way the Yellow Paper described, and it made everything harder/slower.

-   Again in section 9.4.2, it specifies that "these are the only ways exceptions can happen when executing".
    This doesn't help with building implementations, because there is at least one other case that isn't described.
    For example, if the memory is overflown, then the existing semantics doesn't do anything.
    Should it throw an exception?

-   Some operators which access data of other accounts don't specify explicitly what to do if the other account doesn't exist.
    `EXTCODESIZE` and `EXTCODECOPY` examples, though strangely enough `BALANCE` does specify what to do.
    We think the community has reached agreement on this though, "non-existing accounts are empty accounts" or something along those lines.

-   What about contracts that have "junk bytes" in them?
    We've seen a contract with "junk bytes", and use cases of contracts with junk bytes do exist.
    For example, if you want to use some large chunk of data to be used in your contract but don't want to perform a sequences of `PUSH`, `CODECOPY` can be used to move the junk bytes into memory.

-   The description in Appendix H of the `CALLCODE` instruction describes it as like `CALL` except for the fourth argument to the Theta function.
    However, it does not mention that this change from `Mu_s[1]` to `I_a` also applies to the specification of `C_NEW`.

-   The description in Appendix H of the `DELEGATECALL` instruction describes the gas provided to the caller as equal to `Mu_s[0]`.
    However, this is clearly not the correct behavior, since `Mu_s[0]` is a user-provided value, and the user could set it equal to 2^256 - 1, leading to the user having an infinite amount of gas.
    It's clear from the test suite that the intended behavior is to use `Ccallgas` but with the value for the value transfer equal to 0.
    It also describes the exceptional condition of not enough balance in terms of `I_v`, but in fact no value transfer occurs so this condition should never occur.

Issues with design of EVM
-------------------------

More broadly, many features of the EVM seem to be poorly designed.
These can be issues from simple "why did they do it that way?" to "this makes doing formal reasoning about EVM harder".

-   Precompiled contracts: Why are there 4 precompiled contracts?
    Calls into address 1 - 4 result in a "precompiled" contract being called (most of them some sort of cryptographic function).
    There are plenty of opcodes free, we should just have those precompiled contracts be accessed through primitives (like how `SHA3` is done).
    Another (albeit unlikely problem) is that of address-space collisions.

-   The byte-aligned local memory makes reasoning about EVM programs much more difficult.
    Say, for instance, that you write two Words (256-bit) contiguously to local memory (which takes up addresses 0 - 64), then shift between them and read a word (say between addresses 16 - 48).
    If one of those words was symbolic, the resulting symbolic word is a mess of an expression involving the original words.
    Of course, in theory this is possible to reason about, but effectively this allows taking one symbolic value and turning it into 32 symbolic values.
    This makes symbolic execution much slower/more painful.
    Note also that attempting to use bit-vectors, where you have one symbolic boolean variable per bit, is currently infeasible with the existing SMT solvers like [Z3](https://github.com/Z3Prover/z3); while it works with 32-bit words in some program verifiers, it is disarmingly slow with 64-bit words and we failed to prove anything with 256-bit words.

-   Program representation is important in EVM (that is, you must be able to represent a program as a byte-array of opcodes).
    When doing program analysis/abstract verification, you ideally would be allowed to make transformations on the program representation (e.g., convert it to a control-flow graph) without having to maintain a translation back.
    Currently in EVM, the `*CODECOPY` opcodes allow regarding program pieces as data, meaning that a translation back must always be maintained, because using `CREATE` with `DELEGATECALL` allows executing arbitrary code.
    For this reason, we had to build a parser/unparser and an assembler/dissasembler into our semantics.
    Putting a symbolic value through the process of disassembling -> unparsing loses a lot of semantic information about the original value.
    While self-modifying code is nice and powerful in principle, we are not aware of any programming languages for the blockchain that encourage or even allow that.

-   In section H.2, the Yellow Paper states "All arithmetic is modulo 2^256 unless otherwise noted."
    Reasoning "modulo" is very complex with the current SMT provers and it was indeed a, if not the most major difficulty in our [EVM verification efforts](proofs).
    Additionally, the programs (smart contracts) we verified turned out to be wrong, in the sense that they showed unintended behavior, in the presence of arithmetic overflows anyway.
    That is, arithmetic overflows were not expected to happen by the developers, so adding code to deal with the "modulo 2^256" behavior in case of arithmetic overflow was not even considered.
    In such situations, it would be a lot better to simply throw an exception when arithmetic overflow occurs, thus indicating that something bad happened, than to default to "modulo 2^256" and ending up with a program computing wrong values.
    We conjecture that words of 256 bits should be long enough for the current smart contract needs to afford to abruptly terminate computations when the limit is reached.

Recommendations for the Future
------------------------------

In addition to the above mentioned issues, there are several things that could be improved about EVM in general as a distributed computation language.
Here we mention some.

### Deterministic vs. Nondeterministic (and Proof of Work and Scalability)

Because EVM is deterministic, it takes as long to verify a computation as it takes to run a computation.
In both cases, the entire program must be executed; there is no choice about what the next step to take is.

In a nondeterministic language, execution is finding one execution path among many which "solves" the program.
For example, any logical language where there are several possible next inference steps is nondeterministic (eg. Prolog, Maude, K, Coq).
However, once a solution is found, presenting it is telling which choices were made at each nondeterministic step; verifying it is following that same sequence of steps.
If at each step there are a choice from `M` inference rules, and it takes `n` steps to reach a solution, then the speedup in verifying is `M^n`.

One of the goals in a consensus-driven distributed store is scalability, which means as more resources are added to the network the network gets stronger.
Using a deterministic language means that we lose at least one dimension of this scalability; everyone verifying the state of the world must do as much work as it took to compute the state of the world.
Even many functional languages, by having evaluation strategies settled ahead of time, are deterministic (though they may have elegant ways of encoding nondeterministic systems).

On the other hand, what secures many of these blockchain-consensus systems is proof of work.
Proof of work is the ultimate non-deterministic programming language; the programs are the blocks (before adding the nonce), and the solutions are the nonce added to the blocks so that it hashes low enough.
When using a nonce of size `2^N`, there are exactly `M = 2^N` next "inference steps", and they all must be searched uniformly to find a solution.
If instead the underlying programming language had some nondeterminism, some of the proof of work could be done *just by executing the transactions going into the block*.
Perhaps the two can be used to augment each other, allowing for some of the proof of work to be provided via finding a solution to the program and the rest via hashing.

If such a system were implemented, it may be important to incentivize miners to supply solutions to programs/proofs on the blockchain.
Perhaps a system where the time between when a specification/theorem is submitted to the blockchain and when it is solved determines the reward for the computation could be used.
Natural incentive to place proofs of theorems on the blockchain would be provided in the form of the reward; this means it's against the miners interests to ignore transactions.
The hard part is incentivizing placing theorems on the blockchain early (as it may be advantageous to hoard theorems so that you can submit solutions early to collect the reward).

### Termination

The gas mechanic in EVM is designed to ensure that every program terminates so that users can't DOS the miners by submitting infinite computations.
However, there is no such guarantee that the proof of work computation done by miners terminates; there may be no combination of ordering of transactions and a nonce that yields a solution (though this is incredibly improbable).
Instead, we can leave it up to the miner to decide if pursuing a computation is worth the time lost in the pursuit.
Indeed, this directly increases the amount of work possible behind a proof of work, as much more useless work has been added to the system (via computations that don't terminate).

In many sufficiently powerful nondeterministic languages, there will be plenty of execution search paths which do not terminate.
However, automated provers (execution engines) for these languages don't throw up their hands, instead they design better search tactics for the language.
It's not clear that leaving the burden of which transactions to attempt to the miner is entirely bad, especially when coupled with a system which rewards more for longer-standing transactions.

The problem with this, it turns out, is not that users may DOS miners, but that miners may DOS other miners (by presenting blocks that they purport terminate).

### Language Independence

Language independence is difficult to achieve in a distributed system because everyone must agree on how programs are to be executed.
Two approaches are the *language-building language* approach and the *consensus-based* approach.

In the language-building language approach, the underlying language of the blockchain is a language-building language.
Thus, contracts are free to introduce new languages simply as specifications (programs) in the underlying language, and other contracts may use those languages by referring to the language definition contract.
As a very simple example, if the underlying language was K, then you could submit a contract that is just a K definition giving semantics to the language you want to use in the future.
Along this line, we should use a logical framework as the underlying language.
Logical frameworks exhibit both non-determinism and language independence, making two improvements to EVM at the same time.

The consensus-based approach is more flexible in the interpretation of "correct" executions of programs.
Essentially, everyone would vote on which execution is correct by rejecting ill-formed blocks (ill-formed here includes blocks which do not report a correct execution).
This lets the definition of the underlying languages evolve out of band; major changes to the semantics would essentially require widespread network agreement or a fork.
Indeed, the only thing that should be stored on the blockchain would be a hash of the program.

These two techniques could perhaps be combined.
