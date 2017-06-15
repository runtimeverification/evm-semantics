EVM Modeling
============

[ ![Codeship Status for kframework/evm-semantics](https://app.codeship.com/projects/d3ce9a40-343d-0135-d1d4-02553a1f9242/status?branch=master)](https://app.codeship.com/projects/226792)

In this repository we provide a model of the EVM in K.
The model is optimized for presentation purposes with the goal of separating the concerns of EVM's language and the world-state that execution of the EVM modifies.

`ethereum.md`:
:   Driver for semantics of EVM (for loading tests, running simulations).

`evm.md`:
:   Top level EVM semantics file (including local execution and network dynamics).

`evm-dasm.md`:
:   Dissasembler for EVM so that JSON test files can be read directly.

`data.md`:
:   Specifies the basic data of EVM execution, including the 256 bit words and some datastructures over them.

Unfinished
----------

Unfinished/incorrect portions of the semantics are labelled at the place where the problem is so that they stay actual.
Look for paragraph's beginning with "TODO:".

General Concerns
================

Program Representation
----------------------

EVM programs normally are represented in their hex form, and some operations depend on this representation of the program.
Instead, we've represented in their "pretty" word form (and provided a dissasembler).
For operations `CODECOPY` and `EXTCODECOPY`, we'll need to re-assemble the hex-form of the program.

Structure of Semantics
----------------------

Ideally the world-state semantics (account and transaction states) would be defined completely separately and export a simple API.
Right now it's tightly integrated with the EVM semantics.
The commands that would be affected by a switch are isolated to their own section in [the EVM file](evm.md).

Comments
========

These are some ideas about EVM (which we've had while developing the semantics).

EVM State
---------

EVM has two sub-states (the "world state" and the "VM execution state"). The way
we've setup the semantics here, there are some primitive operations you can do
to the world-state (eg. updating the storage of an account, adding an account,
etc...) , and you access those primitive operations via the stack-machine
language.

Right now all of the gas calculation happens over the EVM stack-machine
operations, but if it happened over the primitive world-state operations instead
then the world-state would be (more) language independent. You could define
whatever execution language you wanted, and by hooking it up to the "system
calls" which modify the world state you would have it operate over the shared
state that the network uses. If different cryptocurrencies had their own
language, but they agreed on the shared-state, it would be fairly simple to
"cross-compile" programs between them.

Other Languages
---------------

If we were to make another execution language, it should be noted that EVM is
way too complicated (mostly because it's an assembly-like language, which is
almost necessarily hard to reason about). One advantage to the structure is that
it's easy to prove that all programs terminate with the given gas scheme.

By defining the semantics of a programming language in K, it's easy to force the
language to terminate, making this advantage unnecessary. There are many
examples in the K tutorial of much nicer language definitions which allow for
much simpler reasoning and higher-level programming, any of them would do.

Representation Independence
---------------------------

Many of the operations in EVM are "representation dependent"; that is they
depend on some exact encoding of the data being worked over. For example, any
command which specifies the endian-ness of the data is representation dependent.
In addition, some operations allow using code as data and then the data can be
hashed or cut up into bytes, making the representation of the code important
(ie. we have to store it as a bunch of words instead of as a sum-type of the
command names). Another example is the fixed-width arithmetic which restricts
the integer representations that can be used.

Many of these things require extra work in the formal semantics because the most
convenient representation is not the one needed by the representation dependent
functions. This requires writing and reasoning about converters, or doing
everything over the chosen representation.

In many cases, removing the representation dependencies shouldn't be difficult.
But for things like Keccak, the representation is crucial. In addition, in the
case of fixed-width arithmetic, going to unbounded arithmetic would require a
more nuanced gas scheme to ensure someone isn't just encoding all of their
memory in a single integer.

It would be worth thinking about how to remove data and code representation dependencies in future coins.

Proof of Work
-------------

It seems to me that the proof-of-work scheme could be improved to do more useful work.

Instead of specifying programs, specify specifications. Then a miner must supply
programs that meet the specification, along with a proof that the program does
meet the specification. In the extreme case, the program meeting the
specification would just be the proof itself (eg. if you used Coq theorems as
your specifications and Coq proof-scripts as your programs).

Proof of work must have the property that it's hard to find a solution yet easy
to verify a solution once found. Most mechanical proof languages have this
property anyway, and it's already "tunable" by picking harder and easier
theorems to prove. Then inter-contract execution would just be using already
proven theorems on the blockchain to build bigger theorems (and thus bigger
programs).

If you only want to send money, you could just use the theorem `true`. If
someone wanted to place a bounty, they could write a theorem saying that if a
miner proves the theorem they get a reward (then even some mathematician with a
pencil/paper could contribute to mining). Or perhaps there could be some
mechanism which provides a miner with a larger reward for proving a theorem that
has been around longer.

Of course, this could all be encoded in a smart-contract on the EVM (for
example), but why not just start with a rich language for theorem proving where
the proofs correspond to code?
