EVM Modeling
============

In this repository we provide a model of the EVM in K.

-   `evm.md`: Top-level semantics file. Ties together the execution of the
    virtual machine and the world-state.

-   `world-state.md`: Specifies the data-structures for the world state, which
    maintains the current pool of accounts and transactions.

-   `execution.md`: Specifies how execution of the underlying stack
    machine works. Also provides the calculation of gas consumption for
    each opcode.

-   `data.md`: Specifies the basic data of EVM, including the 256 bit words and
    all the opcodes. Some opcodes (which don't need information from
    the environment) are immediately desugared into more primitive operations.

Unfinished
==========

Here is a list of unfinished work on the semantics (grouped by which file I
suppose the finished work should belong in).

Base Data `data.md`
-------------------

Several of the operators over `Word` are not fully defined. Most of these should
pose no challenge defining them, but a few (eg. `sha3`) we may want to avoid
defining altogether. With `sha3`, the only property about it that should matter
is that it is "injective-ish".

-   `signextend : Word Word -> Word`
-   `bitwisenot : Word -> Word`
-   `signextend : Word Word -> Word`
-   `bitwisenot : Word -> Word`
-   `sdiv       : Word Word -> Word`
-   `smod       : Word Word -> Word`
-   `slt        : Word Word -> Word`
-   `sgt        : Word Word -> Word`
-   `bitwiseand : Word Word -> Word`
-   `bitwiseor  : Word Word -> Word`
-   `bitwisexor : Word Word -> Word`
-   `getbyte    : Word Word -> Word`
-   `sha3       : Word Word -> Word`

Additionally, instead of leaving opcodes in their word form (assembled), I've
chosen to dissasemble them and write the semantics over the dissasembled
version. I'm not sure right now, but it seems that there are many places where
the actual packed representation of the opcodes in memory is important. Will we
need to provide a converter back to the packed form for this functionality?

Local Execution `execution.md`
------------------------------

The `EVM-EXECUTION` module is fairly straightforward, it just shuffles data
around to supply the arguments to each of the operators that is executed. It
also uses the gas calculator to account for used gas at each execution step.

I have not handled the `LOG` operations yet. I'm not sure if their effect should
be recorded in the local-execution state of the machine or somewhere higher up.

The gas calculation is mostly correct, except for some issues that I've made
note of here. Either the data is not fully available at this point (in the local
execution state), or they require auxiliary functions which I haven't
implemented yet.

```k
    rule #gas(SSTORE)       => #gasSSTORE                                           // INCORRECT
    rule #gas(EXP)          => Gexp                                                 // INCORRECT
    rule #gas(OP)           => Gverylow +Word Gcopy          requires OP in Wcopy   // INCORRECT
    rule #gas(EXTCODECOPY)  => Gextcode +Word Gcopy                                 // INCORRECT
    rule #gas(LOG(N))       => Glog +Word (N *Word Glogdata)                        // INCORRECT
    rule #gas(OP)           => #gasCALL                      requires OP in Wcall   // INCORRECT
    rule #gas(SELFDESTRUCT) => #gasSELFDESTRUCT                                     // INCORRECT
    rule #gas(SHA3)         => Gsha3                                                // INCORRECT
```

Additionally, `Wverylow` has `PUSH(N) ; DUP(N) ; SWAP(N) ; ...` in it, but they
will not be matched by the pattern `OP in Wverylow` which is used in the
requires clause to figure out if `Wverylow` is matched. Right now I'm just
thinking of adding an extra three cases directly to the rules for these
operators specifically.

World State `world-state.md`
----------------------------

The world-state file is fairly simple. I think that much of the `EVM-UTIL`
module should be moved over into this file directly. Additionally, I would like
to see the world-state as its own language which exports an API of "system
calls". Then EVM would just be a language which occasionally executes those
system calls. See section "Comments on EVM" below.

EVM `evm.md`
------------

The module `EVM-UTIL` should be moved over to `world-state.md` (as mentioned
above).

Ideas
=====

These are some ideas I've had about EVM while developing the semantics. I'll try
to update this regularly to reflect new understanding/new research ideas.

Comments on EVM
---------------

EVM has two sub-states (shown by the `world-state.md` and the `execution.md`
files). The way we've setup the semantics here, there are some primitive
operations you can do to the world-state (eg. updating the storage of an
account, adding an account, etc...) , and you access those primitive operations
via the stack-machine language.

Right now all of the gas calculation happens over the primitive stack-machine
operations, but if it happened over the primitive world-state operations instead
then the world-state would be language independent. You could define whatever
execution language you wanted, and by hooking it up to the "system calls" which
modify the world state you would have it operate over the shared state that the
network uses.

What I would suggest to explore this idea more is to flesh out the necessary
"system calls" for updating the world state. I suspect once the semantics are
finished there will only be ~20 of them. These could be taken as the primitive
language that the current stack machine is compiled to. A new execution language
(or Serpent/Solidity/Plutus) would just have to provide a compiler to these
primitive operations. This would be nice because the current Ethereum world
state could be used as a genesis for a more flexible machine based on the more
primitive operations.

Language Simplification
-----------------------

If we were to make another simple stack language, it should be noted that EVM
has way too many opcodes (because many fewer would suffice to make a
Turing-complete language).

Alternatively, we could abandon the stack machine idea altogether. With the
stack machine, it's easy to show that all computations terminate because they
all cost gas and there is a finite amount of gas (or they cost zero gas but can
only be executed once).

However, if you defined *any* language you wanted in K (including a functional
language, logical language, etc...), you could go to each rule in the definition
and attach a gas cost to it. If there are rules you don't want to provide a gas
cost to, you could do a proof that those rules can only fire a finite number of
times before one of the rules with a gas cost must fire.

Fixed Width
-----------

Fixed width integer reasoning is hard (or at least harder). Perhaps this can be
dropped? Gas calculation would have to take into account the extra storage
requirements, which would make it difficult.

Proof of Work
-------------

I'm not as experienced in this realm, but it seems to me that the proof-of-work
scheme could be improved to do more useful work. Here are some ideas I've had
about that (admittedly not very fleshed out).

The property that SHA256 has is that it's hard to find a solution, but easy to
verify a solution once one is found. The same is (supposedly) true for NP
problems, or in general for proving things. So as a first-cut, people could
submit theorems (perhaps Coq theorems) with their transaction. When a miner
mines a block, they have to provide a proof-script containing only previously
defined tactics (from older blocks) of each theorem they mine. The proofs are
easily verified by a mechanical Coq proof-checker. (Coq is used here for
demonstrative purposes, pick your favorite logic/calculus with a mechanized
checker).

If you just want to send money (and not have to worry about "that proving stuff
nonsense"), just submit the theorem `true` and a miner can submit a trivial
proof of it to mine the block.

One nice thing about the idea is that now a mathematician can become a miner
(not just computers). They can try to prove something on paper first, once they
are convinced they have a proof they have to formalize it in the chosen
logic/calculus, then they'll *know* if it's actually a proof or not (and get
rewarded if it is).

It would be nice if there was some mechanism for agreeing on how difficult a
theorem is, and therefore on how much a miner should be rewarded for the
theorem. Perhaps something like "the longer it takes for someone to submit a
proof, the higher the reward for that proof is". What I can't figure out is how
to incentevize placing theorems on the blockchain early. (Placing proofs on the
chain early is incentevized by the reward for submitting a proof).
