EVM Modeling
============

In this repository we provide a model of the EVM in K.

`evm.md`:
:   Top-level semantics file. Ties together the execution of the virtual machine
    and the world-state.

`world-state.md`:
:   Specifies the data-structures for the world state, which maintains the
    current pool of accounts and transactions.

`execution.md`:
:   Specifies how execution of the underlying stack machine works. Also provides
    the calculation of gas consumption for each opcode.

`data.md`:
:   Specifies the basic data of EVM, including the 256 bit words and all
    the opcodes. Some opcodes (which don't need information from
    the environment) are immediately desugared into more primitive operations.
