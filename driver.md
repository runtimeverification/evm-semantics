Ethereum Simulations
====================

Ethereum is using the EVM to drive updates over the world state.
Actual execution of the EVM is defined in [the EVM file](../evm).

```k
requires "evm.md"
//requires "optimizations.md"
//requires "asm.md"
//requires "state-utils.md"

module ETHEREUM-SIMULATION
    imports EVM
    //imports EVM-OPTIMIZATIONS
    //imports EVM-ASSEMBLY
    //imports STATE-UTILS
```

An Ethereum simulation is a list of Ethereum commands.
Some Ethereum commands take an Ethereum specification (eg. for an account or transaction).

```k
    syntax EthereumSimulation ::= ".EthereumSimulation"
                                | EthereumCommand EthereumSimulation
 // ----------------------------------------------------------------
    syntax EthereumCommand    ::= "HACK1"
```

```k
    syntax Mode ::= "SUCCESS"
 // -------------------------
```

```k
endmodule
```
