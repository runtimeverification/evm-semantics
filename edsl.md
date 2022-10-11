eDSL High-Level Notations
=========================

The eDSL high-level notations make the EVM specifications more succinct and closer to their high-level specifications.
The succinctness increases the readability, and the closeness helps "eye-ball validation" of the specification refinement.
The high-level notations are defined by translation to the corresponding EVM terms, and thus can be freely used with other EVM terms.
The notations are inspired by the production compilers of the smart contract languages like Solidity and Vyper, and their definition is derived by formalizing the corresponding translation made by the compilers.

```k
requires "buf.md"
requires "hashed-locations.md"
requires "abi.md"
requires "infinite-gas.md"
requires "optimizations.md"

module EDSL
    imports BUF
    imports HASHED-LOCATIONS
    imports SOLIDITY-FIELDS
    imports EVM-ABI
    imports EVM-OPTIMIZATIONS
    imports INFINITE-GAS
    imports BIN-RUNTIME
endmodule

module BIN-RUNTIME
    imports EVM-ABI

    syntax Contract
    syntax ByteArray ::= #binRuntime ( Contract ) [alias, klabel(binRuntime), symbol, function, no-evaluators]
 // ----------------------------------------------------------------------------------------------------------

endmodule
```
