Network State
=============

This file represents all the network state present in the EVM.
It will incrementally build up to supporting the entire [EVM-C API].

```k
module NETWORK
```

EVM Status Codes
----------------

### Exceptional Codes

The following codes all indicate that the VM ended execution with an exception, but give details about how.

-   `EVMC_FAILURE` is a catch-all for generic execution failure.
-   `EVMC_INVALID_INSTRUCTION` indicates reaching the designated `INVALID` opcode.
-   `EVMC_UNDEFINED_INSTRUCTION` indicates that an undefined opcode has been reached.
-   `EVMC_OUT_OF_GAS` indicates that execution exhausted the gas supply.
-   `EVMC_BAD_JUMP_DESTINATION` indicates a `JUMP*` to a non-`JUMPDEST` location.
-   `EVMC_STACK_OVERFLOW` indicates pushing more than 1024 elements onto the wordstack.
-   `EVMC_STACK_UNDERFLOW` indicates popping elements off an empty wordstack.
-   `EVMC_CALL_DEPTH_EXCEEDED` indicates that we have executed too deeply a nested sequence of `CALL*` or `CREATE` opcodes.
-   `EVMC_INVALID_MEMORY_ACCESS` indicates that a bad memory access occured.
    This can happen when accessing local memory with `CODECOPY*` or `CALLDATACOPY`, or when accessing return data with `RETURNDATACOPY`.
-   `EVMC_STATIC_MODE_VIOLATION` indicates that a `STATICCALL` tried to change state.
    **TODO:** Avoid `_ERROR` suffix that suggests fatal error.
-   `EVMC_PRECOMPILE_FAILURE` indicates an errors in the precompiled contracts (eg. invalid points handed to elliptic curve functions).

```k
    syntax String ::= StatusCode2String ( StatusCode ) [function, functional, hook(STRING.token2string)]
 // ----------------------------------------------------------------------------------------------------
    syntax ExceptionalStatusCode ::= "EVMC_FAILURE"               [token]
                                   | "EVMC_INVALID_INSTRUCTION"   [token]
                                   | "EVMC_UNDEFINED_INSTRUCTION" [token]
                                   | "EVMC_OUT_OF_GAS"            [token]
                                   | "EVMC_BAD_JUMP_DESTINATION"  [token]
                                   | "EVMC_STACK_OVERFLOW"        [token]
                                   | "EVMC_STACK_UNDERFLOW"       [token]
                                   | "EVMC_CALL_DEPTH_EXCEEDED"   [token]
                                   | "EVMC_INVALID_MEMORY_ACCESS" [token]
                                   | "EVMC_STATIC_MODE_VIOLATION" [token]
                                   | "EVMC_PRECOMPILE_FAILURE"    [token]
```

### Ending Codes

These additional status codes indicate that execution has ended in some non-exceptional way.

-   `EVMC_SUCCESS` indicates successful end of execution.
-   `EVMC_REVERT` indicates that the contract called `REVERT`.

```k
    syntax EndStatusCode ::= ExceptionalStatusCode
                           | "EVMC_SUCCESS" [token]
                           | "EVMC_REVERT"  [token]
```

### Other Codes

The following codes indicate other non-execution errors with the VM.

-   `EVMC_REJECTED` indicates malformed or wrong-version EVM bytecode.
-   `EVMC_INTERNAL_ERROR` indicates some other error that is unrecoverable but not due to the bytecode.
-   `.StatusCode` is an extra code added for "unset or unknown".

```k
    syntax StatusCode ::= EndStatusCode
                        | "EVMC_REJECTED"       [token]
                        | "EVMC_INTERNAL_ERROR" [token]
                        | ".StatusCode"         [token]
```

Client/Network Codes
--------------------

The following are status codes used to report network state failures to the EVM from the client.
These are not present in the [EVM-C API].

-   `EVMC_ACCOUNT_ALREADY_EXISTS` indicates that a newly created account already exists.
-   `EVMC_BALANCE_UNDERFLOW` indicates an attempt to create an account which already exists.

```k
    syntax ExceptionalStatusCode ::= "EVMC_ACCOUNT_ALREADY_EXISTS" [token]
                                   | "EVMC_BALANCE_UNDERFLOW"      [token]
```

```k
endmodule
```

Resources
=========

[EVM-C API]: <https://github.com/ethereum/evmjit/tree/master/include/evm.h>
