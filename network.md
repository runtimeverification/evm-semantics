Network State
=============

This file represents all the network state present in the EVM.
It will incrementally build up to supporting the entire [EVM-C API].

```k
requires "data.k"

module NETWORK
```

Status Codes
------------

These codes are used to signal the client about how the VM ended execution.

-   `EVM_SUCCESS` indicates successful end of execution.
-   `EVM_FAILURE` is a catch-all for generic execution failure.
-   `EVM_INVALID_INSTRUCTION` indicates reaching the designated `INVALID` opcode.
-   `EVM_UNDEFINED_INSTRUCTION` indicates that an undefined opcode has been reached.
-   `EVM_OUT_OF_GAS` indicates that execution exhausted the gas supply.
-   `EVM_BAD_JUMP_DESTINATION` indicates a `JUMP*` to a non-`JUMPDEST` location.
-   `EVM_STACK_OVERFLOW` indicates pushing more than 1024 elements onto the wordstack.
-   `EVM_STACK_UNDERFLOW` indicates popping elements off an empty wordstack.
-   `EVM_INVALID_MEMORY_ACCESS` indicates that a bad memory access occured.
    This can happen when accessing local memory with `CODECOPY*` or `CALLDATACOPY`, or when accessing return data with `RETURNDATACOPY`.
-   `EVM_REVERT` indicates that the contract called `REVERT`.
-   `EVM_STATIC_MODE_ERROR` indicates that a `STATICCALL` tried to change state.
    **TODO:** Avoid `_ERROR` suffix that suggests fatal error.
-   `EVM_REJECTED` indicates malformed or wrong-version EVM bytecode.
-   `EVM_INTERNAL_ERROR` indicates some other error that is unrecoverable but not due to the bytecode.

```k
    syntax StatusCode ::= "EVM_SUCCESS"
                        | "EVM_FAILURE"
                        | "EVM_INVALID_INSTRUCTION"
                        | "EVM_UNDEFINED_INSTRUCTION"
                        | "EVM_OUT_OF_GAS"
                        | "EVM_BAD_JUMP_DESTINATION"
                        | "EVM_STACK_OVERFLOW"
                        | "EVM_STACK_UNDERFLOW"
                        | "EVM_INVALID_MEMORY_ACCESS"
                        | "EVM_REVERT"
                        | "EVM_STATIC_MODE_ERROR"
                        | "EVM_REJECTED"
                        | "EVM_INTERNAL_ERROR"
```

The following are status codes used to report network state failures to the EVM from the client.
These are not present in the [EVM-C API].

-   `CLIENT_ACCOUNT_ALREADY_EXISTS` indicates that a newly created account already exists.
-   `CLIENT_BALANCE_UNDERFLOW` indicates an attempt to create an account which already exists.

```k
    syntax StatusCode ::= "CLIENT_ACCOUNT_ALREADY_EXISTS"
                        | "CLIENT_BALANCE_UNDERFLOW"
endmodule
```

Resources
=========

[EVM-C API]: <https://github.com/ethereum/evmjit/tree/master/include/evm.h>
