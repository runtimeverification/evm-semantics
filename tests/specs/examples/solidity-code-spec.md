Solidity Verification Example
=============================

```k
requires "edsl.md"
requires "optimizations.md"
requires "lemmas/lemmas.k"
```

Solidity Code
-------------

File `test.sol` contains some code snippets we want to verify the functional correctness of:

```sol
pragma solidity =0.6.7;

contract Test {
    function add(uint256 a, uint256 b) external pure returns (uint256) {
        uint256 c = a + b;
        require(c >= a);
        return c;
    }

    function badAdd(uint256 a, uint256 b) external pure returns (uint256) {
        uint256 c = a + b;
        return c;
    }

    function max(uint256 a, uint256 b) external pure returns (uint256) {
        if (a < b) {
            return b;
        }
        return a;
    }
}
```

Run `solc test.sol --bin-runtime`:

```evm
======= tests/specs/examples/test.sol:Test =======
Binary of the runtime part:
608060405234801561001057600080fd5b50600436106100415760003560e01c80636d5433e614610046578063771602f7146100925780638b9732a9146100de575b600080fd5b61007c6004803603604081101561005c57600080fd5b81019080803590602001909291908035906020019092919050505061012a565b6040518082815260200191505060405180910390f35b6100c8600480360360408110156100a857600080fd5b810190808035906020019092919080359060200190929190505050610146565b6040518082815260200191505060405180910390f35b610114600480360360408110156100f457600080fd5b810190808035906020019092919080359060200190929190505050610165565b6040518082815260200191505060405180910390f35b60008183101561013c57819050610140565b8290505b92915050565b60008082840190508381101561015b57600080fd5b8091505092915050565b6000808284019050809150509291505056fea26469706673582212209559057d4829a2bd8b086d1af32f7f49152dfbebda288916bb69b51644a37bbe64736f6c63430006070033
```

Verification Module
-------------------

Helper module for verification tasks.

-   Define `#binRuntime()` as the compiled bytecode.
-   Add any lemmas needed for our proofs.
-   Import a large body of existing lemmas from KEVM.

```k
module VERIFICATION
    imports EDSL
    imports LEMMAS
    imports EVM-OPTIMIZATIONS

    rule #getValue(#uint256(X)) => X requires #rangeUInt(256, X) [simplification]

    rule X <=Int chop(X +Int Y) => false
      requires #rangeUInt(256, X)
       andBool #rangeUInt(256, Y)
       andBool notBool #rangeUInt(256, X +Int Y)
      [simplification]

    syntax Bytes ::= #binRuntime() [macro]
 // --------------------------------------
    rule #binRuntime() => #parseByteStack("0x608060405234801561001057600080fd5b50600436106100415760003560e01c80636d5433e614610046578063771602f7146100925780638b9732a9146100de575b600080fd5b61007c6004803603604081101561005c57600080fd5b81019080803590602001909291908035906020019092919050505061012a565b6040518082815260200191505060405180910390f35b6100c8600480360360408110156100a857600080fd5b810190808035906020019092919080359060200190929190505050610146565b6040518082815260200191505060405180910390f35b610114600480360360408110156100f457600080fd5b810190808035906020019092919080359060200190929190505050610165565b6040518082815260200191505060405180910390f35b60008183101561013c57819050610140565b8290505b92915050565b60008082840190508381101561015b57600080fd5b8091505092915050565b6000808284019050809150509291505056fea26469706673582212209559057d4829a2bd8b086d1af32f7f49152dfbebda288916bb69b51644a37bbe64736f6c63430006070033")

endmodule
```

K Specifications
----------------

Formal specifications (using KEVM) of the correctness properties for our Solidity code.

```k
module SOLIDITY-CODE-SPEC
    imports VERIFICATION
```

### Call with wrong call-data

-   Everything from `<mode>` to `<callValue>` is boilerplate.
-   We are setting `<callData>` to `add()`, which is not a signature that exists in the Solidity code.
-   We ask the prover to show that in all cases, we will end in `EVMC_REVERT` (rollback) when this happens.
-   This type of proof can be used to prevent some fallback function exploits.

```k
    claim [bad-call-data]:
          <mode>     NORMAL   </mode>
          <schedule> ISTANBUL </schedule>

          <callStack> .List                                 </callStack>
          <program>   #binRuntime()                         </program>
          <jumpDests> #computeValidJumpDests(#binRuntime()) </jumpDests>

          <localMem>   .Bytes     => ?_ </localMem>
          <memoryUsed> 0           => ?_ </memoryUsed>
          <wordStack>  .WordStack  => ?_ </wordStack>
          <pc>         0           => ?_ </pc>
          <gas>        #gas(_VGAS) => ?_ </gas>
          <callValue>  _CALL_VALUE => ?_ </callValue>

          <callData> #abiCallData("add", .TypedArgs) </callData>
          <k>          #execute => #halt ...   </k>
          <output>     .Bytes   => ?_          </output>
          <statusCode> _        => EVMC_REVERT </statusCode>
```

### Add Positive Case

-   `<callData>` says we are calling `add(X, Y)`.
-   `<output>` says we expect the function to return `X +Int Y` (addition did not overflow).
-   `<statusCode>` says we expect the function to exit normally.
-   `requires` says that we only expect this to happen if `0 <=Int X +Int Y <Int 2 ^Int 256` (no overflow).

```k
    claim [add-positive]:
          <mode>     NORMAL   </mode>
          <schedule> ISTANBUL </schedule>

          <callStack> .List                                 </callStack>
          <program>   #binRuntime()                         </program>
          <jumpDests> #computeValidJumpDests(#binRuntime()) </jumpDests>

          <localMem>   .Bytes     => ?_ </localMem>
          <memoryUsed> 0           => ?_ </memoryUsed>
          <wordStack>  .WordStack  => ?_ </wordStack>
          <pc>         0           => ?_ </pc>
          <gas>        #gas(_VGAS) => ?_ </gas>
          <callValue>  0           => ?_ </callValue>

          <callData> #abiCallData("add", #uint256(X), #uint256(Y)) </callData>
          <k>          #execute => #halt ...          </k>
          <output>     .Bytes   => #buf(32, X +Int Y) </output>
          <statusCode> _        => EVMC_SUCCESS       </statusCode>

     requires #rangeUInt(256, X)
      andBool #rangeUInt(256, Y)
      andBool #rangeUInt(256, X +Int Y)
```

### Add Negative Case

-   `<callData>` says we are calling `add(X, Y)`.
-   `<output>` says we don't care what the function outputs.
-   `<statusCode>` says we expect the function to exit in `REVERT` (state rollback).
-   `requires` says that we only expect this to happen if `notBool (0 <=Int X +Int Y <Int 2 ^Int 256)` (overflow occurs).
-   Note that `add-positive` and `add-negative` should cover _all_ cases for `add(X, Y)`.

```k
    claim [add-negative]:
          <mode>     NORMAL   </mode>
          <schedule> ISTANBUL </schedule>

          <callStack> .List                                 </callStack>
          <program>   #binRuntime()                         </program>
          <jumpDests> #computeValidJumpDests(#binRuntime()) </jumpDests>

          <localMem>   .Bytes     => ?_ </localMem>
          <memoryUsed> 0           => ?_ </memoryUsed>
          <wordStack>  .WordStack  => ?_ </wordStack>
          <pc>         0           => ?_ </pc>
          <gas>        #gas(_VGAS) => ?_ </gas>
          <callValue>  0           => ?_ </callValue>

          <callData> #abiCallData("add", #uint256(X), #uint256(Y)) </callData>
          <k>          #execute => #halt ...   </k>
          <output>     .Bytes   => ?_          </output>
          <statusCode> _        => EVMC_REVERT </statusCode>

     requires #rangeUInt(256, X)
      andBool #rangeUInt(256, Y)
      andBool notBool #rangeUInt(256, X +Int Y)
```

### Bad Add Failing Negative Case

-   `<callData>` says we are calling `badAdd(X, Y)`.
-   `<output>` says we don't care what the function returns.
-   `<statusCode>` says we expect the function to exit in `REVERT` (state rollback).
-   `requires` says that we only expect this to happen if `notBool (0 <=Int X +Int Y <Int 2 ^Int 256)` (overflow occurs).
-   This proof _fails_, because the function `badAdd` fails to call `REVERT` on overflow.

```
    claim [badAdd-negative]:
          <mode>     NORMAL   </mode>
          <schedule> ISTANBUL </schedule>

          <callStack> .List                                 </callStack>
          <program>   #binRuntime()                         </program>
          <jumpDests> #computeValidJumpDests(#binRuntime()) </jumpDests>

          <localMem>   .Bytes     => ?_ </localMem>
          <memoryUsed> 0           => ?_ </memoryUsed>
          <wordStack>  .WordStack  => ?_ </wordStack>
          <pc>         0           => ?_ </pc>
          <gas>        #gas(_VGAS) => ?_ </gas>
          <callValue>  0           => ?_ </callValue>

          <callData> #abiCallData("badAdd", #uint256(X), #uint256(Y)) </callData>
          <k>          #execute => #halt ...          </k>
          <output>     .Bytes   => ?_                 </output>
          <statusCode> _        => EVMC_REVERT        </statusCode>

     requires #rangeUInt(256, X)
      andBool #rangeUInt(256, Y)
      andBool notBool #rangeUInt(256, X +Int Y)
```

### Max Positive Case

-   `<callData>` says we are calling `max(X, Y)`.
-   `<output>` says we want the function to return the maximum of `X` and `Y`.
-   `<statusCode>` says we expect the function to exit normally (no `REVERT`).
-   Note that here the prover must consider two branches (for the `if ...` statement in the Solidity code).

```k
    claim [max-positive]:
          <mode>     NORMAL   </mode>
          <schedule> ISTANBUL </schedule>

          <callStack> .List                                 </callStack>
          <program>   #binRuntime()                         </program>
          <jumpDests> #computeValidJumpDests(#binRuntime()) </jumpDests>

          <localMem>   .Bytes     => ?_ </localMem>
          <memoryUsed> 0           => ?_ </memoryUsed>
          <wordStack>  .WordStack  => ?_ </wordStack>
          <pc>         0           => ?_ </pc>
          <gas>        #gas(_VGAS) => ?_ </gas>
          <callValue>  0           => ?_ </callValue>

          <callData> #abiCallData("max", #uint256(X), #uint256(Y)) </callData>
          <k>          #execute => #halt ...              </k>
          <output>     .Bytes   => #buf(32, maxInt(X, Y)) </output>
          <statusCode> _        => EVMC_SUCCESS           </statusCode>

     requires #rangeUInt(256, X)
      andBool #rangeUInt(256, Y)
```

```k
endmodule
```
