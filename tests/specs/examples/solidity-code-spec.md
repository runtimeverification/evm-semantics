Solidity Verification Example
=============================

```k
requires "edsl.md"
requires "optimizations.md"
requires "lemmas/lemmas.k"
requires "lemmas/infinite-gas.k"
```

Solidity Code
-------------

File `test.sol`:

```sol
pragma solidity >=0.5.0;

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
}
```

Run `solc test.sol --bin-runtime`

```evm
======= tests/specs/examples/test.sol:Test =======
Binary of the runtime part:
6080604052348015600f57600080fd5b506004361060325760003560e01c8063771602f71460375780638b9732a9146080575b600080fd5b606a60048036036040811015604b57600080fd5b81019080803590602001909291908035906020019092919050505060c9565b6040518082815260200191505060405180910390f35b60b360048036036040811015609457600080fd5b81019080803590602001909291908035906020019092919050505060e7565b6040518082815260200191505060405180910390f35b60008082840190508381101560dd57600080fd5b8091505092915050565b6000808284019050809150509291505056fea2646970667358221220c666029b6b6de844da30183abbf37ea2865cdcb8a46ef623239384ca9c41de9864736f6c63430006070033
```

Verification Module
-------------------

```k
module VERIFICATION
    imports EDSL
    imports LEMMAS
    imports INFINITE-GAS
    imports EVM-OPTIMIZATIONS

    rule #getValue(#uint256(X)) => X requires #rangeUInt(256, X) [simplification]

    rule X <=Int chop(X +Int Y) => false requires #rangeUInt(256, X) andBool #rangeUInt(256, Y) andBool notBool #rangeUInt(256, X +Int Y) [simplification]

    syntax ByteArray ::= #binRuntime()
 // ----------------------------------
    rule #binRuntime() => #parseByteStack("0x6080604052348015600f57600080fd5b506004361060325760003560e01c8063771602f71460375780638b9732a9146080575b600080fd5b606a60048036036040811015604b57600080fd5b81019080803590602001909291908035906020019092919050505060c9565b6040518082815260200191505060405180910390f35b60b360048036036040811015609457600080fd5b81019080803590602001909291908035906020019092919050505060e7565b6040518082815260200191505060405180910390f35b60008082840190508381101560dd57600080fd5b8091505092915050565b6000808284019050809150509291505056fea2646970667358221220c666029b6b6de844da30183abbf37ea2865cdcb8a46ef623239384ca9c41de9864736f6c63430006070033") [macro]

endmodule
```

K Specifications
----------------

```k
module SOLIDITY-CODE-SPEC
    imports VERIFICATION
```

### Call with wrong call-data

```k
    claim <mode>     NORMAL   </mode>
          <schedule> ISTANBUL </schedule>

          <callStack> .List                                 </callStack>
          <program>   #binRuntime()                         </program>
          <jumpDests> #computeValidJumpDests(#binRuntime()) </jumpDests>

          <localMem>   .Memory     => ?_ </localMem>
          <memoryUsed> 0           => ?_ </memoryUsed>
          <wordStack>  .WordStack  => ?_ </wordStack>
          <pc>         0           => ?_ </pc>
          <endPC>      _           => ?_ </endPC>
          <gas>        #gas(_VGAS) => ?_ </gas>
          <callValue>  _CALLVALUE  => ?_ </callValue>

          <callData> #abiCallData("add", .TypedArgs) </callData>
          <k>          #execute   => #halt ...   </k>
          <output>     .ByteArray => ?_          </output>
          <statusCode> ?_         => EVMC_REVERT </statusCode>
```

### Add Positive Case

```k
    claim <mode>     NORMAL   </mode>
          <schedule> ISTANBUL </schedule>

          <callStack> .List                                 </callStack>
          <program>   #binRuntime()                         </program>
          <jumpDests> #computeValidJumpDests(#binRuntime()) </jumpDests>

          <localMem>   .Memory     => ?_ </localMem>
          <memoryUsed> 0           => ?_ </memoryUsed>
          <wordStack>  .WordStack  => ?_ </wordStack>
          <pc>         0           => ?_ </pc>
          <endPC>      _           => ?_ </endPC>
          <gas>        #gas(_VGAS) => ?_ </gas>
          <callValue>  0           => ?_ </callValue>

          <callData> #abiCallData("add", #uint256(X), #uint256(Y)) </callData>
          <k>          #execute   => #halt ...          </k>
          <output>     .ByteArray => #buf(32, X +Int Y) </output>
          <statusCode> ?_         => EVMC_SUCCESS       </statusCode>

     requires #rangeUInt(256, X)
      andBool #rangeUInt(256, Y)
      andBool #rangeUInt(256, X +Int Y)
```

### Add Negative Case

```k
    claim <mode>     NORMAL   </mode>
          <schedule> ISTANBUL </schedule>

          <callStack> .List                                 </callStack>
          <program>   #binRuntime()                         </program>
          <jumpDests> #computeValidJumpDests(#binRuntime()) </jumpDests>

          <localMem>   .Memory     => ?_ </localMem>
          <memoryUsed> 0           => ?_ </memoryUsed>
          <wordStack>  .WordStack  => ?_ </wordStack>
          <pc>         0           => ?_ </pc>
          <endPC>      _           => ?_ </endPC>
          <gas>        #gas(_VGAS) => ?_ </gas>
          <callValue>  0           => ?_ </callValue>

          <callData> #abiCallData("add", #uint256(X), #uint256(Y)) </callData>
          <k>          #execute   => #halt ...   </k>
          <output>     .ByteArray => ?_          </output>
          <statusCode> ?_         => EVMC_REVERT </statusCode>

     requires #rangeUInt(256, X)
      andBool #rangeUInt(256, Y)
      andBool notBool #rangeUInt(256, X +Int Y)
```

### Bad Add Failing Negative Case

```k
    claim <mode>     NORMAL   </mode>
          <schedule> ISTANBUL </schedule>

          <callStack> .List                                 </callStack>
          <program>   #binRuntime()                         </program>
          <jumpDests> #computeValidJumpDests(#binRuntime()) </jumpDests>

          <localMem>   .Memory     => ?_ </localMem>
          <memoryUsed> 0           => ?_ </memoryUsed>
          <wordStack>  .WordStack  => ?_ </wordStack>
          <pc>         0           => ?_ </pc>
          <endPC>      _           => ?_ </endPC>
          <gas>        #gas(_VGAS) => ?_ </gas>
          <callValue>  0           => ?_ </callValue>

          <callData> #abiCallData("badAdd", #uint256(X), #uint256(Y)) </callData>
          <k>          #execute   => #halt ...          </k>
          <output>     .ByteArray => #buf(32, X +Int Y) </output>
          <statusCode> ?_         => EVMC_SUCCESS       </statusCode>

     requires #rangeUInt(256, X)
      andBool #rangeUInt(256, Y)
      andBool notBool #rangeUInt(256, X +Int Y)
```

```k
endmodule
```
