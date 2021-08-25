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

    function max(uint256 a, uint256 b) external pure returns (uint256) {
        if (a < b) {
            return b;
        }
        return a;
    }
}
```

Run `solc test.sol --bin-runtime`

```evm
======= tests/specs/examples/test.sol:Test =======
Binary of the runtime part:
608060405234801561001057600080fd5b50600436106100415760003560e01c80636d5433e614610046578063771602f7146100925780638b9732a9146100de575b600080fd5b61007c6004803603604081101561005c57600080fd5b81019080803590602001909291908035906020019092919050505061012a565b6040518082815260200191505060405180910390f35b6100c8600480360360408110156100a857600080fd5b810190808035906020019092919080359060200190929190505050610146565b6040518082815260200191505060405180910390f35b610114600480360360408110156100f457600080fd5b810190808035906020019092919080359060200190929190505050610165565b6040518082815260200191505060405180910390f35b60008183101561013c57819050610140565b8290505b92915050565b60008082840190508381101561015b57600080fd5b8091505092915050565b6000808284019050809150509291505056fea2646970667358221220b6c7c7edcc949d990b370be9407bd7427f1897352a7a86cdd919d4243dcb838c64736f6c63430006070033
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
    rule #binRuntime() => #parseByteStack("0x608060405234801561001057600080fd5b50600436106100415760003560e01c80636d5433e614610046578063771602f7146100925780638b9732a9146100de575b600080fd5b61007c6004803603604081101561005c57600080fd5b81019080803590602001909291908035906020019092919050505061012a565b6040518082815260200191505060405180910390f35b6100c8600480360360408110156100a857600080fd5b810190808035906020019092919080359060200190929190505050610146565b6040518082815260200191505060405180910390f35b610114600480360360408110156100f457600080fd5b810190808035906020019092919080359060200190929190505050610165565b6040518082815260200191505060405180910390f35b60008183101561013c57819050610140565b8290505b92915050565b60008082840190508381101561015b57600080fd5b8091505092915050565b6000808284019050809150509291505056fea2646970667358221220b6c7c7edcc949d990b370be9407bd7427f1897352a7a86cdd919d4243dcb838c64736f6c63430006070033") [macro]

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
