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
    function add(uint256 a, uint256 b) internal pure returns (uint256) {
        uint256 c = a + b;
        require(c >= a);
        return c;
    }
}
```

Run `solc test.sol --bin-runtime`

```evm
======= tests/specs/examples/test.sol:Test =======
Binary of the runtime part:
6080604052600080fdfea26469706673582212204f063286d3fc32b402abb10d50b52beba4a41705348be6e7953d4558b0eb115764736f6c63430006070033
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
    rule #binRuntime() => #parseByteStack("0x6080604052348015600f57600080fd5b506004361060285760003560e01c8063771602f714602d575b600080fd5b606060048036036040811015604157600080fd5b8101908080359060200190929190803590602001909291905050506076565b6040518082815260200191505060405180910390f35b600080828401905083811015608a57600080fd5b809150509291505056fea2646970667358221220d4f890eafb82f18efe22e5f44df631ae8e5bfc274bd3559d320c495734442bc064736f6c63430006070033") [macro]

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

```k
endmodule
```
