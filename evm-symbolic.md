EVM Execution
=============

This module contains custom extensions for smart contract verification.

```k
requires "edsl.k"

module EVM-SYMBOLIC     [symbolic]
    imports EVM
    imports EDSL
```

Symbolic result of ecrecover.

```k
    rule <k> ECREC => #end EVMC_SUCCESS ... </k>
         <callData> DATA </callData>
         <output> _ => #ecrec(#symEcrec(DATA)) </output>
      requires notBool #isConcrete(DATA) andBool #sizeWordStack(DATA) ==Int 128 andBool notBool #ecrecEmpty(DATA)
         
    rule <k> ECREC => #end EVMC_SUCCESS ... </k>
         <callData> DATA </callData>
         <output> _ => #ecrec(.Account) </output>
      requires notBool #isConcrete(DATA) andBool #sizeWordStack(DATA) ==Int 128 andBool #ecrecEmpty(DATA)

    //Symbolic wrapper over the argument of #ecrec, no implementation. 
    syntax Int ::= #symEcrec ( WordStack )   [function]
    
    //Symbolic predicate representing whether output of #ecrec is empty. No implementation.
    syntax Bool ::= #ecrecEmpty( WordStack ) [function]
```

```k
endmodule
```
