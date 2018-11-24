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

Split construct. Allows to force branching on arbitrary boolean expressions.
Usage pattern in specs: `k: (split(Exp) => .) ~> (#execute => #halt) ~> _`
If you want to enumerate all values in a certain range, this is an example usage:
```
k: ( split(NR_SIG ==Int 1) ~> split(NR_SIG ==Int 2) => . ) ~> (#execute => #halt) ~> _
+requires:
    andBool #range(1 <= NR_SIG <= 2)
``` 
You have to enumerate each value in a separate split, because kprove cannot infer the last value (e.g. NR_SIG ==Int 2)
from the other constraints, even if it's the only value possible.
But if you put this value explicitly in another split, then K can prove that child path 
`(NR_SIG ==Int 2) ==K false` is infeasible and won't generate it.

```k
    syntax KItem ::= split ( Bool )
 // -----------------------------------------
    rule split ( true ) => .
    rule split ( false ) => .
```

```k
endmodule
```
