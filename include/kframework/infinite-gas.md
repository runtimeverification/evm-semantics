KEVM Infinite Gas
=================

Here we use the construct `#gas` to represent positive infinity, while tracking the gas formula through execution.
This allows (i) computing final gas used, and (ii) never stopping because of out-of-gas.
Note that the argument to `#gas(_)` is just metadata tracking the current gas usage, and is not meant to be compared to other values.
As such, any `#gas(G)` and `#gas(G')` are the _same_ positive infinite, regardless of the values `G` and `G'`.
In particular, this means that `#gas(_) <Gas #gas(_) => false`, and `#gas(_) <=Gas #gas(_) => true`, regardless of the values contained in the `#gas(_)`.

```k
requires "evm.md"

module INFINITE-GAS
    imports BASIC-K
    imports INT
    imports BOOL
    imports GAS
    imports EVM

    syntax Gas ::= #gas(Int) [klabel(infGas), symbol, smtlib(infGas)]

    rule #gas(G) +Gas G'       => #gas(G +Int G')
    rule #gas(G) -Gas G'       => #gas(G -Int G')
    rule #gas(G) *Gas G'       => #gas(G *Int G')
    rule #gas(G) /Gas G'       => #gas(G /Int G')  requires G' =/=Int 0
    rule      G  +Gas #gas(G') => #gas(G +Int G')
    rule      G  -Gas #gas(G') => #gas(G -Int G')
    rule      G  *Gas #gas(G') => #gas(G *Int G')
    rule      G  /Gas #gas(G') => #gas(G /Int G')  requires G' =/=Int 0
    rule #gas(G) +Gas #gas(G') => #gas(G +Int G')
    rule #gas(G) -Gas #gas(G') => #gas(G -Int G')
    rule #gas(G) *Gas #gas(G') => #gas(G *Int G')
    rule #gas(G) /Gas #gas(G') => #gas(G /Int G')  requires G' =/=Int 0

    rule  _:Int    <Gas #gas(_) => true
    rule  #gas(_)  <Gas _       => false [simplification]
    rule  #gas(_) <=Gas _:Int   => false
    rule _        <=Gas #gas(_) => true  [simplification]

    rule minGas(#gas(G), #gas(G')) => #gas(minInt(G, G'))
    rule minGas(G:Int  , #gas(_))  => G
    rule minGas(#gas(_), G':Int)   => G'

    rule gas2Int(#gas(G)) => G

    rule #allBut64th(#gas(G)) => #gas(#allBut64th(G))
    rule Cgascap(SCHED, #gas(GCAP), #gas(GAVAIL), GEXTRA) => #gas(Cgascap(SCHED, GCAP, GAVAIL, GEXTRA)) [simplification]
    rule Cgascap(SCHED, #gas(GCAP), GAVAIL:Int, GEXTRA)   => #gas(Cgascap(SCHED, GCAP, GAVAIL, GEXTRA)) [simplification]
    rule Cgascap(SCHED, GCAP:Int, #gas(GAVAIL), GEXTRA)   => #gas(Cgascap(SCHED, GCAP, GAVAIL, GEXTRA)) [simplification]

    rule #if B #then #gas(G) #else #gas(G') #fi => #gas(#if B #then G #else G' #fi) [simplification]
endmodule
```
