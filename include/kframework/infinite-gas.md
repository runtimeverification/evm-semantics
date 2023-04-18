KEVM Infinite Gas
=================

Here we use the construct `#gas` to represent positive infinity, while tracking the gas formula through execution.
This allows (i) computing final gas used, and (ii) never stopping because of out-of-gas.
Note that the argument to `#gas(_)` is just metadata tracking the current gas usage, and is not meant to be compared to other values.
As such, any `#gas(G)` and `#gas(G')` are the _same_ positive infinite, regardless of the values `G` and `G'`.
In particular, this means that `#gas(_) <Int #gas(_) => false`, and `#gas(_) <=Int #gas(_) => true`, regardless of the values contained in the `#gas(_)`.

```k
requires "evm.md"

module INFINITE-GAS
    imports BASIC-K
    imports INT
    imports BOOL
    imports GAS
    imports EVM

    syntax Gas ::= #gas(Int)

    rule #gas(I1) +Gas I2:Int   => #gas(I1 +Int I2) 
    rule I1:Int   +Gas #gas(I2) => #gas(I1 +Int I2) 
    rule #gas(I1) -Gas I2:Int   => #gas(I1 -Int I2) 
    rule I1:Int   -Gas #gas(I2) => #gas(I1 -Int I2) 
    rule #gas(I1) *Gas I2:Int   => #gas(I1 *Int I2) 
    rule I1:Int   *Gas #gas(I2) => #gas(I1 *Int I2) 
    rule #gas(I1) /Gas I2:Int   => #gas(I1 /Int I2)  requires I2 =/=Int 0
    rule I1:Int   /Gas #gas(I2) => #gas(I1 /Int I2)  requires I2 =/=Int 0

    rule  #gas(_)  <Gas _:Int   => false 
    rule  _:Int    <Gas #gas(_) => true  
    rule  #gas(_) <=Gas _:Int   => false 
    rule  _:Int   <=Gas #gas(_) => true  
    rule  #gas(_)  >Gas _:Int   => true  
    rule  _:Int    >Gas #gas(_) => false 
    rule  #gas(_) >=Gas _:Int   => true  
    rule  _:Int   >=Gas #gas(_) => false 
endmodule
```
