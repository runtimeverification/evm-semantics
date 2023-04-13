KEVM Infinite Gas
=================

Here we use the construct `#gas` to represent positive infinity, while tracking the gas formula through execution.
This allows (i) computing final gas used, and (ii) never stopping because of out-of-gas.
Note that the argument to `#gas(_)` is just metadata tracking the current gas usage, and is not meant to be compared to other values.
As such, any `#gas(G)` and `#gas(G')` are the _same_ positive infinite, regardless of the values `G` and `G'`.
In particular, this means that `#gas(_) <Int #gas(_) => false`, and `#gas(_) <=Int #gas(_) => true`, regardless of the values contained in the `#gas(_)`.

```k
requires "evm.md"

module INFINITE-GAS-SYNTAX
    imports GAS-SYNTAX
    imports INT-SYNTAX
    imports BOOL-SYNTAX

    syntax Gas ::= #gas(Int)
    
    // syntax Gas ::=  Gas  "+" Gas [function, total] 
    //              |  Gas  "-" Gas [function, total]
    //              |  Gas  "*" Gas [function, total]
    //             //  |  Gas  "/" Gas [function]
    
    syntax Bool ::= Gas  "<" Gas [function, total]
                  | Gas "<=" Gas [function, total]
                  | Gas  ">" Gas [function, total]
                  | Gas ">=" Gas [function, total]
endmodule

module INFINITE-GAS
    imports INFINITE-GAS-SYNTAX
    imports BASIC-K
    imports INT
    imports BOOL
    imports GAS
    imports EVM

    // // Arithemtic operators apply to encapsulated Int 
    // rule #gas(I1) + I2:Int  => #gas(I1 +Int I2) 
    // rule I1:Int  + #gas(I2) => #gas(I1 +Int I2) 
    // rule #gas(I1) - I2:Int  => #gas(I1 -Int I2) 
    // rule I1:Int  - #gas(I2) => #gas(I1 -Int I2) 
    // rule #gas(I1) * I2:Int  => #gas(I1 *Int I2) 
    // rule I1:Int  * #gas(I2) => #gas(I1 *Int I2) 
    // // rule #gas(I1) / I2:Int  => #gas(I1 /Int I2)  requires I2 =/=Int 0
    // // rule I1:Int  / #gas(I2) => #gas(I1 /Int I2)  requires I2 =/=Int 0

    // Comparison operators apply to infinity
    rule  #gas(_)  < _:Int  => false 
    rule  _:Int   < #gas(_) => true  
    rule  #gas(_) <= _:Int  => false 
    rule  _:Int  <= #gas(_) => true  
    rule  #gas(_)  > _:Int  => true  
    rule  _:Int   > #gas(_) => false 
    rule  #gas(_) >= _:Int  => true  
    rule  _:Int  >= #gas(_) => false 

    rule <k>  G:Int ~> #deductGas => . ... </k> <gas> #gas(GAVAIL) => #gas(GAVAIL -Int G) </gas>

    rule <k> #gasExec(SCHED, SSTORE INDEX NEW) => Csstore(SCHED, NEW, #lookup(STORAGE, INDEX), #lookup(ORIGSTORAGE, INDEX)) ... </k>
         <id> ACCT </id>
         <gas> #gas(_) </gas>
         <account>
           <acctID> ACCT </acctID>
           <storage> STORAGE </storage>
           <origStorage> ORIGSTORAGE </origStorage>
           ...
         </account>
         <refund> R => R +Int Rsstore(SCHED, NEW, #lookup(STORAGE, INDEX), #lookup(ORIGSTORAGE, INDEX)) </refund>

    rule isKResult(_:Gas)  => true
endmodule
```
