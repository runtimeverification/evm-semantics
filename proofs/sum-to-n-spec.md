The Sum To N Specification file
===============================

Here we provide a specification file containing two reachability rules - the main
proof rule and the circularity rule.

```{.k}
module ADD1-SPEC
    import ETHEREUM-SIMULATION

    rule
    <generatedTop>
        <k>         .   </k>
        <exit-code> 1   </exit-code>
        <mode>      NORMAL </mode>
        <schedule>  DEFAULT </schedule>
        <analysis>  .Map </analysis>
        <ethereum>
            <evm>
                <op>  #next ~> #execute => #end </op>
                <output>.WordStack</output>
                <memoryUsed>0</memoryUsed>
                <callDepth>0</callDepth>
                <callStack>.List</callStack>
                <interimStates>.List</interimStates>
                <callLog>.Set</callLog>
                <txExecState>
                    <program>0 |-> PUSH ( 1 , 0 ) 2 |-> PUSH ( 1 , N:Int ) 4 |-> JUMPDEST 5 |-> DUP ( 1 ) 6 |-> ISZERO 7 |-> PUSH ( 1 , 21 ) 9 |-> JUMPI 10 |-> DUP ( 1 ) 11 |-> SWAP ( 2 ) 12 |-> ADD 13 |-> SWAP ( 1 ) 14 |-> PUSH ( 1 , 1 ) 16 |-> SWAP ( 1 ) 17 |-> SUB 18 |-> PUSH ( 1 , 4 ) 20 |-> JUMP 21 |-> JUMPDEST 22 |-> POP 23 |-> PUSH ( 1 , 0 ) 25 |-> SSTORE</program>
                    <id>87579061662017136990230301793909925042452127430</id>
                    <caller>428365927726247537526132020791190998556166378203</caller>
                    <callData>0 : .WordStack</callData>
                    <callValue>0</callValue>
                    <wordStack>.WordStack</wordStack>
                    <localMem>.Map</localMem>
                    <pc>0 => 26</pc>
                    <gas>100000 => ?G:Int</gas>
                    <previousGas>PG => ?PG:Int</previousGas>
                </txExecState>
                <substate>
                    <selfDestruct>.Set</selfDestruct>
                    <log>.Set</log>
                    <refund>0</refund>
                </substate>
                <gasPrice>100000000000000</gasPrice>
                <origin>428365927726247537526132020791190998556166378203</origin>
                <gasLimit>1000000</gasLimit>
                <coinbase>244687034288125203496486448490407391986876152250</coinbase>
                <timestamp>1</timestamp>
                <number>0</number>
                <previousHash>0</previousHash>
                <difficulty>256</difficulty>
            </evm>
            <network>
                <activeAccounts>SetItem ( 87579061662017136990230301793909925042452127430 )</activeAccounts>
                <accounts>
                    <account>
                        <acctID>87579061662017136990230301793909925042452127430</acctID>
                        <balance>1000000000000000000</balance>
                        <code>0 |-> PUSH ( 1 , 0 ) 2 |-> PUSH ( 1 , N ) 4 |-> JUMPDEST 5 |-> DUP ( 1 ) 6 |-> ISZERO 7 |-> PUSH ( 1 , 21 ) 9 |-> JUMPI 10 |-> DUP ( 1 ) 11 |-> SWAP ( 2 ) 12 |-> ADD 13 |-> SWAP ( 1 ) 14 |-> PUSH ( 1 , 1 ) 16 |-> SWAP ( 1 ) 17 |-> SUB 18 |-> PUSH ( 1 , 4 ) 20 |-> JUMP 21 |-> JUMPDEST 22 |-> POP 23 |-> PUSH ( 1 , 0 ) 25 |-> SSTORE</code>
                        <storage>.Map => 0 |-> (N *Int (N +Int 1)) /Int 2</storage>
                        <acctMap>"nonce" |-> 0</acctMap>
                    </account>
                </accounts>
                <messages> .Bag </messages>
            </network>
        </ethereum>
    </generatedTop>
    requires (N >Int 0) andBool (N <Int (2 ^Int 128))
```
The Cirucularity Rule
---------------------


```{.k}
    rule
    <generatedTop>
        <k>         .   </k>
        <exit-code> 1   </exit-code>
        <mode>      NORMAL </mode>
        <schedule>  DEFAULT </schedule>
        <analysis>  .Map </analysis>
        <ethereum>
            <evm>
                <op>  #execute => #end </op>
                <output>.WordStack</output>
                <memoryUsed>0</memoryUsed>
                <callDepth>0</callDepth>
                <callStack>.List</callStack>
                <interimStates>.List</interimStates>
                <callLog>.Set</callLog>
                <txExecState>
                    <program>0 |-> PUSH ( 1 , 0 ) 2 |-> PUSH ( 1 , N:Int ) 4 |-> JUMPDEST 5 |-> DUP ( 1 ) 6 |-> ISZERO 7 |-> PUSH ( 1 , 21 ) 9 |-> JUMPI 10 |-> DUP ( 1 ) 11 |-> SWAP ( 2 ) 12 |-> ADD 13 |-> SWAP ( 1 ) 14 |-> PUSH ( 1 , 1 ) 16 |-> SWAP ( 1 ) 17 |-> SUB 18 |-> PUSH ( 1 , 4 ) 20 |-> JUMP 21 |-> JUMPDEST 22 |-> POP 23 |-> PUSH ( 1 , 0 ) 25 |-> SSTORE</program>
                    <id>87579061662017136990230301793909925042452127430</id>
                    <caller>428365927726247537526132020791190998556166378203</caller>
                    <callData>0 : .WordStack</callData>
                    <callValue>0</callValue>
                    <wordStack> NP:Int : ( PSUM:Int : .WordStack ) </wordStack>
                    <localMem>.Map</localMem>
                    <pc>4 => 26</pc>
                    <gas> GC:Int => ?GC </gas>
                    <previousGas> PG:Int => ?PG </previousGas>
                </txExecState>
                <substate>
                    <selfDestruct>.Set</selfDestruct>
                    <log>.Set</log>
                    <refund>0</refund>
                </substate>
                <gasPrice>100000000000000</gasPrice>
                <origin>428365927726247537526132020791190998556166378203</origin>
                <gasLimit>1000000</gasLimit>
                <coinbase>244687034288125203496486448490407391986876152250</coinbase>
                <timestamp>1</timestamp>
                <number>0</number>
                <previousHash>0</previousHash>
                <difficulty>256</difficulty>
            </evm>
            <network>
                <activeAccounts>SetItem ( 87579061662017136990230301793909925042452127430 )</activeAccounts>
                <accounts>
                    <account>
                        <acctID>87579061662017136990230301793909925042452127430</acctID>
                        <balance>1000000000000000000</balance>
                        <code>0 |-> PUSH ( 1 , 0 ) 2 |-> PUSH ( 1 , N ) 4 |-> JUMPDEST 5 |-> DUP ( 1 ) 6 |-> ISZERO 7 |-> PUSH ( 1 , 21 ) 9 |-> JUMPI 10 |-> DUP ( 1 ) 11 |-> SWAP ( 2 ) 12 |-> ADD 13 |-> SWAP ( 1 ) 14 |-> PUSH ( 1 , 1 ) 16 |-> SWAP ( 1 ) 17 |-> SUB 18 |-> PUSH ( 1 , 4 ) 20 |-> JUMP 21 |-> JUMPDEST 22 |-> POP 23 |-> PUSH ( 1 , 0 ) 25 |-> SSTORE</code>
                        <storage>.Map => 0 |-> PSUM +Int (NP *Int (NP +Int 1)) /Int 2</storage>
                        <acctMap>"nonce" |-> 0</acctMap>
                    </account>
                </accounts>
                <messages> .Bag </messages>
            </network>
        </ethereum>
    </generatedTop>
    requires (NP >=Int 0) andBool (NP <Int (2 ^Int 128))

endmodule
```
