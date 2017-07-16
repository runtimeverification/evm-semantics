// The Sum To N Specification file
// ===============================

// Here we provide a specification file containing two reachability rules - the
// main proof rule and the circularity rule.


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
                <op>  #next ~> #execute => . </op>
                <output>.WordStack</output>
                <memoryUsed>0</memoryUsed>
                <callDepth>0</callDepth>
                <callStack>.List</callStack>
                <interimStates>.List</interimStates>
                <callLog>.Set</callLog>
                <txExecState>
                    <program>0 |-> PUSH ( 1 , 0 ) 2 |-> PUSH ( 1 , 10 ) 4 |-> JUMPDEST 5 |-> DUP ( 1 ) 6 |-> ISZERO 7 |-> PUSH ( 1 , 21 ) 9 |-> JUMPI 10 |-> DUP ( 1 ) 11 |-> SWAP ( 2 ) 12 |-> ADD 13 |-> SWAP ( 1 ) 14 |-> PUSH ( 1 , 1 ) 16 |-> SWAP ( 1 ) 17 |-> SUB 18 |-> PUSH ( 1 , 4 ) 20 |-> JUMP 21 |-> JUMPDEST 22 |-> POP 23 |-> PUSH ( 1 , 0 ) 25 |-> SSTORE</program>
                    <id>87579061662017136990230301793909925042452127430</id>
                    <caller>428365927726247537526132020791190998556166378203</caller>
                    <callData>0 : .WordStack</callData>
                    <callValue>0</callValue>
                    <wordStack>.WordStack => 0 : .WordStack</wordStack>
                    <localMem>.Map</localMem>
                    <pc>0 => 26</pc>
                    <gas>100000 => 79448</gas>
                    <previousGas>0 => 99448</previousGas>
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
                        <code>0 |-> PUSH ( 1 , 0 ) 2 |-> PUSH ( 1 , 10 ) 4 |-> JUMPDEST 5 |-> DUP ( 1 ) 6 |-> ISZERO 7 |-> PUSH ( 1 , 21 ) 9 |-> JUMPI 10 |-> DUP ( 1 ) 11 |-> SWAP ( 2 ) 12 |-> ADD 13 |-> SWAP ( 1 ) 14 |-> PUSH ( 1 , 1 ) 16 |-> SWAP ( 1 ) 17 |-> SUB 18 |-> PUSH ( 1 , 4 ) 20 |-> JUMP 21 |-> JUMPDEST 22 |-> POP 23 |-> PUSH ( 1 , 0 ) 25 |-> SSTORE</code>
                        <storage>.Map => 0 |-> 55</storage>
                        <acctMap>"nonce" |-> 0</acctMap>
                    </account>
                </accounts>
                <messages> .Bag </messages>
            </network>
        </ethereum>
    </generatedTop>
// rule
// <k>
// .
// </k>
// <mode> NORMAL </mode>
// <schedule> DEFAULT </schedule>
// <op>  #execute => #execute </op>
// <memoryUsed> 0   </memoryUsed>
//  <callStack> .List => .List </callStack>
// <localMem> .Map </localMem>
// <gas> N =>N1 </gas>
// <previousGas> 0 => N1+Int 2 </previousGas>
// <pc> 0 => 23 </pc>
//  <id> ACCT </id>
//   <network>
// <activeAccounts>   SetItem (ACCT)   </activeAccounts>
//
//  <accounts>
//  ...
// <account>
// <acctID> ACCT </acctID>
// <storage> .Map</storage>
// ...
// </account>
// ...
// </accounts>
// <messages> .Bag </messages>
// </network>
// <wordStack> .WordStack => (I *Int (I +Int 1)/Int 2) : .WordStack </wordStack>
// <program> #asMapOpCodes( PUSH(1, 0) ; PUSH(1, I)
// ; JUMPDEST ; DUP(1) ; ISZERO ; PUSH(1, 21) ; JUMPI ; DUP(1) ; SWAP(2) ; ADD ; SWAP(1) ; PUSH(1, 1) ;
// SWAP(1) ; SUB ; PUSH(1, 4) ; JUMP ; JUMPDEST ; POP ; .OpCodes
// )</program>
// requires N>=Int (52*Int I) +Int 29 andBool I>=Int 1  andBool I<Int 2^Int 256
// ensures N-Int N1==Int (52*Int I )+Int 29
//
//
// //loop invariant
// rule
// <k> . </k>
// <mode> NORMAL </mode>
// <schedule> DEFAULT </schedule>
// <op> #execute=> #execute</op>
// <memoryUsed> 0  </memoryUsed>
// <callStack> .List => .List </callStack>
// <localMem>.Map</localMem>
// <gas> N =>N1 </gas>
// <previousGas> N+Int 8 => N1+Int 2 </previousGas>
// <pc> 4=>23</pc>
//  <id> ACCT </id>
//   <network>
// <activeAccounts>   SetItem (ACCT)   </activeAccounts>
//  <accounts>
// <account>
// <acctID> ACCT </acctID>
// <storage> .Map</storage>
// ...
// </account>
// </accounts>
// <messages> .Bag </messages>
// </network>
//
// <program> #asMapOpCodes( PUSH(1, 0) ; PUSH(1, I)
// ; JUMPDEST ; DUP(1) ; ISZERO ; PUSH(1, 21) ; JUMPI ; DUP(1) ; SWAP(2) ; ADD ; SWAP(1) ; PUSH(1, 1) ;
// SWAP(1) ; SUB ; PUSH(1, 4) ; JUMP ; JUMPDEST ; POP ;
//  .OpCodes)</program>
// <wordStack> I1:Int : I2:Int : .WordStack =>(I2 +Int (I1 *Int (I1 -Int 1)/Int 2)) : .WordStack </wordStack>
//
// requires N>=Int (52*Int I1) +Int 23 andBool I1>=Int 0  andBool I1<=Int I andBool I2>=Int 0 andBool I1<Int 2^Int 256 andBool I2<Int 2^Int 256
// ensures N-Int N1==Int (52*Int I1 )+Int 23
//
endmodule

