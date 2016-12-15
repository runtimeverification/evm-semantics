module SUM-ITERATIVE-SPEC
    imports EVM

rule
<T> 
    <k> CALL => . </k> 
    <id> 1 </id> 
    <pc> 10 => _ </pc> 
    <gas> _ => _ </gas>
    <gasPrice> _ </gasPrice> 
    <callStack> _ => _</callStack> 
    <wordStack> 2 : ( 4000 : ( 0 : ( 1 : ( 1 : ( 1 : .WordStack ) ) ) ) ) => _ </wordStack> 
    <localMem> (0 |-> X) => (0 |-> X 1 |-> (X *Int (X +Int 1)) /Int 2) </localMem>
    <accounts>
        <account>     
            <acctID> 1 </acctID> 
            <program> 0 |-> ( PUSH X ) 1 |-> ( PUSH 0 ) 2 |-> MSTORE 3 |-> ( PUSH 1 ) 4 |-> ( PUSH 1 ) 5 |-> ( PUSH 1 ) 6 |-> ( PUSH 0 ) 7 |-> ( PUSH 4000 ) 8 |-> ( PUSH 2 ) 9 |-> CALL </program>
            <storage> _ </storage>
            <balance> _ => _ </balance> 
        </account>
        <account>
            <acctID> 2 </acctID> 
            <program> 0 |-> ( PUSH 0 ) 1 |-> ( PUSH 1 ) 2 |-> MSTORE 3 |-> ( PUSH 0 ) 4 |-> MLOAD 5 |-> ( PUSH 10 ) 6 |-> JUMP1 7 |-> ( PUSH 1 ) 8 |-> ( PUSH 1 ) 9 |-> RETURN 10 |-> ( PUSH 1 ) 11 |-> MLOAD 12 |-> ( PUSH 0 ) 13 |-> MLOAD 14 |-> ADD 15 |-> ( PUSH 1 ) 16 |-> MSTORE 17 |-> ( PUSH 1 ) 18 |-> ( PUSH 0 ) 19 |-> MLOAD 20 |-> SUB 21 |-> ( PUSH 0 ) 22 |-> MSTORE 23 |-> ( PUSH 3 ) 24 |-> JUMP </program>
            <storage> _ </storage>
            <balance> _ => _ </balance> 
        </account>
    </accounts>
</T>

//circularity (Inductive Hypothesis / Loop Invariant)
rule
<T> 
    <k> JUMP1 => . </k> 
    <id> 2 => 1 </id> 
    <pc> 7 => 10 </pc> 
    <gas> _ => _ </gas>
    <gasPrice> _ </gasPrice> 
    <callStack>  { 1 | 10 | _ | 1 : ( 1 : .WordStack ) | 0 |-> X } .CallStack => _ </callStack> 
    <wordStack> 10 : ( A : .WordStack ) => _ </wordStack>
    <localMem> 0 |-> A 1 |-> B => (0 |-> X 1 |-> (B +Int (A *Int (A +Int 1)) /Int 2)) </localMem>
    <accounts>
        <account>     
        <acctID> 1 </acctID> 
        <program> 0 |-> ( PUSH X ) 1 |-> ( PUSH 0 ) 2 |-> MSTORE 3 |-> ( PUSH 1 ) 4 |-> ( PUSH 1 ) 5 |-> ( PUSH 1 ) 6 |-> ( PUSH 0 ) 7 |-> ( PUSH 4000 ) 8 |-> ( PUSH 2 ) 9 |-> CALL 
        </program>
        <storage> _ </storage>
        <balance> _ => _ </balance> 
        </account>
        <account>
        <acctID> 2 </acctID> 
        <program> 0 |-> ( PUSH 0 ) 1 |-> ( PUSH 1 ) 2 |-> MSTORE 3 |-> ( PUSH 0 ) 4 |-> MLOAD 5 |-> ( PUSH 10 ) 6 |-> JUMP1 7 |-> ( PUSH 1 ) 8 |-> ( PUSH 1 ) 9 |-> RETURN 10 |-> ( PUSH 1 ) 11 |-> MLOAD 12 |-> ( PUSH 0 ) 13 |-> MLOAD 14 |-> ADD 15 |-> ( PUSH 1 ) 16 |-> MSTORE 17 |-> ( PUSH 1 ) 18 |-> ( PUSH 0 ) 19 |-> MLOAD 20 |-> SUB 21 |-> ( PUSH 0 ) 22 |-> MSTORE 23 |-> ( PUSH 3 ) 24 |-> JUMP </program>
        <storage> _ </storage>
        <balance> _ => _ </balance> 
        </account>
    </accounts>

</T>

endmodule
