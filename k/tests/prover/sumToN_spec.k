module SUM-ITERATIVE-SPEC
    imports EVM

    rule
        <k> JUMP1 => . </k>
        <pc> 10 => 50 </pc>
        <localMem> 0 |-> (X:Int => 0) 1 |-> (0 => ((X *Int (X +Int 1)) /Int 2)) </localMem>
        <wordStack> 12 : X : .WordStack => .WordStack </wordStack>
        <accounts>
            <account>
	            <acctID> 1 </acctID>
	            <program> 0 |-> (PUSH X) 1 |-> ( PUSH 0 ) 2 |-> MSTORE 3 |-> ( PUSH 0 ) 4 |-> ( PUSH 1 ) 5 |-> MSTORE 6 |-> ( PUSH 0 ) 7 |-> MLOAD 8 |-> ( PUSH 12 ) 9 |-> JUMP1 10 |-> ( PUSH 50 ) 11 |-> JUMP 12 |-> ( PUSH 1 ) 13 |-> MLOAD 14 |-> ( PUSH 0 ) 15 |-> MLOAD 16 |-> ADD 17 |-> ( PUSH 1 ) 18 |-> MSTORE 19 |-> ( PUSH 1 ) 20 |-> ( PUSH 0 ) 21 |-> MLOAD 22 |-> SUB 23 |-> ( PUSH 0 ) 24 |-> MSTORE 25 |-> ( PUSH 6 ) 26 |-> JUMP </program>
	            <balance> 40 </balance>
	            <storage> _ </storage>
            </account>
        </accounts>
        requires X >=Int 0

    //loop invariant
    rule
        <k> JUMP1 => . </k>
        <pc> 10 => 50 </pc>
        <localMem> 0 |-> (X:Int => 0) 1 |-> (Y:Int => Y +Int ((X *Int (X +Int 1)) /Int 2)) </localMem>
        <wordStack> 12 : X : .WordStack => .WordStack </wordStack>
        <accounts>
            <account>
	            <acctID> 1 </acctID>
	            <program> 0 |-> (PUSH _) 1 |-> ( PUSH 0 ) 2 |-> MSTORE 3 |-> ( PUSH 0 ) 4 |-> ( PUSH 1 ) 5 |-> MSTORE 6 |-> ( PUSH 0 ) 7 |-> MLOAD 8 |-> ( PUSH 12 ) 9 |-> JUMP1 10 |-> ( PUSH 50 ) 11 |-> JUMP 12 |-> ( PUSH 1 ) 13 |-> MLOAD 14 |-> ( PUSH 0 ) 15 |-> MLOAD 16 |-> ADD 17 |-> ( PUSH 1 ) 18 |-> MSTORE 19 |-> ( PUSH 1 ) 20 |-> ( PUSH 0 ) 21 |-> MLOAD 22 |-> SUB 23 |-> ( PUSH 0 ) 24 |-> MSTORE 25 |-> ( PUSH 6 ) 26 |-> JUMP </program>
	            <balance> 40 </balance>
	            <storage> _ </storage>
            </account>
        </accounts>
        requires X >=Int 0

endmodule
