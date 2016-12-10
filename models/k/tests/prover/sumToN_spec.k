module SUM-ITERATIVE-SPEC
    imports EVM

    rule
    <T> 
    	<k> ( ( account : - id : 1 - balance : 40 - program : ( PUSH X:Int ) ; ( ( PUSH 0 ) ; ( MSTORE ; ( ( PUSH 0 ) ; ( ( PUSH 1 ) ; ( MSTORE ; ( ( PUSH 0 ) ; ( MLOAD ; ( ( PUSH 12 ) ; ( JUMP1 ; ( ( PUSH 50 ) ; ( JUMP ; ( ( PUSH 1 ) ; ( MLOAD ; ( ( PUSH 0 ) ; ( MLOAD ; ( ADD ; ( ( PUSH 1 ) ; ( MSTORE ; ( ( PUSH 1 ) ; ( ( PUSH 0 ) ; ( MLOAD ; ( SUB ; ( ( PUSH 0 ) ; ( MSTORE ; ( ( PUSH 6 ) ; ( JUMP ; .Program ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) - storage : ( 30 , ( 20 , ( 25 , .WordList ) ) ) ) .Accounts ) START 1 </k> 
    	<accountID> .AcctID </accountID> 
    	<pc> 0 => 50 </pc> 
    	<wordStack> .WordStack </wordStack> 
    	<localMem> .Map </localMem> 
    	<callStack> .CallStack </callStack>
    </T>
    => 
    <T> 
    	<k> . </k> 
     	<accountID> _ </accountID> 
    	<pc>  50 </pc>
    	<wordStack> _ </wordStack> 
    	<localMem> 0 |-> 0 1 |-> ((X *Int (X +Int 1)) /Int 2)) </localMem>

    </T>
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
	            <program> 0 |-> (PUSH V) 1 |-> ( PUSH 0 ) 2 |-> MSTORE 3 |-> ( PUSH 0 ) 4 |-> ( PUSH 1 ) 5 |-> MSTORE 6 |-> ( PUSH 0 ) 7 |-> MLOAD 8 |-> ( PUSH 12 ) 9 |-> JUMP1 10 |-> ( PUSH 50 ) 11 |-> JUMP 12 |-> ( PUSH 1 ) 13 |-> MLOAD 14 |-> ( PUSH 0 ) 15 |-> MLOAD 16 |-> ADD 17 |-> ( PUSH 1 ) 18 |-> MSTORE 19 |-> ( PUSH 1 ) 20 |-> ( PUSH 0 ) 21 |-> MLOAD 22 |-> SUB 23 |-> ( PUSH 0 ) 24 |-> MSTORE 25 |-> ( PUSH 6 ) 26 |-> JUMP </program> 
	            <balance> 40 </balance>
	            <storage> _ </storage>        
            </account> 
        </accounts> 
        requires X >=Int 0 

endmodule


