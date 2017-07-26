The Sum To N Specification file
===============================

Here we provide a specification file containing two reachability rules:
(1) Main rule stating the functional correctness of the program, including the gas that it needs; and
(2) The helper circularity rule stating the functional correctness of its loop and the gas it needs.
Note that the program behaves incorrectly/unexpectedly if arithmetic overflow occurs during its execution.
One challenge in verifying this program is to identify the conditions under which overflow does not occur.


```{.k}
module SUM-SPEC
    import ETHEREUM-SIMULATION

//Main rule
rule <program> #asMapOpCodes(
					PUSH(1, 0); PUSH(1, N); JUMPDEST; DUP(1); ISZERO; PUSH(1, 21); JUMPI; DUP(1);
					SWAP(2); ADD; SWAP(1); PUSH(1, 1); SWAP(1); SUB; PUSH(1, 4); JUMP; JUMPDEST;
			   .OpCodes) </program>
	 <pc> 0 => 22 </pc>
	 <wordStack> .WordStack => 0 : N *Int (N +Int 1) /Int 2 : .WordStack </wordStack>
	 <gas> G => G -Int (52 *Int N +Int 27) </gas>
	 <k> #execute ...</k>
	 <mode> NORMAL </mode>
	 <schedule> DEFAULT </schedule>
	 <callStack> .List </callStack>
	 <memoryUsed> 0   </memoryUsed>
	 <localMem> .Map </localMem>
	 <previousGas> _ => _ </previousGas>
requires N >=Int 0
 andBool N *Int (N +Int 1) /Int 2 <Int 2^Int 256
 andBool G >=Int 52 *Int N +Int 27


//Circularity rule
rule <program> #asMapOpCodes(
					PUSH(1, 0); PUSH(1, N); JUMPDEST; DUP(1); ISZERO; PUSH(1, 21); JUMPI; DUP(1);
					SWAP(2); ADD; SWAP(1); PUSH(1, 1); SWAP(1); SUB; PUSH(1, 4); JUMP; JUMPDEST;
			   .OpCodes) </program>
	 <pc> 4 => 22 </pc>
	 <wordStack> (I => 0) : (S => S +Int I *Int (I +Int 1) /Int 2) : .WordStack </wordStack>
	 <gas> G => G -Int (52 *Int I +Int 21) </gas>
     <k> #execute ...</k>
	 <mode> NORMAL </mode>
	 <schedule> DEFAULT </schedule>
	 <callStack> .List </callStack>
	 <memoryUsed> 0  </memoryUsed>
	 <localMem> .Map </localMem>
	 <previousGas> _ => _ </previousGas>
 requires I >=Int 0
 andBool S >=Int 0
 andBool S +Int I *Int (I +Int 1) /Int 2 <Int 2^Int 256
 andBool G >=Int 52 *Int I +Int 21

endmodule
```
