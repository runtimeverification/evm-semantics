// The Sum To N Specification file
// ===============================

// Here we provide a specification file containing two reachability rules - the
// main proof rule and the circularity rule.


module SUM-SPEC
    import ETHEREUM-SIMULATION
	/*
rule
<k>
.
</k>
<mode> NORMAL </mode>
<schedule> DEFAULT </schedule>
<op>  #execute => ?OP:K</op>
<memoryUsed> 0   </memoryUsed>
 <callStack> .List => .List </callStack>
<localMem> .Map </localMem>
<gas> G =>G1 </gas>
<previousGas> 0 => G1+Int 1 </previousGas>
<pc> 0 => 22 </pc>
<wordStack> .WordStack => 0: (I *Int (I +Int 1)/Int 2) : .WordStack </wordStack>
<program> #asMapOpCodes( PUSH(1, 0) ; PUSH(1, I)
; JUMPDEST ; DUP(1) ; ISZERO ; PUSH(1, 21) ; JUMPI ; DUP(1) ; SWAP(2) ; ADD ; SWAP(1) ; PUSH(1, 1) ;
SWAP(1) ; SUB ; PUSH(1, 4) ; JUMP ; JUMPDEST ; .OpCodes
)</program>
requires G>=Int (52*Int I) +Int 27 andBool I>=Int 1 andBool I<Int 4 
ensures G -Int G1 ==Int (52*Int I) +Int 27*/

//circularity rule
rule
<k> #execute=> #execute ...</k>
<mode> NORMAL </mode>
<schedule> DEFAULT </schedule>
<memoryUsed> 0  </memoryUsed>
<callStack> .List </callStack>
<localMem>.Map</localMem>
<gas> G => G1 </gas>
<previousGas> _ => G1 +Int 1  </previousGas>
<pc> 4=>22</pc>
<program> #asMapOpCodes( PUSH(1, 0) ; PUSH(1, I)
; JUMPDEST ; DUP(1) ; ISZERO ; PUSH(1, 21) ; JUMPI ; DUP(1) ; SWAP(2) ; ADD ; SWAP(1) ; PUSH(1, 1) ;
SWAP(1) ; SUB ; PUSH(1, 4) ; JUMP ; JUMPDEST ; 
 .OpCodes)</program>
<wordStack> N : S : .WordStack => 0: (S +Int (N *Int (N+Int 1)/Int 2)): .WordStack </wordStack>
requires G>=Int (52*Int N) +Int 21 andBool N>=Int 0 andBool S>=Int 0 andBool (S +Int (N *Int (N+Int 1)/Int 2))<Int 2^Int 16
ensures G -Int G1 ==Int (52*Int N) +Int 21

endmodule
