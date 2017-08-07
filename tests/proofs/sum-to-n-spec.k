// The Sum To N Specification file
// ===============================

// Here we provide a specification file containing two reachability rules: (1) Main
// rule stating the functional correctness of the program, including the gas that
// it needs; and (2) The helper circularity rule stating the functional correctness
// of its loop and the gas it needs. Note that the program behaves
// incorrectly/unexpectedly if arithmetic overflow occurs during its execution. One
// challenge in verifying this program is to identify the conditions under which
// overflow does not occur.


module SUM-SPEC
    import ETHEREUM-SIMULATION


// Primary Claim
// -------------


   rule <program> #asMapOpCodes(
                        PUSH(1, 0); PUSH(32, N); JUMPDEST; DUP(1); ISZERO; PUSH(1, 52); JUMPI; DUP(1);
                        SWAP(2); ADD; SWAP(1); PUSH(1, 1); SWAP(1); SUB; PUSH(1, 35); JUMP; JUMPDEST;
                   .OpCodes) </program>
         <pc> 0 => 53 </pc>
         <wordStack> WS:WordStack => 0 : N *Int (N +Int 1) /Int 2 : WS:WordStack </wordStack>
         <gas> G => G -Int (52 *Int N +Int 27) </gas>
         <k> #execute ...</k>
         <mode> NORMAL </mode>
         <schedule> DEFAULT </schedule>
         <callStack> .List </callStack>
         <memoryUsed> 0   </memoryUsed>
         <localMem> .Map </localMem>
         <previousGas> _ => _ </previousGas>
      requires N >=Int 0
       andBool N <=Int 340282366920938463463374607431768211455  // largest integer for which the program does not overflow, a test point to the program for checking overflow of the sum program
       andBool #sizeWordStack(WS) <Int 1021
       andBool G >=Int 52 *Int N +Int 27


// Circularity
// -----------


    rule <program> #asMapOpCodes(
                        PUSH(1, 0); PUSH(32, N); JUMPDEST; DUP(1); ISZERO; PUSH(1, 52); JUMPI; DUP(1);
                        SWAP(2); ADD; SWAP(1); PUSH(1, 1); SWAP(1); SUB; PUSH(1, 35); JUMP; JUMPDEST;
                   .OpCodes) </program>
         <pc> 35 => 53 </pc>
         <wordStack> (I => 0) : (S => S +Int I *Int (I +Int 1) /Int 2) : WS:WordStack </wordStack>
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
       andBool #sizeWordStack(WS) <Int 1021
       andBool G >=Int 52 *Int I +Int 21
endmodule

