requires "asm.md"
requires "lemmas/lemmas.k"

module VERIFICATION
    imports EVM-ASSEMBLY
    imports LEMMAS

    rule #sizeWordStack ( WS , N:Int )
      => N +Int #sizeWordStack ( WS , 0 )
      requires N =/=K 0 [simplification]

    rule bool2Word(A) ==K 0 => notBool(A) [simplification]

    rule chop(I) => I requires #rangeUInt(256, I) [simplification]

    syntax Bytes ::= "sumToN" [macro]
 // -------------------------------------
    rule sumToN
      => #asmOpCodes(PUSH(1, 0) ; SWAP(1)                   // s = 0 ; n = N
                    ; JUMPDEST                              // label:loop
                    ; DUP(1) ; ISZERO ; PUSH(1, 20) ; JUMPI // if n == 0, jump to end
                    ; DUP(1) ; SWAP(2) ; ADD                // s = s + n
                    ; SWAP(1) ; PUSH(1, 1) ; SWAP(1) ; SUB  // n = n - 1
                    ; PUSH(1, 3) ; JUMP                     // jump to loop
                    ; JUMPDEST                              // label:end
                    ; .OpCodes
                    )
endmodule

module SUM-TO-N-SPEC
    imports VERIFICATION

    claim [main]:
          <k> #execute => #halt ... </k>
          <mode> NORMAL </mode>
          <schedule> ISTANBUL </schedule>
          <useGas> true </useGas>
          <callStack> .List </callStack>
          <memoryUsed> 0   </memoryUsed>
          <localMem> .Bytes </localMem>
          <callGas> _ </callGas>
          <program> sumToN </program>
          <jumpDests> #computeValidJumpDests(sumToN) </jumpDests>
          <pc>        0  => 21                                    </pc>
          <wordStack> N : WS => 0 : N *Int (N +Int 1) /Int 2 : WS </wordStack>
          <gas>       G  => G -Int (52 *Int N +Int 27)            </gas>
      requires N >=Int 0
       andBool N <=Int 340282366920938463463374607431768211455
       andBool #sizeWordStack(WS) <Int 1021
       andBool G >=Int 52 *Int N +Int 27
      [depends(loop)]

    claim [loop]:
          <k> #execute => #halt ... </k>
          <mode> NORMAL </mode>
          <schedule> ISTANBUL </schedule>
          <useGas> true </useGas>
          <callStack> .List </callStack>
          <memoryUsed> 0   </memoryUsed>
          <localMem> .Bytes </localMem>
          <callGas> _ </callGas>
          <program> sumToN </program>
          <jumpDests> #computeValidJumpDests(sumToN) </jumpDests>
          <pc>  3 => 21                         </pc>
          <gas> G => G -Int (52 *Int I +Int 21) </gas>
          <wordStack> I : S                               : WS
                   => 0 : S +Int I *Int (I +Int 1) divInt 2 : WS </wordStack>
      requires I >=Int 0
       andBool S >=Int 0
       andBool S +Int I *Int (I +Int 1) divInt 2 <Int pow256
       andBool #sizeWordStack(WS) <Int 1021
       andBool G >=Int 52 *Int I +Int 21
      [circularity]

endmodule
