module ADD1-SPEC
    import ETHEREUM-SIMULATION
    rule <memoryUsed> 0 =>1  </memoryUsed>
         <gas> N =>N1 </gas>
         <program> #asMapOpCodes(
                 PUSH(0, 0); PUSH(0, 0); MSTORE; PUSH (0,I) ; DUP(1);
                 PUSH(0, 0); MSTORE; JUMPDEST; PUSH(0, 1) ;  SWAP(1); SUB;
                 DUP(1); DUP(1);  PUSH(0, 0); MLOAD; ADD ;
                 PUSH(0, 0); MSTORE; PUSH(0, 7); JUMPI;
             .OpCodes)
         </program>
    requires true
    ensures true
endmodule
