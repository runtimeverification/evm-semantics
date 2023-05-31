requires "verification.k"

module FUNCTIONAL-SPEC-SYNTAX
    imports VERIFICATION
// 
//     syntax KItem ::= runLemma ( Step ) | doneLemma ( Step )
//  // -------------------------------------------------------
//     rule <k> runLemma(S) => doneLemma(S) ... </k>
// 
//     syntax Step ::= Int
//  // -------------------

endmodule

module FUNCTIONAL-SPEC
    imports FUNCTIONAL-SPEC-SYNTAX

    claim (#hashedLocation("Solidity", 2, OWNER SPENDER .IntList))
           => (keccak(#bufStrict(32, SPENDER) +Bytes #bufStrict(32, keccak(#bufStrict(32, OWNER) +Bytes #bufStrict(32, 2)))))
      requires #rangeUInt(256, SPENDER) andBool #rangeUInt(256, OWNER)
endmodule
