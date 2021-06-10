requires "verification.k"

module FUNCTIONAL-SPEC-SYNTAX
    imports VERIFICATION

    syntax KItem ::= runLemma ( Step ) | doneLemma ( Step )
 // -------------------------------------------------------
    rule <k> runLemma(S) => doneLemma(S) ... </k>

    syntax Step ::= Int
 // -------------------------

endmodule

module FUNCTIONAL-SPEC
    imports FUNCTIONAL-SPEC-SYNTAX

    claim <k> runLemma(#hashedLocation("Solidity", keccakIntList(OWNER 2 .IntList), SPENDER .IntList))
           => doneLemma(keccak(#buf(32, SPENDER) ++ #buf(32, keccak(#buf(32, OWNER) ++ #buf(32, 2))))) ... </k>
      requires #rangeUInt(256, SPENDER) andBool #rangeUInt(256, OWNER)
endmodule
