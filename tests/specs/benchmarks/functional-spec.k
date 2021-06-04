requires "verification.k"

module FUNCTIONAL-SPEC-SYNTAX
    imports VERIFICATION

    syntax KItem ::= runLemma ( Step ) | doneLemma ( Step )
 // -------------------------------------------------------
    rule <k> runLemma(S) => doneLemma(S) ... </k>

    syntax Step ::= ByteArray
 // -------------------------

endmodule

module FUNCTIONAL-SPEC
    imports FUNCTIONAL-SPEC-SYNTAX

    claim <k> runLemma(#encodeArgs(#bytes32(keccak(1 : #encodeArgs(#uint256(A0)))))) => doneLemma(#buf(32, keccak(#buf(1,1) ++ #buf(32, A0)))) ... </k> requires #rangeUInt(256, A0)

    claim <k> runLemma(#buf(32, maxUInt256 &Int keccak(#buf(32, maxUInt256 &Int A0) ++ #buf(32, maxUInt256 &Int A1))))
           => doneLemma(#buf(32, keccak(#buf(32,A0) ++ #buf(32,A1))))
          </k>
      requires #rangeUInt(256, A0)
       andBool #rangeUInt(256, A1)
endmodule
