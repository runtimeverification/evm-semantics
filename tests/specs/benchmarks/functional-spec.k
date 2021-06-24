requires "verification.k"

module FUNCTIONAL-SPEC-SYNTAX
    imports VERIFICATION

    syntax KItem ::= runLemma ( Step ) | doneLemma ( Step )
 // -------------------------------------------------------
    rule <k> runLemma(S) => doneLemma(S) ... </k>

    syntax Step ::= ByteArray | Int | Bool
 // --------------------------------------

endmodule

module FUNCTIONAL-SPEC
    imports FUNCTIONAL-SPEC-SYNTAX

    claim <k> runLemma(#encodeArgs(#bytes32(keccak(1 : #encodeArgs(#uint256(A0)))))) => doneLemma(#buf(32, keccak(#buf(1,1) ++ #buf(32, A0)))) ... </k> requires #rangeUInt(256, A0)

    claim <k> runLemma(#buf(32, maxUInt256 &Int keccak(#buf(32, maxUInt256 &Int A0) ++ #buf(32, maxUInt256 &Int A1))))
           => doneLemma(#buf(32, keccak(#buf(32,A0) ++ #buf(32,A1)))) ... </k>
      requires #rangeUInt(256, A0)
       andBool #rangeUInt(256, A1)

    claim <k> runLemma(       chop( #ceil32(DATA_LEN) +Int 64 )          ) => doneLemma ( #ceil32(DATA_LEN) +Int 64 ) ... </k> requires #range(0 <= DATA_LEN < pow16)
    claim <k> runLemma( chop( chop( #ceil32(DATA_LEN) +Int 64 ) +Int 4 ) ) => doneLemma ( #ceil32(DATA_LEN) +Int 68 ) ... </k> requires #range(0 <= DATA_LEN < pow16)

    claim <k> runLemma(#ceil32(DATA_LEN) +Int 292 <Int DATA_LEN +Int 292) => doneLemma(false) ... </k> requires #range(0 <= DATA_LEN < pow16)

    // from tests/specs/benchmarks/bytes00-spec.k and tests/specs/benchmarks/keccak00-spec.k
    claim <k> runLemma  ( (#buf(DATA_LEN, DATA) ++ _BUF) [0 .. DATA_LEN] ) 
           => doneLemma (  #buf(DATA_LEN, DATA)          [0 .. DATA_LEN] ) ... </k>
      requires #range(0 <= DATA < (2 ^Int (DATA_LEN *Int 8)))
       andBool 0 <=Int DATA_LEN

endmodule
