requires "edsl.k"

module EDSL-STATIC-ARRAY
    imports EDSL

    syntax ByteArray ::= #abiCallData2 ( String , TypedArgs ) [function]

    rule #abiCallData2( FSIG , ARGS )
      => #parseByteStack(substrString(Keccak256(FSIG), 0, 8))
      ++ #encodeArgs(ARGS)

    rule chop(I) => 0 requires I ==Int pow256

endmodule

