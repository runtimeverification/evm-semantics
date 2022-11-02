requires "edsl.md"
requires "evm-symbolic.k"
requires "lemmas/lemmas.k"

module VERIFICATION
    imports VERIFICATION-JAVA
    imports VERIFICATION-HASKELL
    imports LEMMAS

endmodule

module VERIFICATION-JAVA [symbolic, kast]
    imports EDSL
    imports EVM-SYMBOLIC

  // ########################
  // Buffer Reasoning
  // ########################

    //semantics of #buf
    rule #buf(LEN, BYTES) => #padToWidth(LEN, #asByteStack( BYTES )) [simplification, concrete]

    rule chop ( W0:Int +Int W1:Int ) -Word W1:Int => chop ( W0 )  requires #rangeUInt(256, W0) andBool #rangeUInt(256, W1) [simplification]

endmodule

module VERIFICATION-HASKELL [symbolic, kore]
    imports EDSL
endmodule
