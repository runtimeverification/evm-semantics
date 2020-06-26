requires "abstract-semantics-segmented-gas.k"
requires "edsl.md"
requires "evm-symbolic.k"
requires "../lemmas.k"

module VERIFICATION
    imports VERIFICATION-JAVA
    imports VERIFICATION-HASKELL
    imports LEMMAS

endmodule

module VERIFICATION-JAVA [symbolic, kast]
    imports ABSTRACT-SEMANTICS-SEGMENTED-GAS
    imports EDSL
    imports EVM-SYMBOLIC

    //semantics of #buf
    rule #buf(LEN, BYTES) => #padToWidth(LEN, #asByteStack( BYTES )) [concrete]

    rule chop ( W0:Int +Int W1:Int ) -Word W1:Int => chop ( W0 )
      requires #rangeUInt(256, W0) andBool #rangeUInt(256, W1)
endmodule

module VERIFICATION-HASKELL [symbolic, kore]

    // only to pass the haskell dry-run tests
    syntax Int ::= #gas ( Int , Int , Int )  [function]  // startGas, nonMemory, memory
  //-----------------------------------------------------------------------------------

endmodule
