requires "../lemmas.k"
requires "bin_runtime.k"
requires "storage.k"

module HASKELL-HASH2 [symbolic, kore]
    imports EDSL

    syntax Int ::= hash2(Int, Int) [function]
 // -----------------------------------------
endmodule

module VERIFICATION
    imports LEMMAS
    imports DSS-BIN-RUNTIME
    imports DSS-STORAGE
    imports HASKELL-HASH2

    syntax Bool ::= #notPrecompileAddress ( Int ) [function]
 // --------------------------------------------------------
    rule #notPrecompileAddress ( X ) => 0 ==Int X orBool (10 <=Int X andBool #rangeAddress(X))

    syntax Bool ::= #rangeBool ( Int )
 // ----------------------------------
    rule #rangeBool(X) => X ==Int 0 orBool X ==Int 1 [macro]

    syntax Int ::= "pow208"
 // -----------------------
    rule pow208 => 411376139330301510538742295639337626245683966408394965837152256 [macro]

    syntax Int ::= #WordPackUInt48UInt48     (       Int , Int ) [function]
                 | #WordPackAddrUInt8        (       Int , Int ) [function]
                 | #WordPackAddrUInt48UInt48 ( Int , Int , Int ) [function]
 // -----------------------------------------------------------------------
    rule #WordPackUInt48UInt48     (     X , Y ) => Y *Int pow48  +Int X                    requires #rangeUInt(48, X) andBool #rangeUInt(48, Y)
    rule #WordPackAddrUInt8        (     X , Y ) => Y *Int pow160 +Int X                    requires #rangeAddress(X)  andBool #rangeUInt(8, Y)
    rule #WordPackAddrUInt48UInt48 ( A , X , Y ) => Y *Int pow208 +Int X *Int pow160 +Int A requires #rangeAddress(A)  andBool #rangeUInt(48, X) andBool #rangeUInt(48, Y)

    syntax Int ::= #string2Word ( String ) [function]
 // -------------------------------------------------
    rule #string2Word(S) => #asWord(#padRightToWidth(32, #parseByteStackRaw(S)))

    // in binary: 100 1s followed by 160 0s
    syntax Int ::= "notAddrMask"
 // ----------------------------
    rule notAddrMask => 115792089237316195423570985007226406215939081747436879206741300988257197096960 [macro]

    // ### vat-move-diff

    rule (W0 : WS) [ 0     .. WIDTH ] => W0 : (WS [ 0 .. WIDTH -Int 1 ]) requires 0 <Int WIDTH
    rule (_  : WS) [ START .. WIDTH ] => WS [ START -Int 1 .. WIDTH ]    requires 0 <Int START

    rule #asWord(WS) >>Int M => #asWord(WS [ 0 .. #sizeByteArray(WS) -Int (M /Int 8) ]) requires 0 <=Int M andBool M modInt 8 ==Int 0

    rule hash2(V1, _) ==K hash2(V2, _) => false requires V1 =/=Int V2

    // ### cat-exhaustiveness

    rule #sizeByteArray(_WS [ START .. WIDTH ]) => WIDTH requires 0 <=Int START andBool 0 <=Int WIDTH

    rule WS [ START .. WIDTH ] [ 0 .. WIDTH' ]  => WS [ START .. WIDTH' ] requires WIDTH' <=Int WIDTH

    // ### cat-file-addr-pass-rough

    rule notAddrMask &Int ADDR => 0 requires #rangeAddress(ADDR)

endmodule
