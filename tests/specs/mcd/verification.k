requires "../lemmas.k"
requires "bin_runtime.k"
requires "storage.k"

module HASKELL-HASH2 [symbolic, kore]
    imports INT

    syntax Int ::= hash2(Int, Int) [function]
 // -----------------------------------------
endmodule

module VERIFICATION-SYNTAX
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

    syntax Int ::= "#Wad" | "#Ray" | "#Rad"
 // ---------------------------------------
    rule #Wad => 1000000000000000000                            [macro]
    rule #Ray => 1000000000000000000000000000                   [macro]
    rule #Rad => 1000000000000000000000000000000000000000000000 [macro]

    syntax ByteArray ::= #asByteStackInWidth    ( Int, Int )                 [function]
                       | #asByteStackInWidthaux ( Int, Int, Int, ByteArray ) [function]
 // -----------------------------------------------------------------------------------
    rule #asByteStackInWidth(X, N) => #asByteStackInWidthaux(X, N -Int 1, N, .ByteArray)

    rule #asByteStackInWidthaux(X, I, N, WS) => #asByteStackInWidthaux(X, I -Int 1, N, nthbyteof(X, I, N) : WS) when I >Int 0
    rule #asByteStackInWidthaux(X, 0, N, WS) => nthbyteof(X, 0, N) : WS

    syntax Int ::= nthbyteof ( Int , Int , Int ) [function, smtlib(smt_nthbyteof), proj]
 // ------------------------------------------------------------------------------------
    rule nthbyteof(V, I, N) => nthbyteof(V /Int 256, I, N -Int 1) when N  >Int (I +Int 1) [concrete]
    rule nthbyteof(V, I, N) =>           V modInt 256             when N ==Int (I +Int 1) [concrete]

endmodule

module VERIFICATION
    imports VERIFICATION-SYNTAX

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

    // ### PERFORMANCE: dai-adduu-fail-rough
    // 99s -> 48s

    rule #sizeWordStack(WS, N) => #sizeWordStack(WS, 0) +Int N requires N =/=Int 0

    // ### PERFORMANCE: vat-deny-diff-fail-rough
    // 27.21m -> 3.16m

    rule M:Memory [ K := (W : WS) ]                   => M [ K <- W ] [ K +Int 1 := WS ] requires 0 <=Int K
    rule M:Memory [ K <- V ] [ K' <- V' ]             => M [ K' <- V' ] [ K <- V ]       requires K' <Int K
    rule M:Memory [ K := BUF:ByteArray ] [ K' <- V' ] => M [ K' <- V' ] [ K := BUF ]     requires K' <Int K orBool K +Int #sizeByteArray(BUF) <=Int K'

    // ### dstoken-transferfrom-fail-rough

    rule hash2(_, hash2(_, _)) ==K hash2(_, N) => false requires N <=Int 10

    rule chop(N +Int M) <Int N => true requires #rangeUInt(256, N) andBool #rangeUInt(256, M) andBool notBool #rangeUInt(256, N +Int M)

    // ### dsvalue-read-pass

    rule M [ K <- V ] => M requires #lookup(M, K) ==Int V

    // ### cat-ilks-pass

    rule chop(hash2(I, I') +Int N) => hash2(I, I') +Int N requires N <Int 3

    rule hash2(_, _) +Int N ==K hash2(_, _) +Int M => false requires N =/=Int M
    rule hash2(_, _)        ==K hash2(_, _) +Int M => false requires 0 =/=Int M

    rule ( BA1:ByteArray ++ BA2:ByteArray ) ++ BA3:ByteArray => BA1 ++ ( BA2 ++ BA3 )

    // ### flipper-ttl-pass/flipper-tau-pass

    rule X ==Int #WordPackUInt48UInt48(Y, Z) => (maxUInt48 &Int X ==Int Y) andBool (maxUInt48 &Int (X /Int pow48) ==Int Z)
      requires #rangeUInt(48, Y) andBool #rangeUInt(48, Z)

endmodule
