requires "../lemmas.k"
requires "bin_runtime.k"
requires "storage.k"

module HASKELL-HASH2 [symbolic, kore]
    imports INT

    syntax Int ::= hash2 ( Int , Int ) [function]
 // ---------------------------------------------
endmodule

module VERIFICATION-SYNTAX
    imports LEMMAS
    imports DSS-BIN-RUNTIME
    imports DSS-STORAGE
    imports HASKELL-HASH2

    syntax Bool ::= #notPrecompileAddress ( Int ) [function]
 // --------------------------------------------------------
    rule #notPrecompileAddress ( X ) => 0 ==Int X orBool (10 <=Int X andBool #rangeAddress(X))

    syntax Int ::= "pow208"
 // -----------------------
    rule pow208 => 411376139330301510538742295639337626245683966408394965837152256 [macro]

    syntax Int ::= #WordPackUInt48UInt48     (       Int , Int ) [function, no-evaluators, smtlib(WordPackUInt48UInt48)]
                 | #WordPackAddrUInt48UInt48 ( Int , Int , Int ) [function, no-evaluators, smtlib(WordPackAddrUInt48UInt48)]
                 | #WordPackAddrUInt8        (       Int , Int ) [function, no-evaluators, smtlib(WordPackAddrUInt8)]
 // -----------------------------------------------------------------------------------------------------------------
    // rule #WordPackUInt48UInt48     (            UINT48_1 , UINT48_2 ) => UINT48_2 *Int pow48 +Int UINT48_1                        requires #rangeUInt(48, UINT48_1) andBool #rangeUInt(48, UINT48_2)
    // rule #WordPackAddrUInt48UInt48 (     ADDR , UINT48_1 , UINT48_2 ) => UINT48_2 *Int pow208 +Int UINT48_1 *Int pow160 +Int ADDR requires #rangeAddress(ADDR) andBool #rangeUInt(48, UINT48_1) andBool #rangeUInt(48, UINT48_2)
    // rule #WordPackAddrUInt8        (     ADDR , UINT8               ) => UINT8 *Int pow160 +Int ADDR                              requires #rangeAddress(ADDR) andBool #rangeUInt(8, UINT_8)

    rule maxUInt48 &Int  UINT48_UINT48             => UINT48_1 requires UINT48_UINT48 ==Int #WordPackUInt48UInt48(UINT48_1, UINT48_2) andBool #rangeUInt(48, UINT48_1) andBool #rangeUInt(48, UINT48_2) [smt-lemma]
    rule maxUInt48 &Int (UINT48_UINT48 /Int pow48) => UINT48_2 requires UINT48_UINT48 ==Int #WordPackUInt48UInt48(UINT48_1, UINT48_2) andBool #rangeUInt(48, UINT48_1) andBool #rangeUInt(48, UINT48_2) [smt-lemma]

    rule maxUInt160 &Int  ADDR_UINT48_UINT48              => ADDR     requires ADDR_UINT48_UINT48 ==Int #WordPackAddrUInt48UInt48(ADDR, UINT48_1, UINT48_2) andBool #rangeAddress(ADDR) andBool #rangeUInt(48, UINT48_1) andBool #rangeUInt(48, UINT48_2) [smt-lemma]
    rule maxUInt48  &Int (ADDR_UINT48_UINT48 /Int pow160) => UINT48_1 requires ADDR_UINT48_UINT48 ==Int #WordPackAddrUInt48UInt48(ADDR, UINT48_1, UINT48_2) andBool #rangeAddress(ADDR) andBool #rangeUInt(48, UINT48_1) andBool #rangeUInt(48, UINT48_2) [smt-lemma]
    rule maxUInt48  &Int (ADDR_UINT48_UINT48 /Int pow208) => UINT48_2 requires ADDR_UINT48_UINT48 ==Int #WordPackAddrUInt48UInt48(ADDR, UINT48_1, UINT48_2) andBool #rangeAddress(ADDR) andBool #rangeUInt(48, UINT48_1) andBool #rangeUInt(48, UINT48_2) [smt-lemma]

    rule maxUInt160 &Int  ADDR_UINT8              => ADDR  requires ADDR_UINT8 ==Int #WordPackAddrUInt8(ADDR, UINT8) andBool #rangeAddress(ADDR) andBool #rangeUInt(8, UINT8) [smt-lemma]
    rule maxUInt8   &Int (ADDR_UINT8 /Int pow160) => UINT8 requires ADDR_UINT8 ==Int #WordPackAddrUInt8(ADDR, UINT8) andBool #rangeAddress(ADDR) andBool #rangeUInt(8, UINT8) [smt-lemma]

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

    rule chop(N +Int M) <Int N => true requires #rangeUInt(256, N) andBool #rangeUInt(256, M) andBool notBool #rangeUInt(256, N +Int M)

    // ### dsvalue-read-pass

    rule M [ K <- V ] => M requires #lookup(M, K) ==Int V

    // ### cat-ilks-pass

    // This lemma is considered "safe enough" because `hash2` is a hash function over a large range and is very unlikely to overflow.
    // Note that this case comes from a solidity struct being accessed (hence the integer offsets), so it's an assumption built into the Solidity compiler anyway.
    rule chop(hash2(I1, I2) +Int N) => hash2(I1, I2) +Int N requires 0 <=Int N andBool N <Int 3

    rule ( BA1:ByteArray ++ BA2:ByteArray ) ++ BA3:ByteArray => BA1 ++ ( BA2 ++ BA3 )

endmodule
