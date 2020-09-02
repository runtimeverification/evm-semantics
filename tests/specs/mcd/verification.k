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

    syntax Int ::= #unsigned ( Int ) [function, smtlib(unsigned)]
 // -------------------------------------------------------------
    rule #unsigned(DATA) => DATA             requires 0 <=Int DATA andBool DATA <=Int maxSInt256
    rule #unsigned(DATA) => pow256 +Int DATA requires minSInt256 <=Int DATA andBool DATA <Int 0

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

    // ### vat-addui-fail-rough

    rule #rangeUInt(256, #unsigned(X)) => true requires #rangeSInt(256, X) [smt-lemma]

    // Proof (remembering that sgn(0) ==Int 1 and using the rules for _s<Word_ and _<Word_):
    // X s<Word 0
    //      case sgn(X) ==Int  1 : X <Word 0 => bool2Word(false) (because #rangeUInt(256, X))
    //      case sgn(X) ==Int -1 : bool2Word(true)
    // 0 s<Word X
    //      case sgn(X) ==Int  1 : 0 <Word X
    //      case sgn(X) ==Int -1 : bool2Word(false)
    rule X s<Word 0 => bool2Word(sgn(X) ==Int -1)                  requires #rangeUInt(256, X)
    rule 0 s<Word X => bool2Word(sgn(X) ==Int  1 andBool 0 <Int X) requires #rangeUInt(256, X)

    rule sgn(#unsigned(X)) ==Int  1 => 0 <=Int X andBool X <=Int maxSInt256 requires #rangeSInt(256, X)
    rule sgn(#unsigned(X)) ==Int -1 => minSInt256 <=Int X andBool X <Int 0  requires #rangeSInt(256, X)

    // property of 2s complement
    rule notBool (0 <=Int X +Int Y) => X <Int chop(X +Int #unsigned(Y)) requires #rangeUInt(256, X) andBool #rangeSInt(256, Y) [smt-lemma]

    // ### vat-mului-fail-rough

    rule #unsigned(Y) ==K 0 => Y ==K 0 requires #rangeSInt(256, Y) [smt-lemma]
    rule       abs(Y) ==K 0 => Y ==K 0 requires #rangeUInt(256, Y) [smt-lemma]

    // Proof:
    // case sgn(#unsigned(Y)) ==Int 1                   // #unsigned(Y) ==Int Y andBool 0 <=Int Y
    //      chop(X *Int #unsigned(Y))
    //   => chop(X *Int Y)                              // #unsigned(Y) ==Int Y
    // case sgn(#unsigned(Y)) ==Int -1                  // #unsigned(Y) ==Int Y +Int pow256 andBool Y <Int 0
    //      chop(X *Int #unsigned(Y))
    //   => chop(X *Int (Y +Int pow256))                // #unsigned(Y) ==Int Y +Int pow256
    //   => chop(X *Int Y +Int X *Int pow256)
    //   => chop((X *Int Y) +Int chop(X *Int pow256))
    //   => chop(X *Int Y)
    rule chop(X *Int #unsigned(Y)) => chop(X *Int Y) requires #rangeSInt(256, Y)

    // Proof:
    // case sgn(#unsigned(Y)) ==Int 1                           // 0 <=Int Y andBool #unsigned(Y) ==Int Y
    //      sgn(chop(X *Int Y)) *Int sgn(#unsigned(Y))
    //   => sgn(X *Int Y) *Int sgn(Y)                           // 0 <=Int X andBool 0 <=Int Y andBool #rangeSInt(256, X *Int Y) andBool #unsigned(Y) ==Int Y
    //   => 1 *Int 1                                            // 0 <=Int X *Int Y andBool #rangeSInt(256, X *Int Y)
    //   => 1
    // case sgn(#unsigned(Y)) ==Int -1                          // Y <Int 0 andBool #unsigned(Y) ==Int Y +Int pow256
    //      sgn(chop(X *Int Y)) *Int sgn(#unsigned(Y))
    //   => sgn(X *Int Y +Int pow256) *Int sgn(Y +Int pow256)   // 0 <=Int X andBool Y <Int 0 andBool #rangeSInt(256, X *Int Y) andBool #unsigned(Y) ==Int Y +Int pow256
    //   => -1 *Int -1                                          // X *Int Y <Int 0 andBool #rangeSInt(256, X *Int Y) andBool Y <Int andBool #rangeSInt(256, Y)
    //   => 1
    rule sgn(chop(X *Int Y)) *Int sgn(#unsigned(Y)) => 1 requires #rangeUInt(256, X) andBool #rangeSInt(256, Y) andBool #rangeSInt(256, X *Int Y)

    // Proof (assuming Y =/=Int 0):
    // case sgn(#unsigned(Y)) ==Int 1                                                   // 0 <=Int Y andBool #unsigned(Y) ==Int Y
    //      abs(chop(X *Int Y)) /Int abs(#unsigned(Y))
    //      abs(X *Int Y) /Int abs(Y)                                                   // #rangeSInt(256, Y) andBool #unsigned(Y) ==Int Y
    //      X *Int Y /Int Y                                                             // #rangeSInt(256, X *Int Y) andBool 0 <=Int X *Int Y andBool #rangeSInt(256, Y) andBool 0 <=Int Y
    //      X
    // case sgn(#unsigned(Y)) ==Int -1                                                  // Y <Int 0 andBool #unsigned(Y) ==Int Y +Int pow256
    //      abs(chop(X *Int Y)) /Int abs(#unsigned(Y))
    //   => abs(X *Int Y +Int pow256) /Int abs(Y +Int pow256)                           // #rangeSInt(256, X *Int Y) andBool #unsigned(Y) ==Int Y +Int pow256
    //   => (0 -Word (X *Int Y +Int pow256)) /Int (0 -Word (Y +Int pow256))             // #rangeSInt(256, X *Int Y) andBool X *Int Y <Int 0 andBool #rangeSInt(256, Y) andBool Y <Int 0
    //   => (pow256 -Int (X *Int Y +Int pow256)) /Int (pow256 -Int (Y +Int pow256))     // 0 <Int (X *Int Y +Int pow256) andBool 0 <Int (Y +Int pow256)
    //   => (X *Int Y) /Int Y
    //   => X
    rule abs(chop(X *Int Y)) /Int abs(#unsigned(Y)) => X requires #rangeUInt(256, X) andBool #rangeSInt(256, Y) andBool #rangeSInt(256, X *Int Y) andBool Y =/=Int 0

    rule #unsigned(Y) ==K chop(Y) => true requires #rangeSInt(256, Y) [smt-lemma]

endmodule
