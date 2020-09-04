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

    // ### vat-addui-fail-rough

    // Proof:
    // case sgn(X) ==Int  1
    //      X s<Word 0
    //   => X <Word 0           // sgn(X) ==Int 1 andBool sgn(0) ==Int 1
    //   => bool2Word(false)    // #rangeUInt(256, X)
    // case sgn(X) ==Int -1
    //      X s<Word 0
    //   => bool2Word(true)     // sgn(X) ==Int -1 andBool sgn(0) ==Int 1
    //
    // Via Z3 4.8.7:
    // ; 2^256
    // (declare-const pow256 Int)
    // (assert (= pow256 115792089237316195423570985008687907853269984665640564039457584007913129639936))
    //
    // ; 2^255
    // (declare-const pow255 Int)
    // (assert (= pow255 57896044618658097711785492504343953926634992332820282019728792003956564819968))
    //
    // ; sgn
    // (declare-fun sgn (Int) Int)
    // (assert (forall ((x Int)) (=> (and (>= x 0)      (< x pow255)) (= (sgn x)  1))))
    // (assert (forall ((x Int)) (=> (and (>= x pow255) (< x pow256)) (= (sgn x) -1))))
    //
    // ; s<Word
    // (declare-fun slt (Int Int) Bool)
    // (assert (forall ((x Int) (y Int)) (=> (and (= (sgn x)  1) (= (sgn y)  1)) (= (slt x y) (< x y)))))
    // (assert (forall ((x Int) (y Int)) (=> (and (= (sgn x)  1) (= (sgn y) -1)) (= (slt x y) false))))
    // (assert (forall ((x Int) (y Int)) (=> (and (= (sgn x) -1) (= (sgn y)  1)) (= (slt x y) true))))
    // (assert (forall ((x Int) (y Int)) (=> (and (= (sgn x) -1) (= (sgn y) -1)) (= (slt x y) (> x y)))))
    //
    // ;;;; proof
    //
    // ; uint256
    // (declare-const x Int)
    // (assert (and (>= x 0) (< x pow256)))
    //
    // (assert (not
    //     (= (slt x 0) (= (sgn x) -1))
    // ))
    // (check-sat)
    rule X s<Word 0 => bool2Word(sgn(X) ==Int -1) requires #rangeUInt(256, X)

    rule sgn(chop(X)) ==Int -1 => X <Int 0 requires #rangeSInt(256, X)

    // ### vat-mului-pass

    rule chop(X *Int chop(Y)) => chop(X *Int Y)

    // Proof #rangUInt(256, X) andBool #rangeSInt(256, Y) andBool #rangeSInt(256, X *Int Y) andBool Y =/=Int 0
    //      chop(X *Int Y) /sWord chop(Y)
    //   => #sgnInterp(sgn(chop(X *Int Y)) *Int sgn(chop(Y)), abs(chop(X *Int Y)) /Word abs(chop(Y)))
    // Focus: sgn(chop(X *Int Y)) *Int sgn(chop(Y))
    //      case 0 <=Int chop(Y)
    //           sgn(chop(X *Int Y)) *Int sgn(chop(Y))
    //        => sgn(chop(X *Int Y)) *Int sgn(Y)                     // chop(Y) ==Int Y
    //        => sgn(X *Int Y) *Int sgn(Y)                           // 0 <=Int X andBool 0 <=Int Y
    //        => 1 *Int 1                                            // 0 <=Int X *Int Y andBool 0 <=Int Y
    //        => 1
    //      case Y <Int 0
    //           sgn(chop(X *Int Y)) *Int sgn(chop(Y))
    //        => sgn(X *Int Y +Int pow256) *Int sgn(Y +Int pow256)   // chop(Y) ==Int Y +Int pow256
    //        => -1 *Int -1                                          // X *Int Y <Int 0 andBool Y <Int 0
    //        => 1
    // Focus: abs(chop(X *Int Y)) /Word abs(chop(Y))
    //      case 0 <=Int Y
    //           abs(chop(X *Int Y)) /Word abs(chop(Y))
    //        => abs(chop(X *Int Y)) /Int  abs(chop(Y))
    //        => abs(X *Int Y) /Int abs(Y)                                                   // 0 <=Int X andBool 0 <=Int Y andBool #rangeSigne andBool chop(Y) ==Int Y
    //        => X *Int Y /Int Y                                                             // #rangeSInt(256, X *Int Y) andBool 0 <=Int X *Int Y andBool #rangeSInt(256, Y) andBool 0 <=Int Y
    //        => X
    //      case Y <Int 0
    //           abs(chop(X *Int Y)) /Int abs(chop(Y))
    //        => abs(X *Int Y +Int pow256) /Int abs(Y +Int pow256)                           // #rangeSInt(256, X *Int Y) andBool chop(Y) ==Int Y +Int pow256
    //        => (0 -Word (X *Int Y +Int pow256)) /Int (0 -Word (Y +Int pow256))             // #rangeSInt(256, X *Int Y) andBool X *Int Y <Int 0 andBool #rangeSInt(256, Y) andBool Y <Int 0
    //        => (pow256 -Int (X *Int Y +Int pow256)) /Int (pow256 -Int (Y +Int pow256))     // 0 <Int (X *Int Y +Int pow256) andBool 0 <Int (Y +Int pow256)
    //        => (X *Int Y) /Int Y
    //        => X
    //
    // Via Z3 ?.?.?:
    // ; 2^6 and 2^5 instead of 2^256 and 2^255 for small model proof
    // (declare-const pow256 Int)
    // (assert (= pow256 64))
    // (declare-const pow255 Int)
    // (assert (= pow255 32))
    //
    // ; sgn
    // (declare-fun sgn (Int) Int)
    // (assert (forall ((x Int)) (=> (and (>= x 0)      (< x pow255)) (= (sgn x)  1))))
    // (assert (forall ((x Int)) (=> (and (>= x pow255) (< x pow256)) (= (sgn x) -1))))
    //
    // ; s<Word
    // (declare-fun slt (Int Int) Bool)
    // (assert (forall ((x Int) (y Int)) (=> (and (= (sgn x)  1) (= (sgn y)  1)) (= (slt x y) (< x y)))))
    // (assert (forall ((x Int) (y Int)) (=> (and (= (sgn x)  1) (= (sgn y) -1)) (= (slt x y) false))))
    // (assert (forall ((x Int) (y Int)) (=> (and (= (sgn x) -1) (= (sgn y)  1)) (= (slt x y) true))))
    // (assert (forall ((x Int) (y Int)) (=> (and (= (sgn x) -1) (= (sgn y) -1)) (= (slt x y) (> x y)))))
    //
    // ; chop
    // (define-fun chop ((x Int)) Int (mod x pow256))
    //
    // ; /Word
    // ;(define-fun zdiv ((x Int) (y Int)) Int (ite (= y 0) 0 (div x y)))
    // (define-fun zdiv ((x Int) (y Int)) Int (div x y)) ; y is non-zero in the query below
    //
    // ; /sWord
    // (declare-fun sdiv (Int Int) Int)
    // (assert (forall ((x Int) (y Int)) (=> (> (* (sgn x) (sgn y)) 0) (= (sdiv x y)    (zdiv (abs x) (abs y)) ))))
    // (assert (forall ((x Int) (y Int)) (=> (< (* (sgn x) (sgn y)) 0) (= (sdiv x y) (- (zdiv (abs x) (abs y)))))))
    //
    // ; uint256
    // (define-fun uint256 ((x Int)) Bool (and (>= x 0) (< x pow256)))
    //
    // ; sint256
    // (define-fun sint256 ((x Int)) Bool (and (>= x (- pow255)) (< x pow255)))
    //
    // ;;;; proof
    //
    // (declare-const x Int)
    // (declare-const y Int)
    //
    // (assert (uint256 x))
    // (assert (sint256 y))
    // (assert (sint256 (* x y)))
    // (assert (not (= y 0)))
    //
    // (assert (not
    //     (= (sdiv (chop (* x y)) (chop y)) x)
    // ))
    // (check-sat)
    rule chop(X *Int Y) /sWord chop(Y) => X requires #rangeUInt(256, X) andBool #rangeSInt(256, Y) andBool #rangeSInt(256, X *Int Y) andBool Y =/=Int 0

endmodule
