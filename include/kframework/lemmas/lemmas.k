requires "evm.md"
requires "buf.md"
requires "int-simplification.k"

module LEMMAS [symbolic]
    imports INT-SIMPLIFICATION
    imports LEMMAS-JAVA
    imports LEMMAS-HASKELL

  // ########################
  // Arithmetic
  // ########################

    // For #bufStrict simplification in benchmarks
    rule 0 <=Int #ceil32(I)        => true requires 0 <=Int I [simplification, smt-lemma]
    rule 0 <=Int #ceil32(I) -Int I => true requires 0 <=Int I [simplification]

    // chop range & simplification
    rule chop(I) => I requires #rangeUInt( 256 , I ) [simplification]
    rule 0 <=Int chop(_V)             => true        [simplification, smt-lemma]
    rule         chop(_V) <Int pow256 => true        [simplification]

    rule chop ( ( maxUInt48 &Int X:Int ) *Int Y:Int ) => ( maxUInt48 &Int X:Int ) *Int Y
      requires 0 <=Int X andBool 0 <=Int Y andBool Y <=Int pow208 [simplification]

    rule maxUInt8   &Int X <Int 256    => true requires 0 <=Int X [simplification, smt-lemma]
    rule maxUInt48  &Int X <Int pow48  => true requires 0 <=Int X [simplification, smt-lemma]
    rule maxUInt160 &Int X <Int pow160 => true requires 0 <=Int X [simplification, smt-lemma]

  // ########################
  // Set Reasoning
  // ########################

    rule X in (SetItem(Y) _   ) => true      requires X  ==Int Y [simplification]
    rule X in (SetItem(Y) REST) => X in REST requires X =/=Int Y [simplification]

  // ########################
  // Word Reasoning
  // ########################

    rule 0 <=Int #sizeWordStack ( _ , N ) => true requires 0 <=Int N [simplification, smt-lemma]
    rule 0 <=Int #sizeByteArray ( _ )     => true                    [simplification, smt-lemma]

    // bool2Word range & simplification
    rule 0 <=Int bool2Word(_B)             => true   [simplification]
    rule         bool2Word(_B) <Int pow256 => true   [simplification]

    rule notBool notBool B => B [simplification]

    // #newAddr range
    rule 0 <=Int #newAddr(_,_)             => true   [simplification]
    rule         #newAddr(_,_) <Int pow160 => true   [simplification]
    rule         #newAddr(_,_) <Int pow256 => true   [simplification]

    rule #isPrecompiledAccount(#newAddr(_, _), _) => false [simplification]

    rule 0 <=Int #asWord(_WS)             => true [simplification]
    rule         #asWord(_WS) <Int pow256 => true [simplification]

  // ########################
  // Keccak
  // ########################

    //Required for #Ceil(#buf)
    rule 0 <=Int keccak( _ )             => true [simplification]
    rule         keccak( _ ) <Int pow256 => true [simplification]

  // ########################
  // Buffer Reasoning
  // ########################

    rule WS         ++ .ByteArray => WS  [simplification]
    rule .ByteArray ++ WS         => WS  [simplification]

    // #range

    rule #range(_, _, K) =>
         .ByteArray
      requires K <=Int 0 [simplification]

    rule #range(M [ N := BUF:ByteArray ], L, K) =>
         #let W = minInt(K, N -Int L) #in #range(M, L, W) ++ #range(M [ N := BUF ], N, K -Int W)
      requires 0 <Int K andBool L <Int N [simplification]

    rule #range(M [ N := BUF:ByteArray ], L, K) =>
           #let S = L -Int N #in
           #let W = minInt(K, #sizeByteArray(BUF) -Int S) #in
           BUF [ S .. W ] ++ #range(M, N +Int #sizeByteArray(BUF), K -Int W)
      requires 0 <Int K andBool N <=Int L andBool L <=Int N +Int #sizeByteArray(BUF) [simplification]

    rule #range(M [ N := BUF:ByteArray ], L, K) => #range(M, L, K)
      requires 0 <Int K andBool N +Int #sizeByteArray(BUF) <=Int L [simplification]

    rule #range( M [ N1 := BUF1:ByteArray ] [ N2 := BUF2:ByteArray ], L, K ) =>
         #range( M                          [ N2 := BUF2           ], L, K )
      requires 0 <Int K andBool N1 +Int #sizeByteArray(BUF1) <=Int L [simplification]

  // ########################
  // Map Reasoning
  // ########################

    rule #lookup ( _M:Map [ K1 <- V1 ] , K2 ) => #lookup ( K1 |-> V1 , K1 )  requires K1 ==Int  K2 [simplification]
    rule #lookup (  M:Map [ K1 <- _  ] , K2 ) => #lookup ( M         , K2 )  requires K1 =/=Int K2 [simplification]

    rule 0 <=Int #lookup( _M:Map , _ )             => true [simplification, smt-lemma]
    rule         #lookup( _M:Map , _ ) <Int pow256 => true [simplification, smt-lemma]

    // re-order assignments
    rule MEM [ K1 := BUF1:ByteArray ] [ K2 := BUF2:ByteArray ] => MEM [ K2 := BUF2 ] [ K1 := BUF1 ]  requires         #sizeByteArray(BUF2) <=Int K1 -Int K2                   andBool K2  <Int K1 [simplification]
    // overwritten assignment
    rule MEM [ K1 := BUF1           ] [ K2 := BUF2           ] => MEM [ K2 := BUF2 ]                 requires K1 +Int #sizeByteArray(BUF1) <=Int K2 +Int #sizeByteArray(BUF2) andBool K2 <=Int K1 [simplification]

    // lookup range in memory
    rule _MEM [ _ .. W ] => .ByteArray  requires W ==Int 0                    [simplification]
    rule  MEM [ 0 .. W ] => MEM         requires W ==Int #sizeByteArray(MEM)  [simplification]

    // lookup range in concatenated memory buffers
    rule (BUF1 ++  BUF2)[START .. WIDTH] =>  BUF2[START -Int #sizeByteArray(BUF1) .. WIDTH                          ]                                                              requires                        #sizeByteArray(BUF1) <=Int START                                                             [simplification]
    rule (BUF1 ++  _   )[START .. WIDTH] =>  BUF1[START                           .. WIDTH                          ]                                                              requires START +Int WIDTH <=Int #sizeByteArray(BUF1)                       andBool 0 <=Int START andBool 0 <=Int WIDTH       [simplification]
    rule (BUF1 ++  BUF2)[START .. WIDTH] => (BUF1[START                           .. #sizeByteArray(BUF1) -Int START]) ++ (BUF2[0 .. START +Int WIDTH -Int #sizeByteArray(BUF1)])  requires                        #sizeByteArray(BUF1) <Int START +Int WIDTH andBool #range(0 <= START < #sizeByteArray(BUF1)) [simplification]

    rule M:Map [ I1:Int <- V1:Int ] [ I2:Int <- V2:Int ] ==K M:Map [ I2 <- V2 ] [ I1 <- V1 ] => true
      requires I1 =/=Int I2
      [simplification]

    // sizeByteArray

    rule #sizeByteArray(BUF1 ++ BUF2)            => #sizeByteArray(BUF1) +Int #sizeByteArray(BUF2)      [simplification]
    rule #sizeByteArray(#buf(SIZE, _))           => SIZE                                                [simplification]
    rule #sizeByteArray(_MEM [ START .. WIDTH ]) => WIDTH  requires 0 <=Int START andBool 0 <=Int WIDTH [simplification]
    rule #sizeByteArray(#range(_, START, WIDTH)) => WIDTH  requires 0 <=Int START andBool 0 <=Int WIDTH [simplification]

    // TODO: custom ==K unification doesn't work in Haskell yet
    // ++ unification
    rule #buf(N, A) ++ BUF1 ==K #buf(N, B) ++ BUF2 => #buf(N, A) ==K #buf(N, B) andBool BUF1 ==K BUF2     [simplification]

    rule #padToWidth(32, #asByteStack(V)) => #buf(32, V)  requires #rangeUInt(256, V) [simplification]

    rule #asWord(WS) >>Int M => #asWord(WS [ 0 .. #sizeByteArray(WS) -Int (M /Int 8) ])  requires 0 <=Int M andBool M modInt 8 ==Int 0 [simplification]

endmodule

module LEMMAS-JAVA [symbolic, kast]
    imports EVM
    imports BUF
    imports K-REFLECTION

  // ########################
  // Buffer Reasoning
  // ########################

    rule BUF [ L .. _W ] => .ByteArray requires L >=Int #sizeByteArray(BUF) [simplification]

    rule (W0 : WS) [ 0     .. WIDTH ] => W0 : (WS [ 0            .. WIDTH -Int 1 ]) requires #rangeUInt(8, W0) andBool 0 <Int WIDTH [simplification]
    rule (W0 : WS) [ START .. WIDTH ] =>       WS [ START -Int 1 .. WIDTH        ]  requires #rangeUInt(8, W0) andBool 0 <Int START [simplification]

    // #sizeByteArray

    rule #sizeByteArray(_W : WS) => 1 +Int #sizeByteArray(WS) [simplification]

    // #asWord

    rule #asWord(#buf(_N, BUF)) => BUF [simplification]

    rule #asWord(BUF) /Int pow224 => #asWord(BUF [ 0 .. 4 ]) requires #sizeByteArray(BUF) ==Int 32 [simplification]

    rule #buf(N, #asWord(WS)) => WS
      requires #noOverflow(WS)
       andBool N ==Int #sizeByteArray(WS)
      [simplification]


    rule BA:ByteArray     ==K #buf( 32, DATA ) => #buf( 32, DATA ) ==K   BA              requires #isConcrete(BA)             [simplification]
    rule #buf( 32, DATA ) ==K BA:ByteArray     => DATA             ==Int #asInteger(BA)  requires #isConcrete(BA)
                                                                                          andBool #sizeByteArray(BA) <=Int 32 [simplification]

  // ########################
  // Overflow
  // ########################

    syntax Bool ::= #noOverflow    ( ByteArray ) [function]
                  | #noOverflowAux ( ByteArray ) [function]
 // -------------------------------------------------------
    rule #noOverflow(WS) => #sizeByteArray(WS) <=Int 32 andBool #noOverflowAux(WS)

    rule #noOverflowAux(.ByteArray) => true

  // ########################
  // Arithmetic
  // ########################

    // TODO: figure out how to safely override these with associativity rules
    //       from infinite-gas.k

    // 2 terms

    // associate symbolic terms to the left, concrete terms to the right
    rule I +Int B => B +Int I          requires #isConcrete(I) andBool (notBool #isConcrete(B)) [simplification]
    // converting -Int to +Int for concrete values.
    rule A -Int I => A +Int (0 -Int I) requires #isConcrete(I) andBool (notBool #isConcrete(A)) [simplification]

    // 3 terms

    // symbolic first: A, J, K
    rule (A  +Int  J) +Int  K  => (J +Int K) +Int A  requires #isConcrete(J) andBool #isConcrete(K) andBool (notBool #isConcrete(A)) [simplification]
    // symbolic second: I, B, K
    rule  I  +Int (B  +Int  K) => (I +Int K) +Int B  requires #isConcrete(I) andBool #isConcrete(K) andBool (notBool #isConcrete(B)) [simplification]
    rule  I  -Int (B  +Int  K) => (I -Int K) -Int B  requires #isConcrete(I) andBool #isConcrete(K) andBool (notBool #isConcrete(B)) [simplification]
    rule (I  -Int  B) +Int  K  => (I +Int K) -Int B  requires #isConcrete(I) andBool #isConcrete(K) andBool (notBool #isConcrete(B)) [simplification]
    // symbolic third: I, J, C
    rule  I  +Int (J  +Int  C) => (I +Int J) +Int C  requires #isConcrete(I) andBool #isConcrete(J) andBool (notBool #isConcrete(C)) [simplification]
    rule  I  +Int (J  -Int  C) => (I +Int J) -Int C  requires #isConcrete(I) andBool #isConcrete(J) andBool (notBool #isConcrete(C)) [simplification]
    rule  I  -Int (J  +Int  C) => (I -Int J) -Int C  requires #isConcrete(I) andBool #isConcrete(J) andBool (notBool #isConcrete(C)) [simplification]
    rule  I  -Int (J  -Int  C) => (I -Int J) +Int C  requires #isConcrete(I) andBool #isConcrete(J) andBool (notBool #isConcrete(C)) [simplification]
    rule  I  &Int (J  &Int  C) => (I &Int J) &Int C  requires #isConcrete(I) andBool #isConcrete(J) andBool (notBool #isConcrete(C)) [simplification]

    // 0xffff...f &Int N = N
    // MASK = 0xffff...f
    rule MASK &Int N    => N requires MASK ==Int (2 ^Int (log2Int(MASK) +Int 1)) -Int 1 andBool 0 <=Int N andBool N <=Int MASK [simplification]

    // N &Int 0xffff...f = N
    // MASK = 0xffff...f
    rule N    &Int MASK => N requires MASK ==Int (2 ^Int (log2Int(MASK) +Int 1)) -Int 1 andBool 0 <=Int N andBool N <=Int MASK [simplification]

    rule 0 <=Int X &Int Y             => true requires 0 <=Int X andBool X <Int pow256 andBool 0 <=Int Y andBool Y <Int pow256 [simplification]
    rule         X &Int Y <Int pow256 => true requires 0 <=Int X andBool X <Int pow256 andBool 0 <=Int Y andBool Y <Int pow256 [simplification]

  // ########################
  // Boolean Logic
  // ########################

    rule B ==K false => notBool B [simplification]

  // ########################
  // Gas Calculation
  // ########################

    // for gas calculation
    rule A -Int (#if C #then B1 #else B2 #fi) => #if C #then (A -Int B1) #else (A -Int B2) #fi [simplification]

    rule (#if C #then B1 #else B2 #fi) +Int A => #if C #then (B1 +Int A) #else (B2 +Int A) #fi [simplification]

  // ########################
  // Word Reasoning
  // ########################

    rule bool2Word(A) |Int bool2Word(B) => bool2Word(A  orBool B) [simplification]
    rule bool2Word(A) &Int bool2Word(B) => bool2Word(A andBool B) [simplification]

    rule 1 |Int bool2Word(_B) => 1            [simplification]
    rule 1 &Int bool2Word( B) => bool2Word(B) [simplification]

    rule bool2Word(_B) |Int 1 => 1            [simplification]
    rule bool2Word( B) &Int 1 => bool2Word(B) [simplification]

    rule bool2Word(A) =/=K 0 => A          [simplification]
    rule bool2Word(A) =/=K 1 => notBool(A) [simplification]

    rule notBool  (X ==K 0) => X ==K 1  requires #rangeBool(X) [simplification]
    rule notBool  (X ==K 1) => X ==K 0  requires #rangeBool(X) [simplification]
    rule bool2Word(X ==K 1) => X        requires #rangeBool(X) [simplification]

    rule X <=Int maxUInt256 => X <Int pow256 [simplification]
    rule X <=Int maxUInt160 => X <Int pow160 [simplification]
    rule X <=Int 255        => X <Int 256    [simplification]

    //Simplification of bool2Word() ==Int CONCRETE, #buf() ==K CONCRETE
    rule I                   ==K bool2Word( B:Bool ) => bool2Word(B) ==Int I             requires #isConcrete(I) [simplification]
    rule bool2Word( B:Bool ) ==K I                   => B            ==K   word2Bool(I)  requires #isConcrete(I) [simplification]

endmodule

module LEMMAS-HASKELL [symbolic, kore]
    imports INT-SYMBOLIC
    imports EVM
    imports BUF

  // ########################
  // Word Reasoning
  // ########################

    rule #asWord(BUF) /Int D => #asWord(BUF[0 .. #sizeByteArray(BUF) -Int log256Int(D)])
      requires D ==Int 256 ^Int log256Int(D) andBool D >=Int 0
       andBool #sizeByteArray(BUF) >=Int log256Int(D) [simplification]

    rule #asWord(#buf(N, BUF)) => BUF
      requires #range(0 < N <= 32)
       andBool #range(0 <= BUF < 2 ^Int (N *Int 8)) [simplification]

    rule notBool  (X ==Int 0) => X ==Int 1 requires #rangeBool(X) [simplification]
    rule notBool  (X ==Int 1) => X ==Int 0 requires #rangeBool(X) [simplification]
    rule bool2Word(X ==Int 1) => X         requires #rangeBool(X) [simplification]

    //Simplification of bool2Word() ==Int CONCRETE, #buf() ==K CONCRETE
    rule I                   ==Int bool2Word( B:Bool ) => bool2Word(B) ==Int I  [simplification, concrete(I)]
    rule bool2Word( B:Bool ) ==Int I                   => B ==K word2Bool(I)    [simplification, concrete(I)]

  // ########################
  // Arithmetic
  // ########################

    rule N &Int maxUInt256 => N  requires #rangeUInt(256, N) [simplification]
    rule maxUInt256 &Int N => N  requires #rangeUInt(256, N) [simplification]
    rule N &Int maxUInt248 => N  requires #rangeUInt(248, N) [simplification]
    rule maxUInt248 &Int N => N  requires #rangeUInt(248, N) [simplification]
    rule N &Int maxUInt240 => N  requires #rangeUInt(240, N) [simplification]
    rule maxUInt240 &Int N => N  requires #rangeUInt(240, N) [simplification]
    rule N &Int maxUInt232 => N  requires #rangeUInt(232, N) [simplification]
    rule maxUInt232 &Int N => N  requires #rangeUInt(232, N) [simplification]
    rule N &Int maxUInt224 => N  requires #rangeUInt(224, N) [simplification]
    rule maxUInt224 &Int N => N  requires #rangeUInt(224, N) [simplification]
    rule N &Int maxUInt216 => N  requires #rangeUInt(216, N) [simplification]
    rule maxUInt216 &Int N => N  requires #rangeUInt(216, N) [simplification]
    rule N &Int maxUInt208 => N  requires #rangeUInt(208, N) [simplification]
    rule maxUInt208 &Int N => N  requires #rangeUInt(208, N) [simplification]
    rule N &Int maxUInt200 => N  requires #rangeUInt(200, N) [simplification]
    rule maxUInt200 &Int N => N  requires #rangeUInt(200, N) [simplification]
    rule N &Int maxUInt192 => N  requires #rangeUInt(192, N) [simplification]
    rule maxUInt192 &Int N => N  requires #rangeUInt(192, N) [simplification]
    rule N &Int maxUInt184 => N  requires #rangeUInt(184, N) [simplification]
    rule maxUInt184 &Int N => N  requires #rangeUInt(184, N) [simplification]
    rule N &Int maxUInt176 => N  requires #rangeUInt(176, N) [simplification]
    rule maxUInt176 &Int N => N  requires #rangeUInt(176, N) [simplification]
    rule N &Int maxUInt168 => N  requires #rangeUInt(168, N) [simplification]
    rule maxUInt168 &Int N => N  requires #rangeUInt(168, N) [simplification]
    rule N &Int maxUInt160 => N  requires #rangeUInt(160, N) [simplification]
    rule maxUInt160 &Int N => N  requires #rangeUInt(160, N) [simplification]
    rule N &Int maxUInt152 => N  requires #rangeUInt(152, N) [simplification]
    rule maxUInt152 &Int N => N  requires #rangeUInt(152, N) [simplification]
    rule N &Int maxUInt144 => N  requires #rangeUInt(144, N) [simplification]
    rule maxUInt144 &Int N => N  requires #rangeUInt(144, N) [simplification]
    rule N &Int maxUInt136 => N  requires #rangeUInt(136, N) [simplification]
    rule maxUInt136 &Int N => N  requires #rangeUInt(136, N) [simplification]
    rule N &Int maxUInt128 => N  requires #rangeUInt(128, N) [simplification]
    rule maxUInt128 &Int N => N  requires #rangeUInt(128, N) [simplification]
    rule N &Int maxUInt120 => N  requires #rangeUInt(120, N) [simplification]
    rule maxUInt120 &Int N => N  requires #rangeUInt(120, N) [simplification]
    rule N &Int maxUInt112 => N  requires #rangeUInt(112, N) [simplification]
    rule maxUInt112 &Int N => N  requires #rangeUInt(112, N) [simplification]
    rule N &Int maxUInt104 => N  requires #rangeUInt(104, N) [simplification]
    rule maxUInt104 &Int N => N  requires #rangeUInt(104, N) [simplification]
    rule N &Int maxUInt96  => N  requires #rangeUInt(96,  N) [simplification]
    rule maxUInt96 &Int N  => N  requires #rangeUInt(96,  N) [simplification]
    rule N &Int maxUInt88  => N  requires #rangeUInt(88,  N) [simplification]
    rule maxUInt88 &Int N  => N  requires #rangeUInt(88,  N) [simplification]
    rule N &Int maxUInt80  => N  requires #rangeUInt(80,  N) [simplification]
    rule maxUInt80 &Int N  => N  requires #rangeUInt(80,  N) [simplification]
    rule N &Int maxUInt72  => N  requires #rangeUInt(72,  N) [simplification]
    rule maxUInt72 &Int N  => N  requires #rangeUInt(72,  N) [simplification]
    rule N &Int maxUInt64  => N  requires #rangeUInt(64,  N) [simplification]
    rule maxUInt64 &Int N  => N  requires #rangeUInt(64,  N) [simplification]
    rule N &Int maxUInt56  => N  requires #rangeUInt(56,  N) [simplification]
    rule maxUInt56 &Int N  => N  requires #rangeUInt(56,  N) [simplification]
    rule N &Int maxUInt48  => N  requires #rangeUInt(48,  N) [simplification]
    rule maxUInt48 &Int N  => N  requires #rangeUInt(48,  N) [simplification]
    rule N &Int maxUInt40  => N  requires #rangeUInt(40,  N) [simplification]
    rule maxUInt40 &Int N  => N  requires #rangeUInt(40,  N) [simplification]
    rule N &Int maxUInt32  => N  requires #rangeUInt(32,  N) [simplification]
    rule maxUInt32 &Int N  => N  requires #rangeUInt(32,  N) [simplification]
    rule N &Int maxUInt24  => N  requires #rangeUInt(24,  N) [simplification]
    rule maxUInt24 &Int N  => N  requires #rangeUInt(24,  N) [simplification]
    rule N &Int maxUInt16  => N  requires #rangeUInt(16,  N) [simplification]
    rule maxUInt16 &Int N  => N  requires #rangeUInt(16,  N) [simplification]
    rule N &Int maxUInt8   => N  requires #rangeUInt(8,   N) [simplification]
    rule maxUInt8 &Int N   => N  requires #rangeUInt(8,   N) [simplification]

    rule N modInt pow160   => N  requires #rangeUInt(160, N) [simplification]

    // ; Z3 version 4.8.12
    // (set-option :smt.mbqi true)
    //
    // ; 2^256
    // (declare-const pow256 Int)
    // (assert (= pow256 115792089237316195423570985008687907853269984665640564039457584007913129639936))
    //
    // (define-fun chop ((x Int)) Int (mod x pow256))
    // (define-fun range256 ((x Int)) Bool (and (>= x 0) (< x pow256)))

    // (push)
    // (assert (forall ((x Int) (y Int)) (=> (and (<= pow256 (+ x y)) (range256 x) (range256 y)) (= (< (chop (+ x y)) x) true))))
    // (check-sat)
    // (pop)
    rule chop ( X +Int Y ) <Int X  => true   requires pow256 <=Int ( X +Int Y ) andBool #rangeUInt(256, X) andBool #rangeUInt(256, Y) [simplification]

    // (push)
    // (assert (forall ((x Int) (y Int)) (=> (and (<= pow256 (+ x y)) (range256 x) (range256 y)) (= (<= x (chop (+ x y))) false))))
    // (check-sat)
    // (pop)
    rule X <=Int chop ( X +Int Y ) => false  requires pow256 <=Int ( X +Int Y ) andBool #rangeUInt(256, X) andBool #rangeUInt(256, Y) [simplification]

  // ########################
  // Buffer Reasoning
  // ########################

    rule 0 <=Int lengthBytes ( _ ) => true [smt-lemma, simplification]

    rule BA:ByteArray   ==K #buf(32, DATA) => #buf(32, DATA) ==K              BA                                       [simplification, concrete(BA)]
    rule #buf(32, DATA) ==K BA:ByteArray   =>          DATA  ==Int #asInteger(BA) requires #sizeByteArray(BA) <=Int 32 [simplification, concrete(BA)]

    rule #range(M, N1 +Int N2, K) => #range(#range(M, N2, #sizeByteArray(M) -Int N2), N1, K)
      requires 0 <=Int N1 andBool 0 <=Int N2
      [simplification, concrete(N2), concrete(M)]

  // ########################
  // Map Reasoning
  // ########################

    rule { M:Map [ I1:Int <- V1:Int ] [ I2:Int <- V2:Int ] #Equals M:Map [ I2 <- V2 ] [ I1 <- V1 ] } => #Top
      requires I1 =/=Int I2
      [simplification]

  // ########################
  // Boolean Logic
  // ########################

    rule B ==Bool false => notBool B [simplification]

    rule #range(A ++ _B, START, LENGTH) => #range(A, START, LENGTH)
      requires START +Int LENGTH <=Int #sizeByteArray(A) [simplification]

    rule #range(A ++ B, START, LENGTH) => #range(B, START -Int #sizeByteArray(A), LENGTH)
      requires #sizeByteArray(A) <=Int START [simplification]

    rule #range ( BA:ByteArray , 0 , LEN ) => BA requires #sizeByteArray(BA) ==Int LEN [simplification]

endmodule
