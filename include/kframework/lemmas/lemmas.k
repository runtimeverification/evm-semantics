requires "evm.md"
requires "buf.md"
requires "int-simplification.k"

module LEMMAS [symbolic]
    imports INT-SIMPLIFICATION
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

    rule X *Int Y <Int pow256 => true requires Y <=Int maxUInt256 /Int X [simplification]

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
    rule 0 <=Int lengthBytes ( _ )     => true                    [simplification, smt-lemma]

    // bool2Word range & simplification
    rule 0 <=Int bool2Word(_B)             => true   [simplification]
    rule         bool2Word(_B) <Int pow256 => true   [simplification]

    rule bool2Word(A) |Int bool2Word(B) => bool2Word(A  orBool B) [simplification]
    rule bool2Word(A) &Int bool2Word(B) => bool2Word(A andBool B) [simplification]

    rule 1 |Int bool2Word(_B) => 1            [simplification]
    rule 1 &Int bool2Word( B) => bool2Word(B) [simplification]

    rule bool2Word(_B) |Int 1 => 1            [simplification]
    rule bool2Word( B) &Int 1 => bool2Word(B) [simplification]

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

    // #range

    rule #range(_, _, K) =>
         .Bytes
      requires K <=Int 0 [simplification]

  // ########################
  // Map Reasoning
  // ########################

    rule #lookup ( _M:Map [ K1 <- V1 ] , K2 ) => #lookup ( K1 |-> V1 , K1 )  requires K1 ==Int  K2 [simplification]
    rule #lookup (  M:Map [ K1 <- _  ] , K2 ) => #lookup ( M         , K2 )  requires K1 =/=Int K2 [simplification]

    rule 0 <=Int #lookup( _M:Map , _ )             => true [simplification, smt-lemma]
    rule         #lookup( _M:Map , _ ) <Int pow256 => true [simplification, smt-lemma]

    rule M:Map [ I1:Int <- V1:Int ] [ I2:Int <- V2:Int ] ==K M:Map [ I2 <- V2 ] [ I1 <- V1 ] => true
      requires I1 =/=Int I2
      [simplification]

    rule #padToWidth(32, #asByteStack(V)) => #buf(32, V)  requires #rangeUInt(256, V) [simplification]

    rule #asWord(#padRightToWidth(32, BUF)) &Int notMaxUInt224 =>
         #asWord(#padRightToWidth(32, BUF))
      requires lengthBytes(BUF) <=Int 4 [simplification]

endmodule

module LEMMAS-HASKELL [symbolic, kore]
    imports INT-SYMBOLIC
    imports EVM
    imports BUF

  // ########################
  // Word Reasoning
  // ########################

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

    rule 0 <=Int (X |Int Y) => true requires 0 <=Int X andBool 0 <=Int Y [simplification]
    rule 0 <=Int (X &Int Y) => true requires 0 <=Int X andBool 0 <=Int Y [simplification]

    rule (X &Int Y) <Int Z      => true requires 0 <=Int X andBool 0 <=Int Y andBool (X <Int Z orBool Y <Int Z)          [simplification]
    rule (X |Int Y) <Int pow256 => true requires 0 <=Int X andBool 0 <=Int Y andBool X <Int pow256 andBool Y <Int pow256 [simplification]

    rule maxUInt160 &Int (X |Int (notMaxUInt160 &Int Y:Int)) => X requires #rangeUInt(160, X) andBool 0 <=Int Y [simplification]

  // ########################
  // Buffer Reasoning
  // ########################

    rule 0 <=Int lengthBytes ( _ ) => true [smt-lemma, simplification]

    rule #range(M, N1 +Int N2, K) => #range(#range(M, N2, lengthBytes(M) -Int N2), N1, K)
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

endmodule
