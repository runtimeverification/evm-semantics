requires "evm.md"
requires "buf.md"
requires "bitwise-simplification.k"
requires "bytes-simplification.k"
requires "evm-int-simplification.k"
requires "int-simplification.k"



module LEMMAS [symbolic]
    imports BITWISE-SIMPLIFICATION
    imports BYTES-SIMPLIFICATION
    imports INT-SIMPLIFICATION
    imports EVM-INT-SIMPLIFICATION
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

    rule X *Int Y <Int pow256 => true requires Y <=Int maxUInt256 /Int X [simplification]
    rule #if B #then C +Int C1 #else C +Int C2 #fi => C +Int #if B #then C1 #else C2 #fi [simplification] 

  // ########################
  // Set Reasoning
  // ########################

    rule X in (SetItem(Y) _   ) => true      requires X  ==Int Y [simplification]
    rule X in (SetItem(Y) REST) => X in REST requires X =/=Int Y [simplification]

  // ########################
  // Word Reasoning
  // ########################

    rule 0 <=Int #sizeWordStack ( _ , N ) => true requires 0 <=Int N [simplification, smt-lemma]

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
  // Map Reasoning
  // ########################

    rule #lookup ( _M:Map [ K1 <- V1 ] , K2 ) => #lookup ( K1 |-> V1 , K1 )  requires K1 ==Int  K2 [simplification]
    rule #lookup (  M:Map [ K1 <- _  ] , K2 ) => #lookup ( M         , K2 )  requires K1 =/=Int K2 [simplification]

    rule 0 <=Int #lookup( _M:Map , _ )             => true [simplification, smt-lemma]
    rule         #lookup( _M:Map , _ ) <Int pow256 => true [simplification, smt-lemma]

    rule M:Map [ I1:Int <- V1:Int ] [ I2:Int <- V2:Int ] ==K M:Map [ I2 <- V2 ] [ I1 <- V1 ] => true
      requires I1 =/=Int I2
      [simplification]

 // Hardcoded #addrFromPrivateKey simplifications, see: https://github.com/runtimeverification/haskell-backend/issues/3573
    rule #addrFromPrivateKey("0x0000000000000000000000000000000000000000000000000000000000000001") => 721457446580647751014191829380889690493307935711 [priority(40), concrete]

  // ########################
  // Memory
  // ########################

    rule #memoryUsageUpdate(MU, _, WIDTH) => MU requires WIDTH <=Int 0 [simplification]

    rule 0 <=Int #memoryUsageUpdate(MU, START, WIDTH) => true requires 0 <=Int MU andBool 0 <=Int START andBool 0 <=Int WIDTH [simplification]

    rule #memoryUsageUpdate(#memoryUsageUpdate(MU, START1, WIDTH1), START2, WIDTH2) => #memoryUsageUpdate(MU, START1, WIDTH1)
      requires #rangeUInt(256, MU) andBool 0 <Int WIDTH1 andBool 0 <Int WIDTH2
       andBool START2 +Int WIDTH2 <=Int START1 +Int WIDTH1
      [simplification]

    rule #memoryUsageUpdate(#memoryUsageUpdate(MU, START1, WIDTH1), START2, WIDTH2) => #memoryUsageUpdate(MU, START2, WIDTH2)
      requires #rangeUInt(256, MU) andBool 0 <Int WIDTH1 andBool 0 <Int WIDTH2
       andBool START1 +Int WIDTH1 <Int START2 +Int WIDTH2
      [simplification]

  // ########################
  // Gas Costs
  // ########################

    rule 0 <=Int Csload(_, _)                   => true                                       [simplification]
    rule 0 <=Int Cmem(_, N)                     => true requires 0 <=Int N                    [simplification]
    rule 0 <=Int Caddraccess(_, _)              => true                                       [simplification]
    rule 0 <=Int Csstore(_, _, _, _)            => true                                       [simplification]
    rule 0 <=Int Cgascap(_, _:Int, _:Int, _)    => true                                       [simplification]
    rule 0 <=Int #allBut64th(_:Int)             => true                                       [simplification]
    rule 0 <=Int Cextra(_, _, _, _)             => true                                       [simplification]
    rule 0 <=Int _:ScheduleConst < _:Schedule > => true                                       [simplification]
    rule 0 <=Int G up/Int I                     => true requires 0 <=Int G andBool 0 <Int I   [simplification]
    rule Cextra(_, _, _, _) <Int pow256         => true                                       [simplification]

    rule G <Int Csstore(SCHED, _:Int, _:Int, _) => false
      requires Gsload       < SCHED > <=Int G
       andBool Gsstoreset   < SCHED > <=Int G
       andBool Gsstorereset < SCHED > <=Int G
      [simplification]

    rule Csstore(SCHED, _:Int, _:Int, _) <=Int G => true
      requires Gsload       < SCHED > <=Int G
       andBool Gsstoreset   < SCHED > <=Int G
       andBool Gsstorereset < SCHED > <=Int G
      [simplification]

    rule G <=Int Csstore(SCHED, _:Int, _:Int, _) => false
      requires Gsload       < SCHED > <Int G
       andBool Gsstoreset   < SCHED > <Int G
       andBool Gsstorereset < SCHED > <Int G
      [simplification]

    rule Csstore(SCHED, _:Int, _:Int, _) <Int G => true
      requires Gsload       < SCHED > <Int G
       andBool Gsstoreset   < SCHED > <Int G
       andBool Gsstorereset < SCHED > <Int G
      [simplification]

endmodule

module LEMMAS-HASKELL [symbolic, kore]
    imports INT-SYMBOLIC
    imports EVM
    imports BUF

  // ########################
  // Word Reasoning
  // ########################

    rule #asWord(BUF) /Int D => #asWord(#range(BUF, 0, lengthBytes(BUF) -Int log256Int(D)))
       requires D ==Int 256 ^Int log256Int(D) andBool D >=Int 0
        andBool lengthBytes(BUF) >=Int log256Int(D) [simplification]

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
  // Map Reasoning
  // ########################

    rule { M:Map [ I1:Int <- V1:Int ] [ I2:Int <- V2:Int ] #Equals M:Map [ I2 <- V2 ] [ I1 <- V1 ] } => #Top
      requires I1 =/=Int I2
      [simplification]

  // ########################
  // Boolean Logic
  // ########################

    rule B ==Bool false => notBool B [simplification]
    rule (notBool (A andBool B)) andBool A => (notBool B) andBool A [simplification]
endmodule
