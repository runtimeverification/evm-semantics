requires "evm.md"
requires "edsl.md"

module LEMMAS
    imports LEMMAS-JAVA
    imports LEMMAS-HASKELL

    rule 0 <=Int #sizeWordStack ( _ , _ ) => true [smt-lemma, simplification]
    rule 0 <=Int #sizeByteArray ( _ )     => true [smt-lemma, simplification]

    rule #lookup ( _M:Map [ K1 <- V1 ] , K2 ) => #lookup ( K1 |-> V1 , K1 ) requires K1 ==Int  K2 [simplification]
    rule #lookup (  M:Map [ K1 <- _  ] , K2 ) => #lookup ( M         , K2 ) requires K1 =/=Int K2 [simplification]

    rule 0 <=Int #lookup( _M:Map , _ )             => true                                       [simplification]
    rule         #lookup( _M:Map , _ ) <Int pow256 => true                                       [simplification, smt-lemma]

    //Required for #Ceil(#buf)
    rule 0 <=Int keccak( _ )             => true                                                 [simplification]
    rule         keccak( _ ) <Int pow256 => true                                                 [simplification]

    rule WS ++ .ByteArray => WS  [simplification]
    rule .ByteArray ++ WS => WS  [simplification]

    //Byte array store operations sorting. Slices with lower index first. Helps applying rule below.
    rule MEM [ N := BUF:ByteArray ] [ M := BUF' ] => MEM [ M := BUF' ] [ N := BUF ]
      requires N >Int M andBool N -Int M >=Int #sizeByteArray(BUF')                                               [simplification]

    rule M [ N := BUF ] [ N := BUF' ] => M [ N := BUF' ] requires #sizeByteArray(BUF) ==Int #sizeByteArray(BUF')  [simplification]

    rule _BUF [ _ .. W ] => .ByteArray requires W ==Int 0                    [simplification]
    rule  BUF [ 0 .. W ] => BUF        requires W ==Int #sizeByteArray(BUF)  [simplification]

    rule (BUF1 ++ BUF2)[START .. WIDTH] => (BUF1[START .. #sizeByteArray(BUF1) -Int START]) ++ (BUF2[0 .. START +Int WIDTH -Int #sizeByteArray(BUF1)])
      requires #range(0 <= START < #sizeByteArray(BUF1))
       andBool #sizeByteArray(BUF1) <Int START +Int WIDTH [simplification]

    rule (BUF1 ++_BUF2)[START .. WIDTH] => (BUF1[START .. WIDTH])
      requires #range(0 <= START < #sizeByteArray(BUF1))
       andBool START +Int WIDTH <=Int #sizeByteArray(BUF1) [simplification]

    rule (BUF1 ++ BUF2)[START .. WIDTH] => BUF2 [START -Int #sizeByteArray(BUF1) .. WIDTH]
      requires START >=Int #sizeByteArray(BUF1) [simplification]

    rule #sizeByteArray(BUF1 ++ BUF2)                  => #sizeByteArray(BUF1) +Int #sizeByteArray(BUF2)  [simplification]
    rule #sizeByteArray(#buf(SIZE, _))                 => SIZE                                            [simplification]
    rule #sizeByteArray(#buf(SIZE, _)[START .. WIDTH]) => WIDTH
      requires #range(0 <= START < SIZE)
       andBool #range(0 < WIDTH <= SIZE -Int START)                                                       [simplification]

    rule #sizeByteArray(#range(_, START, WIDTH)) => WIDTH
      requires WIDTH >=Int 0 andBool START >=Int 0                                                        [simplification]

    //Todo custom ==K unification doesn't work in Haskell yet
    //++ unification
    rule #buf(N, A) ++ BUF1 ==K #buf(N, B) ++ BUF2 => #buf(N, A) ==K #buf(N, B) andBool BUF1 ==K BUF2     [simplification]

    rule #padToWidth(32, #asByteStack(V)) => #buf(32, V)
      requires #rangeUInt(256, V)                                                                         [simplification]

    rule 0 <=Int keccak(_)                  => true  [simplification]
    rule         keccak(_) <Int pow256      => true  [simplification]

    //Inequality sign normalization
    rule          X  >Int Y  => Y  <Int X            [simplification]
    rule          X >=Int Y  => Y <=Int X            [simplification]
    rule notBool (X  <Int Y) => Y <=Int X            [simplification]
    rule notBool (X <=Int Y) => Y  <Int X            [simplification]

    // chop range & simplification
    rule chop(I) => I requires #rangeUInt( 256 , I ) [simplification]
    rule 0 <=Int chop(_V)             => true        [simplification]
    rule         chop(_V) <Int pow256 => true        [simplification]

    // bool2Word range & simplification
    rule 0 <=Int bool2Word(_B)             => true   [simplification]
    rule         bool2Word(_B) <Int pow256 => true   [simplification]

    rule notBool notBool B => B [simplification]

    // #newAddr range
    rule 0 <=Int #newAddr(_,_)             => true   [simplification]
    rule         #newAddr(_,_) <Int pow160 => true   [simplification]
    rule         #newAddr(_,_) <Int pow256 => true   [simplification]

    rule N /Int 1 => N  [simplification]

endmodule

module LEMMAS-JAVA [symbolic, kast]
    imports EVM
    imports EDSL
    imports K-REFLECTION

    rule BUF [ L .. _W ] => .ByteArray requires L >=Int #sizeByteArray(BUF) [simplification]

    rule #asWord( BUF => #drop(1, BUF) ) requires BUF [ 0 ] ==Int 0 [simplification]

    rule #sizeByteArray(_W : WS)       => 1 +Int #sizeByteArray(WS)             [simplification]
    rule #sizeByteArray(#drop(N, BUF)) => maxInt(#sizeByteArray(BUF) -Int N, 0) [simplification]

    rule #take(N, BUF)           => BUF                                              requires N ==Int #sizeByteArray(BUF)  [simplification]
    rule #take(N, BUF1 ++ _BUF2) => #take(N, BUF1)                                   requires N <=Int #sizeByteArray(BUF1) [simplification]
    rule #take(N, BUF1 ++  BUF2) => BUF1 ++ #take(N -Int #sizeByteArray(BUF1), BUF2) requires N  >Int #sizeByteArray(BUF1) [simplification]

    rule #drop(N, BUF)          => .ByteArray                               requires N >=Int #sizeByteArray(BUF)  [simplification]
    rule #drop(N, BUF1 ++ BUF2) => #drop(N -Int #sizeByteArray(BUF1), BUF2) requires N >=Int #sizeByteArray(BUF1) [simplification]
    rule #drop(N, BUF1 ++ BUF2) => #drop(N, BUF1) ++ BUF2                   requires N  <Int #sizeByteArray(BUF1) [simplification]

    rule #asWord(#buf(_N, BUF)) => BUF [simplification]

    rule #asWord(BUF) /Int 26959946667150639794667015087019630673637144422540572481103610249216 => #asWord(#take(4, BUF)) [simplification]

    rule #range(_M, _N, K) => .ByteArray requires notBool K >Int 0 [simplification]

    rule #range(M [ N := BUF:ByteArray ], L, K) => #range(M, L, minInt(K, N -Int L)) ++ #range(M [ N := BUF ], N, K -Int minInt(K, N -Int L))
      requires K >Int 0
       andBool L <Int N
      [simplification]

    rule #range(M [ N := BUF ], L, K) => BUF [ L -Int N .. minInt(K, #sizeByteArray(BUF) -Int (L -Int N)) ] ++ #range(M, N +Int #sizeByteArray(BUF), K -Int minInt(K, #sizeByteArray(BUF) -Int (L -Int N)))
      requires K  >Int 0
       andBool L >=Int N
       andBool L  <Int N +Int #sizeByteArray(BUF)
      [simplification]

    rule #range(M [ N := BUF ], L, K) => #range(M, L, K)
      requires K  >Int 0
       andBool L >=Int N +Int #sizeByteArray(BUF)
      [simplification]

    rule keccak(BUF1 ++ BUF2) => hash2(#asWord(BUF1), #asWord(BUF2)) requires #sizeByteArray(BUF1) ==Int 32 andBool #sizeByteArray(BUF2) ==Int 32 [simplification]

    // for Solidity
    rule #asWord(WS) /Int D => #asWord(#take(#sizeByteArray(WS) -Int log256Int(D), WS))
      requires D ==Int 256 ^Int log256Int(D) andBool D >=Int 0
       andBool #sizeByteArray(WS) >=Int log256Int(D)
       andBool #noOverflow(WS)
      [simplification]

    rule #buf(N, #asWord(WS)) => WS
      requires #noOverflow(WS) andBool N ==Int #sizeByteArray(WS)
      [simplification]

    syntax Bool ::= #noOverflow    ( ByteArray ) [function]
                  | #noOverflowAux ( ByteArray ) [function]
 // -------------------------------------------------------
    rule #noOverflow(WS) => #sizeByteArray(WS) <=Int 32 andBool #noOverflowAux(WS)

    rule #noOverflowAux(BA        ) => 0 <=Int BA[0] andBool BA[0] <Int 256 andBool #noOverflowAux(#drop(1,BA)) requires #sizeByteArray(BA) >Int 0
    rule #noOverflowAux(.ByteArray) => true

    // TODO: drop hash1 and keccakIntList once new vyper hashed location scheme is captured in edsl.md

    syntax Int ::= hash1(Int)      [function, smtlib(smt_hash1)]
                 | hash2(Int, Int) [function, smtlib(smt_hash2)]
 // ------------------------------------------------------------
    rule hash1(V) => keccak(#padToWidth(32, #asByteStack(V)))
      requires 0 <=Int V andBool V <Int pow256
      [concrete]

    rule hash2(V1, V2) => keccak(   #padToWidth(32, #asByteStack(V1))
                                 ++ #padToWidth(32, #asByteStack(V2)))
      requires 0 <=Int V1 andBool V1 <Int pow256
       andBool 0 <=Int V2 andBool V2 <Int pow256
      [concrete]

    rule keccakIntList(V:Int .IntList) => hash1(V)
    rule keccakIntList(V1:Int V2:Int .IntList) => hash2(V1, V2)

    // for terms came from bytecode not via #hashedLocation
    rule keccak(WS) => keccakIntList(byteStack2IntList(WS))
      requires ( notBool #isConcrete(WS) )
       andBool ( #sizeByteArray(WS) ==Int 32 orBool #sizeByteArray(WS) ==Int 64 )

    rule 1 *Int N => N
    rule N *Int 1 => N
    rule 0 *Int _ => 0
    rule _ *Int 0 => 0

    rule 0 |Int N => N
    rule N |Int 0 => N
    rule N |Int N => N

    rule  0 &Int _N => 0
    rule _N &Int  0 => 0
    rule  N &Int  N => N

    //orienting symbolic term to be first, converting -Int to +Int for concrete values.
    rule I +Int B => B          +Int I when #isConcrete(I) andBool notBool #isConcrete(B) [simplification]
    rule A -Int I => A +Int (0 -Int I) when notBool #isConcrete(A) andBool #isConcrete(I) [simplification]

    rule (A +Int I2) +Int I3 => A +Int (I2 +Int I3) when notBool #isConcrete(A) andBool #isConcrete(I2) andBool #isConcrete(I3) [simplification]

    rule I1 +Int (B +Int I3) => B +Int (I1 +Int I3) when #isConcrete(I1) andBool notBool #isConcrete(B) andBool #isConcrete(I3) [simplification]
    rule I1 -Int (B +Int I3) => (I1 -Int I3) -Int B when #isConcrete(I1) andBool notBool #isConcrete(B) andBool #isConcrete(I3) [simplification]
    rule (I1 -Int B) +Int I3 => (I1 +Int I3) -Int B when #isConcrete(I1) andBool notBool #isConcrete(B) andBool #isConcrete(I3) [simplification]

    rule I1 +Int (I2 +Int C) => (I1 +Int I2) +Int C when #isConcrete(I1) andBool #isConcrete(I2) andBool notBool #isConcrete(C) [simplification]
    rule I1 +Int (I2 -Int C) => (I1 +Int I2) -Int C when #isConcrete(I1) andBool #isConcrete(I2) andBool notBool #isConcrete(C) [simplification]
    rule I1 -Int (I2 +Int C) => (I1 -Int I2) -Int C when #isConcrete(I1) andBool #isConcrete(I2) andBool notBool #isConcrete(C) [simplification]
    rule I1 -Int (I2 -Int C) => (I1 -Int I2) +Int C when #isConcrete(I1) andBool #isConcrete(I2) andBool notBool #isConcrete(C) [simplification]

    rule I1 &Int (I2 &Int C) => (I1 &Int I2) &Int C when #isConcrete(I1) andBool #isConcrete(I2) andBool notBool #isConcrete(C) [simplification]

    // 0xffff...f &Int N = N
    rule MASK &Int N => N  requires MASK ==Int (2 ^Int (log2Int(MASK) +Int 1)) -Int 1 // MASK = 0xffff...f
                            andBool 0 <=Int N andBool N <=Int MASK
      [simplification]

    // N &Int 0xffff...f = N
    rule N &Int MASK => N  requires MASK ==Int (2 ^Int (log2Int(MASK) +Int 1)) -Int 1 // MASK = 0xffff...f
                            andBool 0 <=Int N andBool N <=Int MASK
      [simplification]


    // for gas calculation
    rule A -Int (#if C #then B1 #else B2 #fi) => #if C #then (A -Int B1) #else (A -Int B2) #fi [simplification]

    rule (#if C #then B1 #else B2 #fi) +Int A => #if C #then (B1 +Int A) #else (B2 +Int A) #fi [simplification]

    rule bool2Word(A) |Int bool2Word(B) => bool2Word(A  orBool B) [simplification]
    rule bool2Word(A) &Int bool2Word(B) => bool2Word(A andBool B) [simplification]

    rule 1 |Int bool2Word(_B) => 1            [simplification]
    rule 1 &Int bool2Word( B) => bool2Word(B) [simplification]

    rule bool2Word(_B) |Int 1 => 1            [simplification]
    rule bool2Word( B) &Int 1 => bool2Word(B) [simplification]

    rule bool2Word(A) =/=K 0 => A          [simplification]
    rule bool2Word(A) =/=K 1 => notBool(A) [simplification]

    rule notBool  (X ==K 0) => X ==K 1 requires #rangeBool(X) [simplification]
    rule notBool  (X ==K 1) => X ==K 0 requires #rangeBool(X) [simplification]
    rule bool2Word(X ==K 1) => X       requires #rangeBool(X) [simplification]

    rule B ==K false => notBool B [simplification]

    rule 0 <=Int X &Int Y             => true requires 0 <=Int X andBool X <Int pow256 andBool 0 <=Int Y andBool Y <Int pow256 [simplification]
    rule         X &Int Y <Int pow256 => true requires 0 <=Int X andBool X <Int pow256 andBool 0 <=Int Y andBool Y <Int pow256 [simplification]

    rule 0 <=Int #asWord(_WS)         => true [simplification]
    rule #asWord(_WS) <Int pow256     => true [simplification]

    rule 0 <=Int hash1(_)             => true [simplification]
    rule         hash1(_) <Int pow256 => true [simplification]

    rule 0 <=Int hash2(_,_)             => true [simplification]
    rule         hash2(_,_) <Int pow256 => true [simplification]

    rule 0 <=Int keccakIntList(_)             => true [simplification]
    rule         keccakIntList(_) <Int pow256 => true [simplification]

    rule X <=Int maxUInt256 => X <Int pow256 [simplification]
    rule X <=Int maxUInt160 => X <Int pow160 [simplification]
    rule X <=Int 255        => X <Int 256    [simplification]

    //Simplification of bool2Word() ==Int CONCRETE, #buf() ==K CONCRETE
    rule I                   ==K bool2Word( B:Bool ) => bool2Word(B) ==Int I    requires #isConcrete(I) [simplification]
    rule bool2Word( B:Bool ) ==K I                   => B ==K word2Bool(I)      requires #isConcrete(I) [simplification]

    rule BA:ByteArray     ==K #buf( 32, DATA ) => #buf( 32, DATA ) ==K BA       requires #isConcrete(BA) [simplification]
    rule #buf( 32, DATA ) ==K BA:ByteArray     => DATA ==Int #asInteger(BA)
      requires #sizeByteArray(BA) <=Int 32                                      andBool  #isConcrete(BA) [simplification]

endmodule

module LEMMAS-HASKELL [symbolic, kore]
    imports INT-SYMBOLIC
    imports EVM
    imports EDSL

    rule #asWord(BUF) /Int D => #asWord(BUF[0 .. #sizeByteArray(BUF) -Int log256Int(D)])
      requires D ==Int 256 ^Int log256Int(D) andBool D >=Int 0
       andBool #sizeByteArray(BUF) >=Int log256Int(D) [simplification]

    rule #asWord(#buf(N, BUF)) => BUF
      requires #range(0 < N <= 32)
       andBool #range(0 <= BUF < 2 ^Int (N *Int 8)) [simplification]

    rule N &Int maxUInt160 => N
      requires #rangeUInt(160, N) [simplification]

    rule maxUInt160 &Int N => N
      requires #rangeUInt(160, N) [simplification]

    rule N modInt pow160 => N
      requires #rangeUInt(160, N) [simplification]

    rule #range(_, _, K) => .ByteArray requires notBool K >Int 0  [simplification]

    rule #range(M [ N := BUF:ByteArray ], L, K) => #range(M, L, minInt(K, N -Int L)) ++ #range(M [ N := BUF ], N, K -Int minInt(K, N -Int L))
      requires K >Int 0
       andBool L <Int N
      [simplification]

    rule #range(M [ N := BUF ], L, K) => BUF [ L -Int N .. minInt(K, #sizeByteArray(BUF) -Int (L -Int N)) ] ++ #range(M, N +Int #sizeByteArray(BUF), K -Int minInt(K, #sizeByteArray(BUF) -Int (L -Int N)))
      requires K  >Int 0
       andBool L >=Int N
       andBool L  <Int N +Int #sizeByteArray(BUF)
      [simplification]

    rule #range(M [ N := BUF ], L, K) => #range(M, L, K)
      requires K  >Int 0
       andBool L >=Int N +Int #sizeByteArray(BUF)
      [simplification]

    rule N <=Int maxInt(P, Q) => true requires N <=Int P orBool N <=Int Q  [simplification]
    rule minInt(P, Q)         => P    requires P <=Int Q                   [simplification]

    rule 0 <=Int lengthBytes ( _ ) => true [smt-lemma, simplification]

    //Simplification of bool2Word() ==Int CONCRETE, #buf() ==K CONCRETE
    rule I                   ==Int bool2Word( B:Bool ) => bool2Word(B) ==Int I  [simplification, concrete(I)]
    rule bool2Word( B:Bool ) ==Int I                   => B ==K word2Bool(I)    [simplification, concrete(I)]

    rule notBool  (X ==Int 0) => X ==Int 1 requires #rangeBool(X) [simplification]
    rule notBool  (X ==Int 1) => X ==Int 0 requires #rangeBool(X) [simplification]
    rule bool2Word(X ==Int 1) => X         requires #rangeBool(X) [simplification]

    rule B ==Bool false => notBool B [simplification]

    rule BA:ByteArray     ==K #buf( 32, DATA ) => #buf( 32, DATA ) ==K BA       [simplification, concrete(BA)]
    rule #buf( 32, DATA ) ==K BA:ByteArray     => DATA ==Int #asInteger(BA)
      requires #sizeByteArray(BA) <=Int 32                                      [simplification, concrete(BA)]

endmodule
