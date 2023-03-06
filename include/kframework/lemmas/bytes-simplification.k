module BYTES-SIMPLIFICATION
    imports BYTES-SIMPLIFICATION-JAVA
    imports BYTES-SIMPLIFICATION-HASKELL
endmodule

module BYTES-SIMPLIFICATION-JAVA [symbolic, kast]
    imports BYTES-SIMPLIFICATION-COMMON
    imports EVM
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

endmodule

module BYTES-SIMPLIFICATION-HASKELL [symbolic, kore]
    imports BYTES-SIMPLIFICATION-COMMON
    imports INT-SYMBOLIC
    imports EVM
    imports BUF

  // ########################
  // Buffer Reasoning
  // ########################

    rule 0 <=Int lengthBytes ( _ ) => true [smt-lemma, simplification]

    rule BA:ByteArray   ==K #buf(32, DATA) => #buf(32, DATA) ==K              BA                                       [simplification, concrete(BA)]
    rule #buf(32, DATA) ==K BA:ByteArray   =>          DATA  ==Int #asInteger(BA) requires #sizeByteArray(BA) <=Int 32 [simplification, concrete(BA)]

    rule #range(M, N1 +Int N2, K) => #range(#range(M, N2, #sizeByteArray(M) -Int N2), N1, K)
      requires 0 <=Int N1 andBool 0 <=Int N2
      [simplification, concrete(N2), concrete(M)]

    rule #range(A ++ _B, START, LENGTH) => #range(A, START, LENGTH)
      requires START +Int LENGTH <=Int #sizeByteArray(A) [simplification]

    rule #range(A ++ B, START, LENGTH) => #range(B, START -Int #sizeByteArray(A), LENGTH)
      requires #sizeByteArray(A) <=Int START [simplification]

    rule #range ( BA:ByteArray , 0 , LEN ) => BA requires #sizeByteArray(BA) ==Int LEN [simplification]

    rule ( #buf ( 32 , X ) [ 0 .. 28 ] ):ByteArray => #buf(28, 0) requires #rangeUInt ( 32 , X ) [simplification]

    rule ( #range ( #range ( BA:ByteArray , S0 , L0 ) , S1 , L1 ) ) => #range ( BA , S0 +Int S1 , minInt ( L1 , L0 -Int S1 ) ) ++ #buf ( maxInt ( 0 , L1 -Int ( L0 -Int S1 ) ) , 0 )
      requires 0 <=Int S0 andBool 0 <=Int L0 andBool 0 <=Int S1 andBool 0 <=Int L1 [simplification]

endmodule

module BYTES-SIMPLIFICATION-COMMON [symbolic]
    imports BUF

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

    // sizeByteArray

    rule #sizeByteArray(BUF1 ++ BUF2)                 => #sizeByteArray(BUF1) +Int #sizeByteArray(BUF2)      [simplification]
    rule #sizeByteArray(#buf(SIZE, _))                => SIZE                                                [simplification]
    rule #sizeByteArray(_MEM [ START .. WIDTH ])      => WIDTH  requires 0 <=Int START andBool 0 <=Int WIDTH [simplification]
    rule #sizeByteArray(#range(_, START, WIDTH))      => WIDTH  requires 0 <=Int START andBool 0 <=Int WIDTH [simplification]
    rule #sizeByteArray(#padRightToWidth(WIDTH, BUF)) => WIDTH  requires #sizeByteArray(BUF) <=Int WIDTH     [simplification]

    // TODO: custom ==K unification doesn't work in Haskell yet
    // ++ unification
    rule #buf(N, A) ++ BUF1 ==K #buf(N, B) ++ BUF2 => #buf(N, A) ==K #buf(N, B) andBool BUF1 ==K BUF2     [simplification]

    rule #padToWidth(32, #asByteStack(V)) => #buf(32, V)  requires #rangeUInt(256, V) [simplification]

    rule #asWord(WS) >>Int M => #asWord(WS [ 0 .. #sizeByteArray(WS) -Int (M /Int 8) ])  requires 0 <=Int M andBool M modInt 8 ==Int 0 [simplification]

    rule #asWord(#padRightToWidth(32, BUF)) &Int notMaxUInt224 =>
         #asWord(#padRightToWidth(32, BUF))
      requires #sizeByteArray(BUF) <=Int 4 [simplification]

    rule #padRightToWidth(_, BUF)[ 0 .. WIDTH ] => BUF requires #sizeByteArray(BUF) ==Int WIDTH [simplification]

endmodule
