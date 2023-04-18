module BYTES-SIMPLIFICATION [symbolic]
    imports INT-SYMBOLIC
    imports EVM
    imports BUF

  // ########################
  // Buffer Reasoning
  // ########################

    rule BA:Bytes   ==K #buf(32, DATA) => #buf(32, DATA) ==K              BA                                    [simplification, concrete(BA)]
    rule #buf(32, DATA) ==K BA:Bytes   =>          DATA  ==Int #asInteger(BA) requires lengthBytes(BA) <=Int 32 [simplification, concrete(BA)]

    rule [bytes-concat-empty-right]: B:Bytes +Bytes .Bytes  => B [simplification]
    rule [bytes-concat-empty-left]:  .Bytes  +Bytes B:Bytes => B [simplification]

    rule [bytes-concat-assoc-right]: (BA1 +Bytes BA2) +Bytes BA3 => BA1 +Bytes (BA2 +Bytes BA3) [simplification]

    // #buf

    // TODO: custom ==K unification doesn't work in Haskell yet
    // +Bytes unification
    rule #buf(N, A) +Bytes BUF1 ==K #buf(N, B) +Bytes BUF2 => #buf(N, A) ==K #buf(N, B) andBool BUF1 ==K BUF2     [simplification]

    // #range

    rule #range(_, _, K) => .Bytes requires K <=Int 0 [simplification]

    rule #range(#writeRange(M, N, BUF:Bytes ), L, K) =>
         #let W = minInt(K, N -Int L) #in #range(M, L, W) +Bytes #range(#writeRange(M, N, BUF), N, K -Int W)
      requires 0 <Int K andBool L <Int N [simplification]

    rule #range(#writeRange(M, N, BUF:Bytes), L, K) =>
           #let S = L -Int N #in
           #let W = minInt(K, lengthBytes(BUF) -Int S) #in
           #range(BUF, S, W) +Bytes #range(M, N +Int lengthBytes(BUF), K -Int W)
      requires 0 <Int K andBool N <=Int L andBool L <=Int N +Int lengthBytes(BUF) [simplification]

    rule #range(#writeRange(M, N, BUF:Bytes ), L, K) => #range(M, L, K)
      requires 0 <Int K andBool N +Int lengthBytes(BUF) <=Int L [simplification]

    rule #range(#writeRange(#writeRange(M, N1, BUF1:Bytes), N2, BUF2:Bytes), L, K ) => #range(#writeRange(M, N2, BUF2), L, K)
        requires 0 <Int K andBool N1 +Int lengthBytes(BUF1) <=Int L [simplification]

    rule #range(M, N1 +Int N2, K) => #range(#range(M, N2, lengthBytes(M) -Int N2), N1, K)
      requires 0 <=Int N1 andBool 0 <=Int N2
      [simplification, concrete(N2), concrete(M)]

    rule #range(A +Bytes _B, START, LENGTH) => #range(A, START, LENGTH)
      requires START +Int LENGTH <=Int lengthBytes(A) [simplification]

    rule #range(A +Bytes B, START, LENGTH) => #range(B, START -Int lengthBytes(A), LENGTH)
      requires lengthBytes(A) <=Int START [simplification]

    rule #range(BA:Bytes, 0, LEN) => BA requires lengthBytes(BA) ==Int LEN [simplification]

    rule (#range(#buf(32, X), 0, 28) ):Bytes => #buf(28, 0) requires #rangeUInt ( 32 , X ) [simplification]

    rule (#range(#range( BA:Bytes, S0, L0), S1, L1) ) =>#range(BA, S0 +Int S1, minInt(L1, L0 -Int S1)) +Bytes #buf(maxInt(0, L1 -Int (L0 -Int S1)), 0)
      requires 0 <=Int S0 andBool 0 <=Int L0 andBool 0 <=Int S1 andBool 0 <=Int L1 [simplification]

    // lookup range in memory
    rule #range(MEM, 0, W) => MEM  requires W ==Int lengthBytes(MEM) [simplification]

    // lookup range in concatenated memory buffers
    rule #range((BUF1 +Bytes  BUF2), START, WIDTH) =>  #range(BUF2, START -Int lengthBytes(BUF1), WIDTH                        )                                                                    requires                        lengthBytes(BUF1) <=Int START                                                          [simplification]
    rule #range((BUF1 +Bytes  _   ), START, WIDTH) =>  #range(BUF1, START                       , WIDTH                        )                                                                    requires START +Int WIDTH <=Int lengthBytes(BUF1)                       andBool 0 <=Int START andBool 0 <=Int WIDTH    [simplification]
    rule #range((BUF1 +Bytes  BUF2), START, WIDTH) => (#range(BUF1, START                       , lengthBytes(BUF1) -Int START)) +Bytes (#range(BUF2, 0, START +Int WIDTH -Int lengthBytes(BUF1)))  requires                        lengthBytes(BUF1) <Int START +Int WIDTH andBool #range(0 <= START < lengthBytes(BUF1)) [simplification]

    rule #range(#padRightToWidth(_, BUF), 0, WIDTH) => BUF requires lengthBytes(BUF) ==Int WIDTH [simplification]

    // #writeRange

    // re-order assignments
    rule #writeRange(#writeRange(MEM, K1, BUF1:Bytes), K2, BUF2:Bytes) => #writeRange(#writeRange(MEM, K2, BUF2), K1, BUF1)
      requires lengthBytes(BUF2) <=Int K1 -Int K2 andBool K2  <Int K1 [simplification]

    // overwritten assignment
    rule #writeRange(#writeRange(MEM, K1, BUF1), K2, BUF2) => #writeRange(MEM, K2, BUF2)
      requires K1 +Int lengthBytes(BUF1) <=Int K2 +Int lengthBytes(BUF2) andBool K2 <=Int K1 [simplification]

    // lengthBytes

    rule [lengthBytes-geq-zero]:     0 <=Int lengthBytes ( _ )                 => true                                                [simplification, smt-lemma]
    rule [lengthBytes-concat]:       lengthBytes(BUF1 +Bytes BUF2)             => lengthBytes(BUF1) +Int lengthBytes(BUF2)            [simplification]
    rule [lengthBytes-buf]:          lengthBytes(#buf(SIZE, _))                => SIZE                                                [simplification]
    rule [lengthBytes-range]:        lengthBytes(#range(_, START, WIDTH))      => WIDTH  requires 0 <=Int START andBool 0 <=Int WIDTH [simplification]
    rule [lengthBytes-prtw-leq-len]: lengthBytes(#padRightToWidth(WIDTH, BUF)) => WIDTH  requires lengthBytes(BUF) <=Int WIDTH        [simplification]

    // #asWord

    rule #asWord(WS) >>Int M => #asWord(#range(WS, 0, lengthBytes(WS) -Int (M /Int 8) ))  requires 0 <=Int M andBool M modInt 8 ==Int 0 [simplification]

    rule #asWord(#padRightToWidth(32, BUF)) &Int notMaxUInt224 => #asWord(#padRightToWidth(32, BUF))
      requires lengthBytes(BUF) <=Int 4 [simplification]

    rule #padToWidth(32, #asByteStack(V)) => #buf(32, V)  requires #rangeUInt(256, V) [simplification]

endmodule
