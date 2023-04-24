module BYTES-SIMPLIFICATION [symbolic]
    imports INT-SYMBOLIC
    imports EVM
    imports BUF

  // ########################
  // Buffer Reasoning
  // ########################

    rule [bytes-not-equal-length]:
      BA1:Bytes ==K BA2:Bytes => false
      requires lengthBytes(BA1) =/=Int lengthBytes(BA2)
      [simplification]

    rule [bytes-equal-concat-split-k]:
      A:Bytes +Bytes B:Bytes ==K C:Bytes +Bytes D:Bytes => A ==K C #And B ==K D
      requires lengthBytes(A) ==Int lengthBytes(C)
        orBool lengthBytes(B) ==Int lengthBytes(D)
      [simplification]

    rule [bytes-equal-concat-split-ml]:
      { A:Bytes +Bytes B:Bytes #Equals C:Bytes +Bytes D:Bytes } => { A #Equals C } #And { B #Equals D }
      requires lengthBytes(A) ==Int lengthBytes(C)
        orBool lengthBytes(B) ==Int lengthBytes(D)
      [simplification]

    rule [bytes-concat-empty-right]: B:Bytes +Bytes .Bytes  => B [simplification]
    rule [bytes-concat-empty-left]:   .Bytes +Bytes B:Bytes => B [simplification]

    rule [bytes-concat-right-assoc-symb-l]: (B1:Bytes +Bytes B2:Bytes) +Bytes B3:Bytes => B1 +Bytes (B2 +Bytes B3) [symbolic(B1), simplification]
    rule [bytes-concat-right-assoc-symb-r]: (B1:Bytes +Bytes B2:Bytes) +Bytes B3:Bytes => B1 +Bytes (B2 +Bytes B3) [symbolic(B2), simplification]
    rule [bytes-concat-left-assoc-conc]:    B1:Bytes +Bytes (B2:Bytes +Bytes B3:Bytes) => (B1 +Bytes B2) +Bytes B3 [concrete(B1, B2), symbolic(B3), simplification]

    // #buf

    rule [buf-inject-k]:
      #buf(W:Int, X:Int) ==K #buf(W:Int, Y:Int) => X ==Int Y
      requires 0 <=Int W
       andBool #rangeUInt (8 *Int W, X)
       andBool #rangeUInt (8 *Int W, Y)
      [simplification]

    rule [buf-inject-ml]:
      { #buf(W:Int, X:Int) #Equals #buf(W:Int, Y:Int) } => { X #Equals Y }
      requires 0 <=Int W
       andBool #rangeUInt (8 *Int W, X)
       andBool #rangeUInt (8 *Int W, Y)
      [simplification]

    rule [buf-as-int-left]:  B:Bytes   ==K #buf(32, X:Int) => X ==Int #asInteger(B) requires lengthBytes(B) <=Int 32 [simplification, concrete(B)]
    rule [buf-as-int-right]: #buf(32, X:Int) ==K B:Bytes   => X ==Int #asInteger(B) requires lengthBytes(B) <=Int 32 [simplification, concrete(B)]

    rule [buf-asWord-invert]:
      #buf (W:Int , #asWord(B:Bytes)) => #buf(W -Int lengthBytes(B), 0) +Bytes B
      requires lengthBytes(B) <=Int W
      [simplification]

    rule [buf-zero-concat-base]:
      #buf(W1:Int, 0) +Bytes #buf(W2:Int, 0) => #buf(W1 +Int W2, 0)
      requires 0 <=Int W1 andBool 0 <=Int W2
      [simplification]

    rule [buf-zero-concat-conc]:
      #buf(W1:Int, 0) +Bytes #buf(W2:Int, 0) +Bytes B => #buf(W1 +Int W2, 0) +Bytes B
      requires 0 <=Int W1 andBool 0 <=Int W2
      [simplification]

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

    rule (#range(#range(BA:Bytes, S0, L0), S1, L1)) => #range(BA, S0 +Int S1, minInt(L1, L0 -Int S1)) +Bytes #buf(maxInt(0, L1 -Int (L0 -Int S1)), 0)
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

    rule #writeRange(MEM, K, BUF) => MEM +Bytes #buf(K -Int lengthBytes(MEM), 0) +Bytes BUF
      requires lengthBytes(MEM) <=Int K [simplification]

    // lengthBytes

    rule [lengthBytes-geq-zero]: 0 <=Int lengthBytes ( _ )                     => true                                                [simplification, smt-lemma]
    rule [lengthBytes-concat]:   lengthBytes(BUF1 +Bytes BUF2)                 => lengthBytes(BUF1) +Int lengthBytes(BUF2)            [simplification]
    rule [lengthBytes-buf]:      lengthBytes(#buf(SIZE, _))                    => SIZE   requires 0 <=Int SIZE                        [simplification]
    rule [lengthBytes-range]:    lengthBytes(#range(_, START, WIDTH))          => WIDTH  requires 0 <=Int START andBool 0 <=Int WIDTH [simplification]
    rule [lengthBytes-prtw]:     lengthBytes(#padRightToWidth(W:Int, B:Bytes)) => maxInt(lengthBytes(B), W)                           [simplification]

    rule [lengthBytes-leq-zero]: lengthBytes(B:Bytes) <=Int 0 => B ==K .Bytes [simplification]

    // #asWord

    rule #asWord(WS) >>Int M => #asWord(#range(WS, 0, lengthBytes(WS) -Int (M /Int 8) ))  requires 0 <=Int M andBool M modInt 8 ==Int 0 [simplification]

    rule #asWord(#padRightToWidth(32, BUF)) &Int notMaxUInt224 => #asWord(#padRightToWidth(32, BUF))
      requires lengthBytes(BUF) <=Int 4 [simplification]

    rule #padToWidth(32, #asByteStack(V)) => #buf(32, V)  requires #rangeUInt(256, V) [simplification]

    // #ecrec

    rule lengthBytes ( #ecrec ( _ , _ , _ , _ ) ) <=Int 32 => true
        [simplification, smt-lemma]

    rule #asWord ( #ecrec ( _ , _ , _ , _ ) ) <Int pow160 => true
        [simplification, smt-lemma]

endmodule
