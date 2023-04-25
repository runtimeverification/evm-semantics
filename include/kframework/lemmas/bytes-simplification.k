module BYTES-SIMPLIFICATION [symbolic]
    imports INT-SYMBOLIC
    imports EVM
    imports BUF

  // ########################
  // Buffer Reasoning
  // ########################

    rule BA:Bytes       ==K #buf(32, DATA) => #buf(32, DATA) ==K              BA                                    [simplification, concrete(BA)]
    rule #buf(32, DATA) ==K BA:Bytes       =>          DATA  ==Int #asInteger(BA) requires lengthBytes(BA) <=Int 32 [simplification, concrete(BA)]

    rule [bytes-concat-empty-right]: B:Bytes +Bytes .Bytes  => B [simplification]
    rule [bytes-concat-empty-left]:  .Bytes  +Bytes B:Bytes => B [simplification]

    rule [bytes-concat-assoc-right]: (BA1 +Bytes BA2) +Bytes BA3 => BA1 +Bytes (BA2 +Bytes BA3) [simplification]

    // #buf

    // TODO: custom ==K unification doesn't work in Haskell yet
    // +Bytes unification
    rule #buf(N, A) +Bytes BUF1 ==K #buf(N, B) +Bytes BUF2 => #buf(N, A) ==K #buf(N, B) andBool BUF1 ==K BUF2     [simplification]

    // #range

    rule [range-empty]:
      #range(_:Bytes, S:Int, W:Int) => .Bytes
      requires S <Int 0 orBool W <=Int 0
      [simplification(1)]

    rule [range-full]:
      #range(B:Bytes, 0, W:Int) => B
      requires lengthBytes(B) ==Int W
      [simplification]

    rule [range-overfull]:
      #range(B:Bytes, 0, W:Int) => B +Bytes #buf(W -Int lengthBytes(B), 0)
      requires lengthBytes(B) <Int W
      [simplification]

    rule [range-params-equal-ml]:
      { #range (B1:Bytes, S1:Int, W1:Int) #Equals #range (B2:Bytes, S2:Int, W2:Int) } => #Top
      requires B1 ==K B2 andBool S1 ==Int S2 andBool W1 ==Int W2
      [simplification]

    rule [range-included-in-cHead]:
      #range(B1:Bytes +Bytes _:Bytes, S:Int, W:Int) => #range(B1, S, W)
      requires S +Int W <=Int lengthBytes(B1)
      [simplification]

    rule [range-outside-cHead]:
      #range(B1:Bytes +Bytes B2:Bytes, S:Int, W:Int) => #range(B2, S -Int lengthBytes(B1), W)
      requires lengthBytes(B1) <=Int S
      [simplification]

    rule [range-includes-cHead]:
      #range(B1:Bytes +Bytes B2:Bytes, 0, W:Int) => B1 +Bytes #range(B2, 0, W -Int lengthBytes(B1))
      requires lengthBytes(B1) <=Int W
      [simplification]

    rule [range-inside-cHead-base-conc-left]:
      #range(B:Bytes, S1:Int +Int S2:Int, W:Int) => #range(#range(B, S1, lengthBytes(B) -Int S1), S2, W)
      requires 0 <Int S1 +Int S2 andBool S1 +Int S2 <=Int lengthBytes(B)
      [concrete(B), concrete(S1), simplification]

    rule [range-inside-cHead-base-conc-right]:
      #range(B:Bytes, S1:Int +Int S2:Int, W:Int) => #range(#range(B, S2, lengthBytes(B) -Int S2), S1, W)
      requires 0 <Int S1 +Int S2 andBool S1 +Int S2 <=Int lengthBytes(B)
      [concrete(B), concrete(S2), simplification]

    rule [range-inside-cHead-concat]:
      #range(B1:Bytes +Bytes B2:Bytes, S:Int, W:Int) => #range(#range(B1, S, lengthBytes(B1) -Int S) +Bytes B2, 0, W)
      requires 0 <Int S andBool S <=Int lengthBytes(B1)
      [simplification]

    rule [range-of-range]:
      #range(#range(B:Bytes, S1:Int, W1:Int), S2:Int, W2:Int) =>
        #range(B, S1 +Int S2, minInt(W2, W1 -Int S2)) +Bytes #buf(maxInt(0, W2 -Int (W1 -Int S2)), 0)
      requires 0 <=Int S1 andBool 0 <=Int W1 andBool 0 <=Int S2 andBool 0 <=Int W2
      [simplification]

    rule [range-join-base]:
      #range(B, S1, W1) +Bytes #range(B, S2, W2) => #range(B, S1, W1 +Int W2)
      requires S2 ==Int S1 +Int W1
       andBool 0 <=Int S1 andBool 0 <=Int W1 andBool 0 <=Int S2 andBool 0 <=Int W2
      [simplification]

    rule [range-join-concat]:
      #range(B1, S1, W1) +Bytes #range(B1, S2, W2) +Bytes B2 => #range(B1, S1, W1 +Int W2) +Bytes B2
      requires S2 ==Int S1 +Int W1
       andBool 0 <=Int S1 andBool 0 <=Int W1 andBool 0 <=Int S2 andBool 0 <=Int W2
      [simplification]

    rule [range-reform-base]:
      #range(B:Bytes, S:Int, minInt(W1:Int, W2:Int)) +Bytes #buf(maxInt(0, W3:Int), 0) => #range (B, S, W1)
      requires W2 ==Int lengthBytes(B) -Int S
       andBool W3 ==Int S +Int W1 -Int lengthBytes(B)
       andBool 0 <=Int S andBool 0 <=Int W1 andBool 0 <=Int W2
      [simplification]

    rule [range-reform-concat]:
      #range(B1:Bytes, S:Int, minInt(W1:Int, W2:Int)) +Bytes #buf(maxInt(0, W3:Int), 0) +Bytes B2:Bytes => #range (B1, S, W1) +Bytes B2
      requires W2 ==Int lengthBytes(B1) -Int S
       andBool W3 ==Int S +Int W1 -Int lengthBytes(B1)
       andBool 0 <=Int S andBool 0 <=Int W1 andBool 0 <=Int W2
      [simplification]

    rule [range-buf-zero-1]:
      #range(#buf(32, X:Int), 0, W:Int) => #buf(W, 0)
      requires 0 <=Int W andBool W <=Int 32
       andBool #rangeUInt (8 *Int (32 -Int W), X)
      [simplification, concrete(W)]

    rule [range-buf-zero-2]:
      #range(#buf(W:Int, 0), S1:Int, W1:Int) => #buf(W1, 0)
      requires 0 <=Int W andBool 0 <=Int S1 andBool 0 <=Int W
      [simplification]

    rule [range-writeRange-before]:
      #range(#writeRange(B1:Bytes, S1:Int, B2:Bytes), S2:Int, W2:Int) =>
        #let W = minInt(W2, S1 -Int S2) #in
          #range(B1, S2, W) +Bytes #range(#writeRange(B1, S1, B2), S1, W2 -Int W)
      requires S2 <Int S1
      [simplification]

    rule [range-writeRange-in-between]:
      #range(#writeRange(B1:Bytes, S1:Int, B2:Bytes), S2:Int, W2:Int) =>
        #let S = S2 -Int S1 #in
        #let W = minInt(W2, lengthBytes(B2) -Int S) #in
          #range(B2, S, W) +Bytes #range(B1, S1 +Int lengthBytes(B2), W2 -Int W)
      requires S1 <=Int S2 andBool S2 <=Int S1 +Int lengthBytes(B2)
      [simplification]

    rule [range-writeRange-outside]:
      #range(#writeRange(B1:Bytes, S1:Int, B2:Bytes), S2:Int, W2:Int) => #range(B1, S2, W2)
      requires 0 <=Int S1 andBool 0 <=Int W2 andBool S1 +Int lengthBytes(B2) <=Int S2 [simplification]

    rule [range-buf-zero]:
      #range (#buf(W1:Int, X:Int), S2:Int, W2:Int) => #buf(W2, 0)
      requires 0 <=Int X andBool X <Int 2 ^Int (8 *Int (W1 -Int (S2 +Int W2))) andBool S2 +Int W2 <=Int W1
      [simplification]

    rule [range-padRightToWidth]:
      #range(#padRightToWidth(_, BUF), 0, WIDTH) => BUF
      requires lengthBytes(BUF) ==Int WIDTH [simplification]

    // #writeRange

    rule [writeRange-is-empty]:
      #writeRange(_:Bytes, S:Int, _:Bytes) => .Bytes
      requires S <Int 0
      [simplification]

    rule [writeRange-as-concat-inside]:
      #writeRange(B1, S, B2:Bytes) =>
        #range(B1, 0, S) +Bytes B2 +Bytes #range (B1 , S +Int lengthBytes(B2), lengthBytes(B1) -Int ( S +Int lengthBytes(B2)))
      requires 0 <=Int S andBool S +Int lengthBytes(B2) <Int lengthBytes(B1)
      [simplification(60)]

    rule [writeRange-as-concat-outside]:
      #writeRange(B1, S, B2:Bytes) => #range(B1, 0, S) +Bytes B2
      requires 0 <=Int S andBool lengthBytes(B1) <=Int S +Int lengthBytes(B2)
      [simplification(60)]

    rule [writeRange-reorder]:
      #writeRange(#writeRange(B:Bytes, S1:Int, B1:Bytes), S2:Int, B2:Bytes) =>
        #writeRange(#writeRange(B, S2, B2), S1, B1)
      requires S2 <Int S1 andBool S2 +Int lengthBytes(B2) <=Int S1
      [simplification]

    rule [writeRange-subsume]:
      #writeRange(#writeRange(B:Bytes, S1:Int, B1:Bytes), S2:Int, B2:Bytes) => #writeRange(B, S2, B2)
      requires S2 <=Int S1 andBool S1 +Int lengthBytes(B1) <=Int S2 +Int lengthBytes(B2)
      [simplification]

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

    rule [lengthBytes-geq-zero]: 0 <=Int lengthBytes ( _ )                     => true                                     [simplification, smt-lemma]
    rule [lengthBytes-concat]:   lengthBytes(BUF1 +Bytes BUF2)                 => lengthBytes(BUF1) +Int lengthBytes(BUF2) [simplification]
    rule [lengthBytes-buf]:      lengthBytes(#buf(S, _))                       => S  requires 0 <=Int S                    [simplification]
    rule [lengthBytes-range]:    lengthBytes(#range(_, S:Int, W:Int))          => maxInt(0, W) requires 0 <=Int S          [simplification]
    rule [lengthBytes-prtw]:     lengthBytes(#padRightToWidth(W:Int, B:Bytes)) => maxInt(lengthBytes(B), W)                [simplification]

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
