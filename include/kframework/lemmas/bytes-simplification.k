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

    rule [bytes-equal-concat-split-ml]:
      { A:Bytes +Bytes B:Bytes #Equals C:Bytes +Bytes D:Bytes } => { A #Equals C } #And { B #Equals D }
      requires lengthBytes(A) ==Int lengthBytes(C)
      [simplification]

    rule [bytes-concat-empty-right]: B:Bytes +Bytes .Bytes  => B [simplification]
    rule [bytes-concat-empty-left]:   .Bytes +Bytes B:Bytes => B [simplification]

    rule [bytes-concat-right-assoc-symb-l]: (B1:Bytes +Bytes B2:Bytes) +Bytes B3:Bytes => B1 +Bytes (B2 +Bytes B3) [symbolic(B1), simplification]
    rule [bytes-concat-right-assoc-symb-r]: (B1:Bytes +Bytes B2:Bytes) +Bytes B3:Bytes => B1 +Bytes (B2 +Bytes B3) [symbolic(B2), simplification]
    rule [bytes-concat-left-assoc-conc]   : B1:Bytes +Bytes (B2:Bytes +Bytes B3:Bytes) => (B1 +Bytes B2) +Bytes B3 [concrete(B1, B2), symbolic(B3), simplification]

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

    rule [range-inside-cHead]:
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

    rule [range-join-conc]:
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

    rule [range-reform-conc]:
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
      #range(#writeRange(B1:Bytes, S1:Int, _:Bytes), S2:Int, W2:Int) => #range(B1, S2, W2)
      requires 0 <=Int S1 andBool 0 <=Int W2 andBool S1 +Int lengthBytes(B1) <=Int S2 [simplification]

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

    // lengthBytes

    rule [lengthBytes-geq-zero]    : 0 <=Int lengthBytes(_:Bytes)                       => true                                           [simplification, smt-lemma]
    rule [lengthBytes-concat]      : lengthBytes(B1:Bytes +Bytes B2:Bytes)              => lengthBytes(B1) +Int lengthBytes(B2)           [simplification]
    rule [lengthBytes-buf]         : lengthBytes(#buf(W:Int, _:Int))                    => W requires 0 <=Int W                           [simplification]
    rule [lengthBytes-range]       : lengthBytes(#range(_:Bytes, S:Int, W:Int))         => maxInt(0, W) requires 0 <=Int S                [simplification]
    rule [lengthBytes-prtw-leq-len]: lengthBytes(#padRightToWidth(W:Int, B:Bytes))      => W requires lengthBytes(B) <Int W               [simplification]
    rule [lengthBytes-prtw-len-gt] : lengthBytes(#padRightToWidth(W:Int, B:Bytes))      => lengthBytes(B) requires W <=Int lengthBytes(B) [simplification]
    rule [lengthBytes-padleft]     : lengthBytes(padLeftBytes(B:Bytes, W:Int, _:Int) )  => maxInt(lengthBytes(B), W)                      [simplification]
    rule [lengthBytes-padright]    : lengthBytes(padRightBytes(B:Bytes, W:Int, _:Int) ) => maxInt(lengthBytes(B), W)                      [simplification]

    rule [lengthBytes-leq-zero]: lengthBytes(B:Bytes) <=Int 0 => B ==K .Bytes [simplification]

    // #padRightToWidth

    rule [padrighttowidth-def-leq-len]:
      #padRightToWidth(W:Int, B:Bytes) => B
      requires 0 <=Int W andBool W <=Int lengthBytes(B)
      [simplification]

    rule [padrighttowidth-def-len-gt]:
      #padRightToWidth(W:Int, B:Bytes) => B +Bytes #buf(W -Int lengthBytes(B), 0)
      requires 0 <=Int W andBool lengthBytes(B) <Int W
      [simplification]

    // #asWord

    rule [asWord-params-equal-ml]:
      { #asWord(B1:Bytes) #Equals #asWord(B2:Bytes) } => #Top
      requires B1 ==K B2
      [simplification]

    rule [asWord-geq-zero]:
      0 <=Int #asWord(_:Bytes) => true
      [simplification, smt-lemma]

    rule [asWord-leq-pow256]:
      #asWord(B:Bytes) <Int pow256 => true
      requires lengthBytes(B) <=Int 32
      [simplification]

    // PETAR: these last three are uncategorised artefacts from before upstreaming

    rule #padToWidth(32, #asByteStack(X:Int)) => #buf(32, X) requires #rangeUInt(256, X) [simplification]

    rule #asWord(B:Bytes) >>Int N:Int => #asWord(#range(B, 0, lengthBytes(B) -Int (N /Int 8) ))
      requires 0 <=Int N andBool N modInt 8 ==Int 0
      [simplification]

    rule #asWord(#padRightToWidth(32, B:Bytes)) &Int notMaxUInt224 => #asWord(#padRightToWidth(32, B))
      requires lengthBytes(B) <=Int 4 [simplification]

endmodule
