module BYTES-SIMPLIFICATION [symbolic]
    imports INT-SYMBOLIC
    imports EVM
    imports BUF

  //
  // concatHead/concatTail
  //

    syntax Bytes ::= concatHead(Bytes) [function, total] // Leftmost operand in a concat
                   | concatTail(Bytes) [function, total] // Rest of concat

    rule [concatHead-ind]:  concatHead(BA1 +Bytes _) => concatHead(BA1) [simplification(40)]
    rule [concatHead-base]: concatHead(BA)           => BA              [simplification    ]

    rule [concatTail-ind]:  concatTail(BA1 +Bytes BA2) => concatTail(BA1) +Bytes BA2 [simplification(40)]
    rule [concatTail-base]: concatTail(_)              => .Bytes                     [simplification    ]

  // ########################
  // Buffer Reasoning
  // ########################

    rule 0 <=Int lengthBytes ( _ ) => true [smt-lemma, simplification]

    rule BA:Bytes   ==K #buf(32, DATA) => #buf(32, DATA) ==K              BA                                    [simplification, concrete(BA)]
    rule #buf(32, DATA) ==K BA:Bytes   =>          DATA  ==Int #asInteger(BA) requires lengthBytes(BA) <=Int 32 [simplification, concrete(BA)]

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

    rule WS         +Bytes .Bytes => WS  [simplification]
    rule .Bytes +Bytes WS         => WS  [simplification]

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

    // re-order assignments
    rule #writeRange(#writeRange(MEM, K1, BUF1:Bytes), K2, BUF2:Bytes) => #writeRange(#writeRange(MEM, K2, BUF2), K1, BUF1)
      requires lengthBytes(BUF2) <=Int K1 -Int K2 andBool K2  <Int K1 [simplification]

    // overwritten assignment
    rule #writeRange(#writeRange(MEM, K1, BUF1), K2, BUF2) => #writeRange(MEM, K2, BUF2)
      requires K1 +Int lengthBytes(BUF1) <=Int K2 +Int lengthBytes(BUF2) andBool K2 <=Int K1 [simplification]

    // lookup range in memory
    rule #range(MEM, 0, W) => MEM  requires W ==Int lengthBytes(MEM) [simplification]

    // lookup range in concatenated memory buffers
    rule #range((BUF1 +Bytes  BUF2), START, WIDTH) =>  #range(BUF2, START -Int lengthBytes(BUF1), WIDTH                        )                                                                    requires                        lengthBytes(BUF1) <=Int START                                                          [simplification]
    rule #range((BUF1 +Bytes  _   ), START, WIDTH) =>  #range(BUF1, START                       , WIDTH                        )                                                                    requires START +Int WIDTH <=Int lengthBytes(BUF1)                       andBool 0 <=Int START andBool 0 <=Int WIDTH    [simplification]
    rule #range((BUF1 +Bytes  BUF2), START, WIDTH) => (#range(BUF1, START                       , lengthBytes(BUF1) -Int START)) +Bytes (#range(BUF2, 0, START +Int WIDTH -Int lengthBytes(BUF1)))  requires                        lengthBytes(BUF1) <Int START +Int WIDTH andBool #range(0 <= START < lengthBytes(BUF1)) [simplification]

    // lengthBytes

    rule lengthBytes(BUF1 +Bytes BUF2)             => lengthBytes(BUF1) +Int lengthBytes(BUF2)            [simplification]
    rule lengthBytes(#buf(SIZE, _))                => SIZE                                                [simplification]
    rule lengthBytes(#range(_, START, WIDTH))      => WIDTH  requires 0 <=Int START andBool 0 <=Int WIDTH [simplification]
    rule lengthBytes(#padRightToWidth(WIDTH, BUF)) => WIDTH  requires lengthBytes(BUF) <=Int WIDTH        [simplification]

    // TODO: custom ==K unification doesn't work in Haskell yet
    // +Bytes unification
    rule #buf(N, A) +Bytes BUF1 ==K #buf(N, B) +Bytes BUF2 => #buf(N, A) ==K #buf(N, B) andBool BUF1 ==K BUF2     [simplification]

    rule #padToWidth(32, #asByteStack(V)) => #buf(32, V)  requires #rangeUInt(256, V) [simplification]

    rule #asWord(WS) >>Int M => #asWord(#range(WS, 0, lengthBytes(WS) -Int (M /Int 8) ))  requires 0 <=Int M andBool M modInt 8 ==Int 0 [simplification]

    rule #asWord(#padRightToWidth(32, BUF)) &Int notMaxUInt224 => #asWord(#padRightToWidth(32, BUF))
      requires lengthBytes(BUF) <=Int 4 [simplification]

    rule #range(#padRightToWidth(_, BUF), 0, WIDTH) => BUF requires lengthBytes(BUF) ==Int WIDTH [simplification]

  //
  // Bytes
  //

    // Byte arrays cannot be equal if they are of different lengths
    rule [bytes-not-equal-length]:
      BA1:Bytes ==K BA2:Bytes => false
      requires lengthBytes(BA1) =/=Int lengthBytes(BA2)
      [simplification]

    // Equality split into head and tail equality
    rule [bytes-equal-concat-split]:
      { BA1:Bytes #Equals BA2:Bytes } =>
        { concatHead(BA1):Bytes #Equals concatHead(BA2):Bytes } #And
        { concatTail(BA1):Bytes #Equals concatTail(BA2):Bytes }
      requires (lengthBytes(concatHead(BA1)) =/=K lengthBytes(BA1) orBool lengthBytes(concatHead(BA2)) =/=K lengthBytes(BA2))
       andBool lengthBytes(concatHead(BA1)) ==Int lengthBytes(concatHead(BA2))
      [simplification]

  //
  // lengthBytes
  //

    // A byte array of non-positive length is empty
    rule [lengthBytes-leq-zero]:
      lengthBytes ( X ) <=Int 0 => X ==K .Bytes
      [simplification]

    // General range length
    rule [lengthBytes-range]:
      lengthBytes( #range( _, S, W ) ) => maxInt( 0, W )
      requires 0 <=Int S
      [simplification(60)]

    // Size of paddings
    rule [lengthBytes-pad-left]:
      lengthBytes ( padLeftBytes ( B:Bytes, WIDTH, _ ) ) => maxInt( lengthBytes(B), WIDTH )
      requires 0 <=Int WIDTH
      [simplification]

    rule [lengthBytes-pad-right]:
      lengthBytes ( padRightBytes ( B:Bytes, WIDTH, _ ) ) => maxInt( lengthBytes(B), WIDTH )
      requires 0 <=Int WIDTH
      [simplification]

  //
  // #range(M, START, WIDTH)
  //

    // Equality via parameter equality
    rule [range-params-equal]:
      { #range (A, B, C) #Equals #range (D, E, F) } => #Top
      requires A ==K D andBool B ==Int E andBool C ==Int F
      [simplification]

    // Range is empty if either the starting position or the width are negative
    rule [range-non-pos-empty]:
      #range( _, START, WIDTH ) => .Bytes
      requires START <Int 0 orBool WIDTH <=Int 0
      [simplification(40)]

    // Range is zero if start is outside of the bytearray
    rule [range-start-outside]:
      #range( BA, START, WIDTH ) => #buf ( WIDTH , 0 )
      requires lengthBytes(BA) <=Int START
       andBool 0 <=Int WIDTH
      [simplification(45)]

    // Interaction of range and memory update
    rule [range-writeRange]:
      #range( #writeRange(_:Bytes, N, BUF), N:Int, X:Int ) => BUF
      requires X ==Int lengthBytes(BUF) [simplification]

    // Starting position, possibly zero, outside head of concat]
    rule [range-outside-concatHead]:
      #range(M, START:Int, WIDTH:Int) =>
        #range(concatTail(M), START -Int lengthBytes(concatHead(M)), WIDTH)
      requires lengthBytes(concatHead(M)) =/=Int lengthBytes(M)
       andBool lengthBytes(concatHead(M)) <=Int START
      [simplification]

    // Starting position non-zero, within head of concat
    rule [range-inside-concatHead]:
      #range(M, START:Int, WIDTH:Int) =>
        #range(#range(concatHead(M), START, lengthBytes(concatHead(M)) -Int START) +Bytes concatTail(M), 0, WIDTH)
      requires lengthBytes(concatHead(M)) =/=Int lengthBytes(M)
       andBool 0 <Int START
       andBool START <Int lengthBytes(concatHead(M))
      [simplification]

    // Starting position zero, width greater than or equal to length of head of concat
    rule [range-includes-concathead]:
      #range(M, 0, WIDTH:Int) =>
        concatHead(M) +Bytes #range(concatTail(M), 0, WIDTH -Int lengthBytes(concatHead(M)))
      requires lengthBytes(concatHead(M)) <=Int WIDTH
      [simplification]

    // Starting position zero, width less than length of head of concat
    rule [range-included-in-concathead]:
      #range(M, 0, WIDTH:Int) => #range(concatHead(M), 0, WIDTH)
      requires lengthBytes(concatHead(M)) =/=Int lengthBytes(M)
       andBool WIDTH <Int lengthBytes(concatHead(M))
      [simplification]

  //
  // #buf
  //

    // Invertibility of #buf and #asWord
    rule [buf-asWord-invert]:
      #buf ( WIDTH , #asWord ( BA:Bytes ) ) => #buf(WIDTH -Int lengthBytes(BA), 0) +Bytes BA
      requires lengthBytes(BA) <=Int WIDTH
      [simplification]

    // Injectivity of #buf at the K and ML levels
    rule [buf-inject-ml]:
      { #buf ( N, X ) #Equals #buf ( N, Y ) } => { X #Equals Y }
      requires 0 <=Int N
        andBool 0 <=Int X andBool X <Int 2 ^Int ( 8 *Int N )
        andBool 0 <=Int Y andBool Y <Int 2 ^Int ( 8 *Int N )
      [concrete(N), simplification]

    rule [buf-inject-k]:
      #buf ( N, X ) ==K #buf ( N, Y ) => X ==Int Y
      requires 0 <=Int N
        andBool 0 <=Int X andBool X <Int 2 ^Int ( 8 *Int N )
        andBool 0 <=Int Y andBool Y <Int 2 ^Int ( 8 *Int N )
      [concrete(N), simplification]

  //
  // #padRightToWidth
  //

    rule [padright-conc-width]:
      #padRightToWidth (W, X) => X +Bytes #buf(W -Int lengthBytes(X), 0)
      requires lengthBytes(X) <=Int W
      [simplification]

  //
  // Memory update
  //

    // Memory update in terms of concat
    rule [writeRange-as-concat]:
      #writeRange(MEM, N, BUF) =>
      #range(MEM, 0, N) +Bytes ( BUF +Bytes #range ( MEM , N +Int lengthBytes(BUF) , lengthBytes(MEM) -Int ( N +Int lengthBytes(BUF) ) ) )
      requires 0 <=Int N
      [simplification]

endmodule
