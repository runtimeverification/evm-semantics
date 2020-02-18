requires "edsl.k"

module VERIFICATION
    imports EDSL

    rule WS ++ .ByteArray => WS  [simplification]
    rule .ByteArray ++ WS => WS  [simplification]

    rule #sizeByteArray(BUF1 ++ BUF2)  => #sizeByteArray(BUF1) +Int #sizeByteArray(BUF2)  [simplification]
    rule #sizeByteArray(#buf(N, _)  )  => N                                               [simplification]
    rule #sizeByteArray(#bufSeg(_, _, WIDTH)) => WIDTH                                    [simplification]

    rule (BUF1 ++ BUF2)[START .. WIDTH] => (BUF1[START .. #sizeByteArray(BUF1) -Int START]) ++ (BUF2[0 .. START +Int WIDTH -Int #sizeByteArray(BUF1)])
      requires #range(0 <= START < #sizeByteArray(BUF1))
       andBool #sizeByteArray(BUF1) <Int START +Int WIDTH [simplification]

    rule (BUF1 ++ BUF2)[START .. WIDTH] => (BUF1[START .. WIDTH])
      requires #range(0 <= START < #sizeByteArray(BUF1))
       andBool START +Int WIDTH <=Int #sizeByteArray(BUF1) [simplification]

    rule (BUF1 ++ BUF2)[START .. WIDTH] => BUF2 [START -Int #sizeByteArray(BUF1) .. WIDTH]
      requires START >=Int #sizeByteArray(BUF1) [simplification]

    rule #buf(SIZE, DATA)[START .. WIDTH] => #bufSeg(#buf(SIZE, DATA), START, WIDTH)
       requires #range(0 <= START < SIZE)
       andBool #range(0 < WIDTH <= SIZE -Int START) [simplification]

    rule #bufSeg(WS, START, WIDTH) => WS requires START ==Int 0 andBool WIDTH ==Int #sizeByteArray(WS) [simplification]

    rule #Ceil(#buf(@SIZE, @DATA)) => {(@SIZE >=Int 0) #Equals true} #And #Ceil(@SIZE) #And #Ceil(@DATA) [anywhere]

    rule #Ceil(#bufSeg(@BUF, @START, @WIDTH))
           => {(@START >=Int 0) #Equals true} #And {(@WIDTH >=Int 0) #Equals true} #And {(@START +Int @WIDTH <=Int #sizeByteArray(@BUF)) #Equals true} #And #Ceil(@START) #And #Ceil(@WIDTH) #And #Ceil(@BUF) [anywhere]

    rule #asWord(BUF) /Int D => #asWord(BUF[0 .. #sizeByteArray(BUF) -Int log256Int(D)])
      requires D ==Int 256 ^Int log256Int(D) andBool D >=Int 0
       andBool #sizeByteArray(BUF) >=Int log256Int(D) [simplification]

    rule #padToWidth(32, #asByteStack(V)) => #buf(32, V)
      requires #rangeUInt(256, V) [simplification]

    rule #asWord(#buf(N, BUF)) => BUF
      requires #range(0 < N <= 32)
       andBool #range(0 <= BUF < 2 ^Int (N *Int 8)) [simplification]

    rule N &Int maxUInt160 => N
      requires #rangeUInt(160, N) [simplification]

    rule maxUInt160 &Int N => N
      requires #rangeUInt(160, N) [simplification]

    rule #range(M, N, K) => .ByteArray requires notBool K >Int 0  [simplification]

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

    rule 0 <=Int keccak(V)                  => true  [simplification]
    rule         keccak(V) <=Int maxUInt256 => true  [simplification]

endmodule
