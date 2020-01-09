requires "evm.k"
requires "edsl2.k"

module VERIFICATION
    imports EVM
    imports EDSL2

    rule .Bytes +Bytes BS => BS [simplification]
    rule BS +Bytes .Bytes => BS [simplification]

    rule lengthBytes(B1 +Bytes B2) => lengthBytes(B1) +Int lengthBytes(B2) [simplification]

    rule lengthBytes(#buf(N, _)) => N [simplification]
    rule lengthBytes(#bufSeg(_, _, WIDTH)) => WIDTH [simplification]

    rule (BUF1 +Bytes BUF2)[START .. WIDTH] => (BUF1[START .. lengthBytes(BUF1) -Int START]) +Bytes (BUF2[0 .. START +Int WIDTH -Int lengthBytes(BUF1)])
      requires #range(0 <= START < lengthBytes(BUF1))
       andBool lengthBytes(BUF1) <Int START +Int WIDTH [simplification]

    rule (BUF1 +Bytes BUF2)[START .. WIDTH] => BUF1[START .. WIDTH]
      requires #range(0 <= START < lengthBytes(BUF1))
       andBool START +Int WIDTH <=Int lengthBytes(BUF1) [simplification]

    rule (BUF1 +Bytes BUF2)[START .. WIDTH] => BUF2[START -Int lengthBytes(BUF1) .. WIDTH]
      requires lengthBytes(BUF1) <=Int START [simplification]

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

    rule #asWord(#buf(SIZE, DATA)) => DATA requires SIZE <=Int 32 andBool #range(0 <= DATA < (2 ^Int (SIZE *Int 8))) [simplification]


    // Following two rules will cause the haskell backend to print "Failed to decide predicate" warning when MASK is matched by a variable.
    // 0xffff...f &Int N = N
    // rule MASK &Int N => N  requires MASK ==Int (2 ^Int (log2Int(MASK) +Int 1)) -Int 1 // MASK = 0xffff...f
    //                        andBool 0 <=Int N andBool N <=Int MASK

    // N &Int 0xffff...f = N
    // rule N &Int MASK => N  requires MASK ==Int (2 ^Int (log2Int(MASK) +Int 1)) -Int 1 // MASK = 0xffff...f
    //                        andBool 0 <=Int N andBool N <=Int MASK

    rule maxUInt160 &Int N => N requires #rangeUInt(160, N) [simplification]

    rule N &Int maxUInt160 => N requires #rangeUInt(160, N) [simplification]

    rule #padToWidth(32, #asByteStack(V)) => #buf(32, V)
      requires #rangeUInt(256, V) [simplification]

    // included: [START0..[START..END]..END0]
    rule #range(storeRange(M, START0, WIDTH0, WS), START, WIDTH) => WS [ START -Int START0 .. WIDTH ]
      requires START0 <=Int START andBool START +Int WIDTH <=Int START0 +Int WIDTH0 [simplification]

    // no overlap: [START..END]..[START0..END0]  or  [START0..END0]..[START..END]
    rule #range(storeRange(M, START0, WIDTH0, WS), START, WIDTH) => #range(M, START, WIDTH)
      requires ( (START +Int WIDTH) <=Int START0 orBool (START0 +Int WIDTH0) <=Int START ) [simplification]

    // left  margin: [START..(START0..END]..END0)  or  [START..(START0..END0)..END]
    rule #range(storeRange(M, START0, WIDTH0, WS), START, WIDTH) => #range(M, START, START0 -Int START)
                                                                 ++ #range(storeRange(M, START0, WIDTH0, WS), START0, (START +Int WIDTH) -Int START0)
      requires START <Int START0 andBool START0 <Int START +Int WIDTH
       andBool WIDTH0 >=Int 1 [simplification] // to avoid unnecessary split

    // right margin: (START0..[START..END0)..END]  or  [START..(START0..END0)..END]
    rule #range(storeRange(M, START0, WIDTH0, WS), START, WIDTH) => #range(storeRange(M, START0, WIDTH0, WS), START, (START0 +Int WIDTH0) -Int START)
                                                                 ++ #range(M, START0 +Int WIDTH0, (START +Int WIDTH) -Int (START0 +Int WIDTH0))
      requires START <Int START0 +Int WIDTH0 andBool START0 +Int WIDTH0 <Int START +Int WIDTH
       andBool WIDTH0 >=Int 1 [simplification] // to avoid unnecessary split


endmodule
