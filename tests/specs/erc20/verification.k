requires "abstract-semantics-segmented-gas.k"
requires "edsl.k"
requires "evm-symbolic.k"

module VERIFICATION
    imports ABSTRACT-SEMANTICS-SEGMENTED-GAS
    imports EDSL
    imports EVM-SYMBOLIC

    //semantics of #buf (This is wrong!!!! see the correct one in the edsl.md)
    //rule #buf(LEN, BYTES) => #padToWidth(LEN, #asByteStack( BYTES )) [concrete]

    //Rules for #padToWidth with non-regular symbolic arguments.
    rule #padToWidth(32, #asByteStack(V)) => #buf(32, V)
      requires 0 <=Int V andBool V <Int pow256

    rule chop ( W0:Int +Int W1:Int ) -Word W1:Int => chop ( W0 )
      requires #rangeUInt(256, W0) andBool #rangeUInt(256, W1)

    rule #sizeByteArray(#bufSeg(_, _, WIDTH)) => WIDTH [simplification]

    rule (BUF1 ++ BUF2)[START .. WIDTH] => (BUF1[START .. #sizeByteArray(BUF1) -Int START]) ++ (BUF2[0 .. START +Int WIDTH -Int #sizeByteArray(BUF1)])
      requires #range(0 <= START < #sizeByteArray(BUF1))
       andBool #sizeByteArray(BUF1) <Int START +Int WIDTH [simplification]

    rule (BUF1 ++ BUF2)[START .. WIDTH] => (BUF1[START .. WIDTH])
      requires #range(0 <= START < #sizeByteArray(BUF1))
       andBool START +Int WIDTH <=Int #sizeByteArray(BUF1) [simplification]

    rule #buf(SIZE, DATA)[START .. WIDTH] => #bufSeg(#buf(SIZE, DATA), START, WIDTH)
       requires #range(0 <= START < SIZE)
       andBool #range(0 < WIDTH <= SIZE -Int START) [simplification]

    rule #bufSeg(WS, START, WIDTH) => WS requires START ==Int 0 andBool WIDTH ==Int #sizeByteArray(WS) [simplification]

    rule #Ceil(#buf(@SIZE, @DATA)) => {(@SIZE >=Int 0) #Equals true} #And #Ceil(@SIZE) #And #Ceil(@DATA) [anywhere]

    rule #Ceil(#bufSeg(@BUF, @START, @WIDTH))
           => {(@START >=Int 0) #Equals true} #And {(@WIDTH >=Int 0) #Equals true} #And {(@START +Int @WIDTH <=Int #sizeByteArray(@BUF)) #Equals true} #And #Ceil(@START) #And #Ceil(@WIDTH) #And #Ceil(@BUF) [anywhere]


endmodule
