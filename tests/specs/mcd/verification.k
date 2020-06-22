requires "../lemmas.k"
requires "bin_runtime.k"

module VERIFICATION
    imports LEMMAS
    imports BIN_RUNTIME

    syntax Bool ::= #notPrecompileAddress ( Int ) [function]
 // --------------------------------------------------------
    rule #notPrecompileAddress ( X ) => 0 ==Int X orBool (10 <=Int X andBool #rangeAddress(X))

    // arithmetic/data-structures
    rule I modInt N => I requires 0 <=Int I andBool I <Int N
    rule I in (SetItem(I') REST) => I in REST requires I =/=Int I'

    // chop
    rule chop(hash2(V1, V2) +Int 1) => hash2(V1, V2) +Int 1

    // sizeWordStack/sizeByteArray
    // rule #sizeWordStack(WS1 ++ WS2, N)                       => #sizeWordStack(WS1) +Int #sizeWordStack(WS2) +Int N
    // rule #sizeWordStack(#padToWidth(32, #asByteStack(I)), N) => N +Int 32 requires 0 <=Int I andBool I <Int pow256
    // rule #sizeWordStack(#take(WIDTH, _)       , N)           => WIDTH +Int N
    // rule #sizeWordStack(WS [ START .. WIDTH ] , N)           => WIDTH +Int N
    rule #sizeByteArray(WS ++ WS')                        => #sizeByteArray(WS) +Int #sizeByteArray(WS')
    rule #sizeByteArray(#padToWidth(32, #asByteStack(I))) => 32 requires 0 <=Int I andBool I <Int pow256
    rule #sizeByteArray(WS [ START .. WIDTH ])            => WIDTH

    rule 0 <=Int #sizeWordStack(_, _) => true [smt-lemma]
    rule 0 <=Int #sizeByteArray(_)    => true [smt-lemma]

    // ranged lookups in ByteArray
    rule (WS ++ WS') [ START .. WIDTH ] => WS  [ START                         .. WIDTH ] requires START +Int WIDTH <=Int #sizeByteArray(WS)
    rule (WS ++ WS') [ START .. WIDTH ] => WS' [ START -Int #sizeByteArray(WS) .. WIDTH ] requires #sizeByteArray(WS) <=Int START

    rule (W0 : WS) [ 0     .. WIDTH ] => W0 : (WS [ 0 .. WIDTH -Int 1 ]) requires 0 <Int WIDTH
    rule (_  : WS) [ START .. WIDTH ] => WS [ START -Int 1 .. WIDTH ]    requires 0 <Int START

    // #asWord
    rule #asWord(WS) >>Int M                           => #asWord(WS [ 0 .. #sizeByteArray(WS) -Int (M /Int 8) ]) requires 0 <=Int M andBool M modInt 8 ==Int 0
    rule #asWord(#padToWidth(32, #asByteStack(VALUE))) => VALUE                                                   requires 0 <=Int VALUE andBool VALUE <Int pow256

    // #unsigned
    rule #unsigned(#sizeWordStack(WS, N) +Int M) => #sizeWordStack(WS, N) +Int M requires 0 <=Int M andBool #sizeWordStack(WS, N) +Int M <Int maxSInt256

    // #storage lookup
    rule #lookup(MAP [ KEY <- VALUE ], KEY') => #lookup(MAP, KEY') requires KEY =/=K KEY'
    rule #lookup(MAP [ KEY <- VALUE ], KEY') => VALUE              requires KEY  ==K KEY'

    // key differences
    // rule hash2(_, _)        ==K 1                     => false
    // rule hash2(_, _) +Int I ==K 1                     => false requires I =/=Int 0
    // rule hash2(_, _)        ==K 0                     => false
    // rule hash2(_, _) +Int I ==K 0                     => false requires I =/=Int 0
    // rule hash2(_, 5)        ==K hash2(_, hash2(_, _)) => false
    // rule hash2(V1, _)       ==K hash2(V2, _)          => false requires V1 =/=Int V2
    // rule I                  ==K I +Int 1              => false
    // rule #newAddr(_, _)     ==K 0                     => false
    // rule hash2(_, V1)       ==K hash2(_, V2)          => false requires V1 =/=Int V2
    // rule 1                  ==K hash2(_, _)           => false
    // rule hash2(_, _) +Int I ==K hash2(_, _)           => false requires I =/=Int 0
    // rule hash2(_, _)        ==K hash2(_, _) +Int I    => false requires I =/=Int 0
    // rule 1                  ==K hash2(_, _) +Int I    => false

    rule 24465873643947496235832446106509767096567058095563226156125564318740882468608 ==K hash2(_, _) => false

    // ranged lookups in Memory
    rule #range(MAP [ KEY <- _           ] => MAP, START, WIDTH)                       requires START +Int WIDTH <=Int KEY
    rule #range(MAP [ KEY := BUF         ]       , START, WIDTH) => BUF [ 0 .. WIDTH ] requires KEY ==Int START andBool WIDTH <=Int #sizeByteArray(BUF)
    rule #range(MAP [ KEY := _:ByteArray ] => MAP, START, WIDTH)                       requires START +Int WIDTH <=Int KEY
    // rule #range(MAP [ KEY := BA:ByteArray ] => MAP, END, WIDTH, WS) requires END <Int KEY orBool KEY +Int WIDTH +Int #sizeWordStack(BA) -Int 1 <=Int END
    // rule #range(MAP [ KEY <- _            ] => MAP, END, WIDTH, WS) requires END <Int KEY orBool KEY +Int WIDTH                                <=Int END
    // rule #range(MAP [ KEY <- V ], START, WIDTH) => #range(MAP [ KEY <- V ], START, WIDTH -Int 1) ++ V : .ByteArray requires KEY ==Int START +Int WIDTH -Int 1
    // rule #range(MAP [ KEY <- VALUE ], KEY => KEY -Int 1, WIDTH => WIDTH -Int 1, WS => VALUE : WS) requires 0 <Int WIDTH
    // rule #range(MAP [ KEY := BUF ], END => END -Int #sizeWordStack(BUF), WIDTH => WIDTH -Int #sizeWordStack(BUF), WS => BUF ++ WS) requires KEY +Int WIDTH -Int 1 ==Int END andBool #sizeWordStack(BUF) <=Int WIDTH

    // #computeValidJumpDests
    rule #computeValidJumpDests(#padToWidth(32, #asByteStack(ADDR)) => .ByteArray, I => I +Int 32, RESULT) requires 0 <=Int ADDR andBool ADDR <Int pow256

    // Memory assignment sorting/normalization
    rule MAP [ N := .ByteArray ] => MAP
    rule MAP [ N := W : WS     ] => MAP [ N <- W ] [ N +Int 1 := WS ]

    rule MAP:Memory [ N <- V           ] [ N' <- V' ] => MAP [ N' <- V' ] [ N <- V ] requires N'                          <Int N
    rule MAP:Memory [ N := V:ByteArray ] [ N' <- V' ] => MAP [ N' <- V' ] [ N := V ] requires N'                          <Int N orBool N +Int #sizeByteArray(V) <=Int N'
    rule MAP:Memory [ N := V:ByteArray ] [ N' := V' ] => MAP [ N' := V' ] [ N := V ] requires N' +Int #sizeByteArray(V') <=Int N
    rule MAP:Memory [ N <- V           ] [ N' := V' ] => MAP [ N' := V' ]            requires N' <=Int N andBool N <Int N' +Int #sizeByteArray(V')
endmodule
