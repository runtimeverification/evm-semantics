requires "../lemmas.k"
requires "bin_runtime.k"
requires "storage.k"

module HASKELL-HASH2 [symbolic, kore]
    imports EDSL

    syntax Int ::= hash2(Int, Int) [function]
 // -----------------------------------------
endmodule

module VERIFICATION
    imports LEMMAS
    imports DSS-BIN-RUNTIME
    imports DSS-STORAGE
    imports HASKELL-HASH2

    syntax Bool ::= #notPrecompileAddress ( Int ) [function]
 // --------------------------------------------------------
    rule #notPrecompileAddress ( X ) => 0 ==Int X orBool (10 <=Int X andBool #rangeAddress(X))

    // arithmetic/data-structures
    rule I modInt N => I requires 0 <=Int I andBool I <Int N
    rule I in (SetItem(I') REST) => I in REST requires I =/=Int I'

    // chop
    rule chop(hash2(V1, V2) +Int 1) => hash2(V1, V2) +Int 1

    // sizeWordStack/sizeByteArray
    rule #sizeByteArray(WS ++ WS')                        => #sizeByteArray(WS) +Int #sizeByteArray(WS')
    rule #sizeByteArray(#padToWidth(32, #asByteStack(I))) => 32 requires 0 <=Int I andBool I <Int pow256
    rule #sizeByteArray(WS [ START .. WIDTH ])            => WIDTH

    rule 0 <=Int #sizeWordStack(_, _) => true [smt-lemma]
    rule 0 <=Int #sizeByteArray(_)    => true [smt-lemma]

    // ranged lookups in ByteArray
    rule (WS ++ WS') [ 0 .. WIDTH ] => WS ++ (WS' [ 0 .. WIDTH -Int #sizeByteArray(WS) ]) requires #sizeByteArray(WS) <=Int WIDTH

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
    rule hash2(_, 5)  ==K hash2(_, hash2(_, _)) => false                              // vat final implication
    rule hash2(V1, _) ==K hash2(V2, _)          => false requires V1 =/=Int V2        // vat step 2674

    // ranged lookups in Memory
    rule #range(MAP [ KEY <- _           ] => MAP, START, WIDTH)                       requires START +Int WIDTH <=Int KEY
    rule #range(MAP [ KEY := BUF         ]       , START, WIDTH) => BUF [ 0 .. WIDTH ] requires KEY ==Int START andBool WIDTH <=Int #sizeByteArray(BUF)
    rule #range(MAP [ KEY := _:ByteArray ] => MAP, START, WIDTH)                       requires START +Int WIDTH <=Int KEY

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
