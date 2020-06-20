requires "../lemmas.k"
requires "bin_runtime.k"

module VERIFICATION
    imports LEMMAS
    imports BIN_RUNTIME

    syntax Bool ::= #notPrecompileAddress ( Int ) [function]
 // --------------------------------------------------------
    rule #notPrecompileAddress ( X ) => 0 ==Int X orBool (10 <=Int X andBool #rangeAddress(X))

    // step 132 - could not simplify #sizeWordStack(#padToWidth(32, _), _) or #sizeWordStack(_ ++ _, _)
    rule #sizeWordStack(WS1 ++ WS2, N) => #sizeWordStack(WS1) +Int #sizeWordStack(WS2) +Int N
    rule #sizeWordStack(#padToWidth(32, #asByteStack(I)), N) => N +Int 32 requires 0 <=Int I andBool I <Int pow256

    // step 164 - sizeWordStack(_, _) + 68 <Int 4
    rule 0 <=Int #sizeWordStack(_, _) => true [smt-lemma]
    rule 0 <=Int #sizeByteArray(_) => true [smt-lemma]

    // step 262 - #asWord(((96 : 144 : 222 : 197 : #padToWidth(32, #asByteStack(ABI_ilk))) ++ #padToWidth(32, #asByteStack(ABI_usr)) ++ CD) [ 0 .. 32 ]) >>Int 224 <Int 2160673182
    rule #sizeWordStack(#take(WIDTH, _)       , N) => WIDTH +Int N
    rule #sizeWordStack(WS [ START .. WIDTH ] , N) => WIDTH +Int N
    rule (WS ++ WS') [ START .. WIDTH ] => WS [ START .. WIDTH ]           requires START +Int WIDTH <=Int #sizeWordStack(WS)
    rule (W0 : WS)   [ 0     .. WIDTH ] => W0 : (WS [ 0 .. WIDTH -Int 1 ]) requires 0 <Int WIDTH
    rule #asWord(WS) >>Int M => #asWord(WS [ 0 .. #sizeWordStack(WS) -Int (M /Int 8) ]) requires 0 <=Int M andBool M modInt 8 ==Int 0

    // step 730 - #unsigned(#sizeWordStack(CD, 0) +Int 64) <Int 64
    rule #unsigned(#sizeWordStack(WS, N) +Int M) => #sizeWordStack(WS, N) +Int M requires 0 <=Int M andBool #sizeWordStack(WS, N) +Int M <Int maxSInt256

    // step 811 - #asWord(#padToWidth(32, #asByteStack(ABI_ilk)))
    rule #asWord(#padToWidth(32, #asByteStack(VALUE))) => VALUE requires 0 <=Int VALUE andBool VALUE <Int pow256

    // step 1188 - maxUInt160 &Int #asWord((96 : (144 : (222 : (197 : (#padToWidth(32, #asByteStack(AB I_ilk)) ++ (#padToWidth(32, #asByteStack(ABI_usr)) ++ CD)))))) [ 36 .. 32 ])
    rule (WS ++ WS') [ START .. WIDTH ] => WS' [ START -Int #sizeWordStack(WS) .. WIDTH ] requires #sizeWordStack(WS) <=Int START
    rule (_ : WS) [ START .. WIDTH ] => WS [ START -Int 1 .. WIDTH ] requires 0 <Int START

    // step 1406 - #lookup(_39 [ 0                      <- Vat   ]
    //                         [ 1                      <- Cdpi  ]
    //                         [ hash2(Cdpi + 1, 2)     <- 0     ]
    //                         [ hash2(ABI_usr , 7)     <- Last  ]
    //                         [ hash2(ABI_usr , 8)     <- Count ]
    //                         [ hash2(Cdpi + 1, 4)     <- Own   ]
    //                         [ hash2(Cdpi + 1, 5)     <- Ilk   ]
    //                         [ hash2(ABI_usr , 6)     <- First ]
    //                         [ hash2(Cdpi + 1, 3)     <- Prev  ]
    //                         [ hash2(Last    , 3) + 1 <- Next  ]
    //                    , 1
    //                    )
    rule #lookup(MAP [ KEY <- VALUE ], KEY') => #lookup(MAP, KEY') requires KEY =/=K KEY'
    rule #lookup(MAP [ KEY <- VALUE ], KEY') => VALUE              requires KEY  ==K KEY'
    rule hash2(_, _)        ==K 1 => false
    rule hash2(_, _) +Int I ==K 1 => false requires I =/=Int 0
    rule hash2(_, _)        ==K 0 => false
    rule hash2(_, _) +Int I ==K 0 => false requires I =/=Int 0

    // step 1621 - vat-move-diff
    rule hash2(_, 5) ==K hash2(_, hash2(_, _)) => false

    // step 2309 - vat-move-diff
    rule hash2(V1, _) ==K hash2(V2, _) => false requires V1 =/=Int V2

    // step 1527 - Cdpi ==K (Cdpi +Int 1)
    rule I ==K I +Int 1 => false

    // step 2088 - 0 < #sizeByteArray(#padToWidth(32, #asByteStack(Vat)) + 292
    rule #sizeByteArray(#padToWidth(32, #asByteStack(I))) => 32 requires 0 <=Int I andBool I <Int pow256

    // step 2177 - DEST in #range(M [ 420 := #padToWidth(32, #asByteStack(_)) ], 420, 32)
    rule #range(MAP [ N := BUF ], START, WIDTH) => BUF requires N ==Int START andBool #sizeWordStack(BUF) ==Int WIDTH
    rule #computeValidJumpDests(#padToWidth(32, #asByteStack(ADDR)) => .WordStack, I => I +Int 32, RESULT) requires 0 <=Int ADDR andBool ADDR <Int pow256

    // step 2780 - MAP [ N := (W : WS) ]
    rule MAP [ N := .ByteArray ] => MAP
    rule MAP [ N := W : WS     ] => MAP [ N <- W ] [ N +Int 1 := WS ]

    // step 2893 - M [ N <- K ] [ M := BUF ]
    rule MAP:Memory [ N <- V           ] [ N' <- V' ] => MAP [ N' <- V' ] [ N <- V ] requires N'                          <Int N
    rule MAP:Memory [ N := V:ByteArray ] [ N' <- V' ] => MAP [ N' <- V' ] [ N := V ] requires N'                          <Int N orBool N +Int #sizeWordStack(V) <=Int N'
    rule MAP:Memory [ N := V:ByteArray ] [ N' := V' ] => MAP [ N' := V' ] [ N := V ] requires N' +Int #sizeWordStack(V') <=Int N
    rule MAP:Memory [ N <- V           ] [ N' := V' ] => MAP [ N' := V' ]            requires N' <=Int N andBool N <Int N' +Int #sizeWordStack(V')

    // step 2983 - #range(M [ 128 := _ ] [ 160 <- _ ] [ 161 <- _ ] [ 162 <- _ ] [ 163 <- _ ], 64, 32)
    rule #range(MAP [ KEY <- _           ] => MAP, KEY', WIDTH) requires KEY' +Int WIDTH <=Int KEY
    rule #range(MAP [ KEY := _:ByteArray ] => MAP, KEY', WIDTH) requires KEY' +Int WIDTH <=Int KEY

    // step 3067 - (Vat mod pow160) in (SetItem(Vat) ...)
    rule I modInt N => I requires 0 <=Int I andBool I <Int N

    // step 3187 - Vat in SetItem(1) ... SetItem(9)
    rule I in (SetItem(I') REST) => I in REST requires I =/=Int I'

    // step 3165 - #range(MAP [ N := #padToWidth(_, _) ] [ N' <- _ ], END, WIDTH, _)
    rule #range(MAP [ N := BA:ByteArray ] => MAP, END, WIDTH, WS) requires END <Int N orBool N +Int WIDTH +Int #sizeWordStack(BA) -Int 1 <=Int END
    rule #range(MAP [ N <- _            ] => MAP, END, WIDTH, WS) requires END <Int N orBool N +Int WIDTH                                <=Int END

    // step 3377 - #range(MAP [ 160 <- _ ] [ 161 <- _ ] [ 162 <- _ ] [ 163 <- _ ], 160, 4)
    rule #range(MAP [ KEY <- V ], KEY', WIDTH) => #range(MAP [ KEY <- V ], KEY', WIDTH -Int 1) ++ V : .ByteArray requires KEY ==Int KEY' +Int WIDTH -Int 1

    // step 3450 - #range(M [ N <- V ], N, W, WS)
    rule #range(MAP [ KEY <- VALUE ], KEY => KEY -Int 1, WIDTH => WIDTH -Int 1, WS => VALUE : WS) requires 0 <Int WIDTH

    // step 4271 - #range(M [ N := V ], E, W, WS)
    rule #range(MAP [ KEY := BUF ], END => END -Int #sizeWordStack(BUF), WIDTH => WIDTH -Int #sizeWordStack(BUF), WS => BUF ++ WS) requires KEY +Int WIDTH -Int 1 ==Int END andBool #sizeWordStack(BUF) <=Int WIDTH

    // step 5202 - #newAddr(ACCT_ID, Nonce_DssCdpManager) ==K 0
    rule #newAddr(_, _) ==K 0 => false

    // step 5497 - #lookup(M [ hash2(_, _) <- _ ], hash2(_, _) )
    rule hash2(_, V1)       =/=K hash2(_, V2) => true requires V1 =/=Int V2
    rule 1                  =/=K hash2(_, _)  => true
    rule hash2(_, _) +Int I =/=K hash2(_, _)  => true requires I =/=Int 0

    // step 7091 - #lookup(M [ N <- _ ], hash2(_, _))
    rule 24465873643947496235832446106509767096567058095563226156125564318740882468608 =/=K hash2(_, _) => true

    // step 8245 - #lookup(MAP [ chop(hash2(_, _) + 1) <- _ ], hash2(_, _))
    rule chop(hash2(V1, V2) +Int 1) => hash2(V1, V2) +Int 1
    rule hash2(_, _) =/=K hash2(_, _) +Int I => true requires I =/=Int 0
    rule 1           =/=K hash2(_, _) +Int I => true
endmodule
