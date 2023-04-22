requires "edsl.md"
requires "lemmas/lemmas.k"

module VERIFICATION
    imports EDSL
    imports LEMMAS

    syntax StepSort ::= Map | Bytes | Int | Bool
 // --------------------------------------------

    syntax KItem ::= runLemma ( StepSort )
                   | doneLemma( StepSort )
 // --------------------------------------
    rule runLemma( T ) => doneLemma( T )

endmodule

module LEMMAS-SPEC
    imports VERIFICATION

 // bool2Word
 // ---------

    claim <k> runLemma ( bool2Word((UINT8 ==K 0) ==K false) ) => doneLemma ( UINT8 ) ... </k> requires #rangeBool(UINT8)

 // sizeBytes
 // -------------

    claim <k> runLemma(lengthBytes(#padToWidth(32, #asByteStack(#hashedLocation("Solidity", 2, OWNER .IntList))))) => doneLemma(32) ... </k> requires #rangeUInt(256, OWNER)

 // Addresses
 // ---------

    claim <k> runLemma(#isPrecompiledAccount(#newAddr(TESTER_ACCT, 1), ISTANBUL)) => doneLemma(false) ... </k> requires #rangeAddress(TESTER_ACCT)

 // Arithmetic
 // ----------

    claim <k> runLemma(#rangeUInt(256, #lookup(M, KX) -Int #lookup(M, KY))) => doneLemma(true) ... </k>
      requires #rangeUInt(256, X) andBool X ==Int #lookup(M,  KX)
       andBool #rangeUInt(256, Y) andBool Y ==Int #lookup(M,  KY)
       andBool #rangeUInt(256, Z) andBool Z ==Int #lookup(M, _KZ)
       andBool #rangeUInt(256, (X -Int Y) -Int Z)

    claim [address-reprojection]: <k> runLemma(((maxUInt160 &Int ((368263281805664599098893944405654396525700029268 |Int (notMaxUInt160 &Int X:Int)) modInt pow256)) modInt pow160))
                                   => doneLemma(368263281805664599098893944405654396525700029268) ... </k>
                                requires #rangeUInt(256, X)

    claim [address-reprojection-1]: <k> runLemma(0 <=Int (368263281805664599098893944405654396525700029268 |Int (notMaxUInt160 &Int X:Int)))
                                     => doneLemma(true) ... </k>
                                  requires #rangeUInt(256, X)

    claim [address-reprojection-2]: <k> runLemma(0 <=Int (notMaxUInt160 &Int X:Int))
                                     => doneLemma(true) ... </k>
                                  requires #rangeUInt(256, X)

    claim [address-reprojection-4]: <k> runLemma((368263281805664599098893944405654396525700029268 |Int (notMaxUInt160 &Int X:Int)) <Int pow256)
                                     => doneLemma(true) ... </k>
                                  requires #rangeUInt(256, X)

    claim [address-reprojection-5]: <k> runLemma((notMaxUInt160 &Int X:Int) <Int pow256)
                                     => doneLemma(true) ... </k>
                                  requires #rangeUInt(256, X)

    claim [address-reprojection-6]: <k> runLemma(maxUInt160 &Int (368263281805664599098893944405654396525700029268 |Int (notMaxUInt160 &Int X:Int)))
                                     => doneLemma(368263281805664599098893944405654396525700029268) ... </k>
                                  requires #rangeUInt(256, X)

    claim [address-insertion-1]: <k> runLemma(368263281805664599098893944405654396525700029268 |Int (notMaxUInt160 &Int #lookup(ACCT_STORAGE:Map, 8)))
                                  => doneLemma(368263281805664599098893944405654396525700029268) ... </k>
                               requires #lookup(ACCT_STORAGE, 8) <Int pow160

 // Buffer write simplifications
 // ----------------------------

    // claim <k> runLemma ( M [ L := .Bytes ] [ N := WS:Bytes ]                             ) => doneLemma ( M [ N := WS ]                        ) ... </k> requires L <=Int N
    // claim <k> runLemma ( M [ L := WS:Bytes ] [ N := .Bytes ]                             ) => doneLemma ( M [ L := WS ]                        ) ... </k> requires N <=Int L
    // claim <k> runLemma ( M [ 32 := (0 : 1 : 2 : .Bytes) ] [ 32 := (3 : 4 : 5 : .Bytes) ] ) => doneLemma ( M [ 32 := (3 : 4 : 5 : .Bytes) ] ) ... </k>

    claim <k> runLemma ( M:Map [ I1 <- 1 ] [ I2 <- 2 ] ) => doneLemma ( M [ I1 <- 1 ] [ I2 <- 2 ] ) ... </k> requires I1  <Int I2
    claim <k> runLemma ( M:Map [ I1 <- 1 ] [ I2 <- 2 ] ) => doneLemma ( M [ I2 <- 2 ] [ I1 <- 1 ] ) ... </k> requires I1  >Int I2
    claim <k> runLemma ( M:Map [ I1 <- 1 ] [ I2 <- 2 ] ) => doneLemma ( M [ I1 <- 2 ]             ) ... </k> requires I1 ==Int I2
    claim <k> runLemma ( M:Map [ I1 <- 1 ] [ I2 <- 2 ] ) => doneLemma ( M [ I2 <- 2 ]             ) ... </k> requires I1 ==Int I2

    claim <k> runLemma( #writeRange( #writeRange( M:Bytes, 32, BA1 ), 32, BA2                                                                  )) => doneLemma(#writeRange(M:Bytes, 32, BA2                                                                  )) ... </k> requires lengthBytes(BA1) <=Int lengthBytes(BA2)
    claim <k> runLemma( #writeRange( #writeRange( M:Bytes, 32, BA1 ), 32, #padToWidth(32, #asByteStack(#hashedLocation("Solidity", 2, OWNER))) )) => doneLemma(#writeRange(M:Bytes, 32, #padToWidth(32, #asByteStack(#hashedLocation("Solidity", 2, OWNER))) )) ... </k> requires lengthBytes(BA1) ==Int 32 andBool #rangeUInt(256, OWNER)

    // #writeRange past the end of the buffer
    claim [write-past-end]: <k> runLemma  ( #writeRange ( #writeRange ( #writeRange ( #writeRange ( #buf(160, A) , 160 , #buf(32, B) ) , 192 , #buf(32, C) ) , 224 , #buf(32, D) ) , 256 , #buf(32, E) ) )
                             => doneLemma ( #buf(160, A) +Bytes #buf(32, B) +Bytes #buf(32, C) +Bytes #buf(32, D) +Bytes #buf(32, E) ) ... </k>

 // #lookup simplifications
 // -----------------------

    claim <k> runLemma ( #lookupMemory(( KEY |-> 33) (_KEY' |-> 728) (_KEY'' |-> (pow256 +Int 5)) (_KEY''' |-> "hello"), KEY)    ) => doneLemma ( 33  ) ... </k>
    claim <k> runLemma ( #lookupMemory((_KEY |-> 33) ( KEY' |-> 728) (_KEY'' |-> (pow256 +Int 5)) (_KEY''' |-> "hello"), KEY')   ) => doneLemma ( 216 ) ... </k>
    claim <k> runLemma ( #lookupMemory((_KEY |-> 33) (_KEY' |-> 728) ( KEY'' |-> (pow256 +Int 5)) (_KEY''' |-> "hello"), KEY'')  ) => doneLemma ( 5   ) ... </k>
    claim <k> runLemma ( #lookupMemory((_KEY |-> 33) (_KEY' |-> 728) (_KEY'' |-> (pow256 +Int 5)) ( KEY''' |-> "hello"), KEY''') ) => doneLemma ( 0   ) ... </k>
    //TODO Haskell limitation? https://github.com/runtimeverification/haskell-backend/issues/1948
    //claim <k> runLemma ( #lookupMemory((KEY |-> 33), KEY') ) => doneLemma ( 0 ) ... </k> requires notBool KEY' in_keys(KEY |-> 33)

    claim <k> runLemma ( #lookup(( KEY |-> 33) (_KEY' |-> 728) (_KEY'' |-> (pow256 +Int 5)) (_KEY''' |-> "hello"), KEY)    ) => doneLemma ( 33  ) ... </k>
    claim <k> runLemma ( #lookup((_KEY |-> 33) ( KEY' |-> 728) (_KEY'' |-> (pow256 +Int 5)) (_KEY''' |-> "hello"), KEY')   ) => doneLemma ( 728 ) ... </k>
    claim <k> runLemma ( #lookup((_KEY |-> 33) (_KEY' |-> 728) ( KEY'' |-> (pow256 +Int 5)) (_KEY''' |-> "hello"), KEY'')  ) => doneLemma ( 5   ) ... </k>
    claim <k> runLemma ( #lookup((_KEY |-> 33) (_KEY' |-> 728) (_KEY'' |-> (pow256 +Int 5)) ( KEY''' |-> "hello"), KEY''') ) => doneLemma ( 0   ) ... </k>
    //claim <k> runLemma ( #lookup((KEY |-> 33), KEY') ) => doneLemma ( 0 ) ... </k> requires notBool KEY' in_keys(KEY |-> 33)

    claim <k> runLemma ( #lookup( _M:Map [ KEY <- 33 ] [ KEY' <- 728 ] [ KEY'' <- (pow256 +Int 5) ] [ KEY''' <- "hello" ] , KEY    ) ) => doneLemma ( 33  ) ... </k> requires KEY =/=Int KEY' andBool KEY =/=Int KEY'' andBool KEY =/=Int KEY''' andBool KEY' =/=Int KEY'' andBool KEY' =/=Int KEY''' andBool KEY'' =/=Int KEY'''
    claim <k> runLemma ( #lookup( _M:Map [ KEY <- 33 ] [ KEY' <- 728 ] [ KEY'' <- (pow256 +Int 5) ] [ KEY''' <- "hello" ] , KEY'   ) ) => doneLemma ( 728 ) ... </k> requires KEY =/=Int KEY' andBool KEY =/=Int KEY'' andBool KEY =/=Int KEY''' andBool KEY' =/=Int KEY'' andBool KEY' =/=Int KEY''' andBool KEY'' =/=Int KEY'''
    claim <k> runLemma ( #lookup( _M:Map [ KEY <- 33 ] [ KEY' <- 728 ] [ KEY'' <- (pow256 +Int 5) ] [ KEY''' <- "hello" ] , KEY''  ) ) => doneLemma ( 5   ) ... </k> requires KEY =/=Int KEY' andBool KEY =/=Int KEY'' andBool KEY =/=Int KEY''' andBool KEY' =/=Int KEY'' andBool KEY' =/=Int KEY''' andBool KEY'' =/=Int KEY'''
    claim <k> runLemma ( #lookup( _M:Map [ KEY <- 33 ] [ KEY' <- 728 ] [ KEY'' <- (pow256 +Int 5) ] [ KEY''' <- "hello" ] , KEY''' ) ) => doneLemma ( 0   ) ... </k> requires KEY =/=Int KEY' andBool KEY =/=Int KEY'' andBool KEY =/=Int KEY''' andBool KEY' =/=Int KEY'' andBool KEY' =/=Int KEY''' andBool KEY'' =/=Int KEY'''

 // #range selection operation
 // --------------------------

    // Non-positive range
    claim <k> runLemma ( #range(_M, _N,  0) ) => doneLemma ( .Bytes ) ... </k>
    claim <k> runLemma ( #range(_M, _N, -3) ) => doneLemma ( .Bytes ) ... </k>

    // Range outside of previous buffer write
    claim <k> runLemma ( #range(#writeRange(M, 32, _BUF:Bytes ), 20, 4) ) => doneLemma ( #range(M, 20, 4) ) ... </k>
    claim <k> runLemma ( #range(#writeRange(M, 32,  BUF:Bytes ), 48, 4) ) => doneLemma ( #range(M, 48, 4) ) ... </k> requires lengthBytes(BUF) <=Int 12
    claim <k> runLemma ( #range(#writeRange(M, 32, _BUF:Bytes ), 31, 1) ) => doneLemma ( #range(M, 31, 1) ) ... </k>
    claim <k> runLemma ( #range(#writeRange(M, 32,  #buf(1, _BUF) ), 33, 1) ) => doneLemma ( #range(M, 33, 1) ) ... </k>

    // Range starting before buf#writeRange(f, wr,
    claim <k> runLemma ( #range(#writeRange(M, 32, BUF:Bytes )            , 30 , 8) ) => doneLemma ( #range(M, 30, 2) +Bytes (#range(BUF, 0, 6))                          ) ... </k> requires lengthBytes(BUF) >=Int 6
    claim <k> runLemma ( #range(#writeRange(M, 32, (0 : 1 : 2 : .Bytes) ) , 30 , 8) ) => doneLemma ( #range(M, 30, 2) +Bytes (0 : 1 : 2 : .Bytes) +Bytes #range(M, 35, 3) ) ... </k>
    claim <k> runLemma ( #range(#writeRange(M, 32, #buf(2, BUF) )         , 31 , 2) ) => doneLemma ( #range(M, 31, 1) +Bytes (#range(#buf(2, BUF), 0, 1) )                ) ... </k>
    claim <k> runLemma ( #range(#writeRange(M, 32, #buf(1, BUF) )         , 31 , 2) ) => doneLemma ( #range(M, 31, 1) +Bytes #buf(1, BUF)                                 ) ... </k>
    claim <k> runLemma ( #range(#writeRange(M, 32, #buf(1, BUF) )         , 31 , 3) ) => doneLemma ( #range(M, 31, 1) +Bytes #buf(1, BUF) +Bytes #range(M, 33, 1)         ) ... </k>

    // Range starting at same point as buffer write
    claim <k> runLemma ( #range(#writeRange(_M, 32, BUF:Bytes )            , 32 , 7) ) => doneLemma( #range( BUF, 0, 7 )                          ) ... </k> requires lengthBytes(BUF) >=Int 7
    claim <k> runLemma ( #range(#writeRange( M, 32, (0 : 1 : 2 : .Bytes) ) , 32 , 7) ) => doneLemma( (0 : 1 : 2 : .Bytes) +Bytes #range(M, 35, 4) ) ... </k>
    claim <k> runLemma ( #range(#writeRange(_M, 32, #buf(2, BUF) )         , 32 , 1) ) => doneLemma( #range(#buf(2, BUF), 0, 1 )                  ) ... </k>
    claim <k> runLemma ( #range(#writeRange(_M, 32, #buf(1, BUF) )         , 32 , 1) ) => doneLemma( #buf(1, BUF)                                 ) ... </k>
    claim <k> runLemma ( #range(#writeRange( M, 32, #buf(1, BUF) )         , 32 , 2) ) => doneLemma( #buf(1, BUF) +Bytes #range(M, 33, 1)         ) ... </k>

    // Range starting in the middle of the buffer write
    claim <k> runLemma ( #range(#writeRange(_M, 32, (0 : 1 : 2 : 3 : 4 : .Bytes) ) , 35 , 2) ) => doneLemma( (3 : 4 : .Bytes)                          ) ... </k>
    claim <k> runLemma ( #range(#writeRange( M, 32, (0 : 1 : 2 : 3 : 4 : .Bytes) ) , 35 , 8) ) => doneLemma( (3 : 4 : .Bytes) +Bytes #range(M, 37, 6)  ) ... </k>
    claim <k> runLemma ( #range(#writeRange(_M, 32, (0 : 1 : 2 : .Bytes)         ) , 33 , 1) ) => doneLemma( (1 : .Bytes)                              ) ... </k>
    claim <k> runLemma ( #range(#writeRange(_M, 32, (0 : 1 : 2 : .Bytes)         ) , 33 , 2) ) => doneLemma( (1 : 2 : .Bytes)                          ) ... </k>
    claim <k> runLemma ( #range(#writeRange( M, 32, (0 : 1 : 2 : .Bytes)         ) , 33 , 3) ) => doneLemma( (1 : 2 :  .Bytes) +Bytes #range(M, 35, 1) ) ... </k>

    claim [nestedRange]: <k> runLemma ( #range ( #range ( BA:Bytes , 4 , 64 ) , 32 , 32 ) ) => doneLemma ( #range ( BA , 36 , 32 ) ) ... </k>

 // #buf simplification
 // -------------------
    claim [bufExtractPadding]: <k> runLemma ( #asWord ( ( #range( #buf ( 32 , X ), 0, 28 ) ):Bytes ) ) => doneLemma ( 0 ) ... </k> requires #rangeUInt(32, X)

    claim <k> runLemma ( #buf( 32 , bool2Word ( B:Bool ) ) ==K #buf( 32 , 1 )     ) => doneLemma( B ==K true ) ... </k>
    claim <k> runLemma ( #buf( 32 , I:Int )                ==K #buf( 32 , 1 )     ) => doneLemma( I ==K 1    ) ... </k>
    claim <k> runLemma ( #buf( 32 , 1 )                    ==K #buf( 32 , I:Int ) ) => doneLemma( I ==K 1    ) ... </k>

    claim <k> runLemma ( #bufStrict( #ceil32(LEN) -Int LEN, 0 ) ) => doneLemma( #buf( #ceil32(LEN) -Int LEN, 0 ) ) ... </k> requires 0 <=Int LEN

    claim <k> runLemma( #padToWidth(32, #asByteStack(#hashedLocation("Solidity", 2, OWNER         .IntList))) ) => doneLemma(#buf(32, #hashedLocation("Solidity", 2, OWNER         .IntList))) ... </k> requires #rangeUInt(256, OWNER)
    claim <k> runLemma( #padToWidth(32, #asByteStack(#hashedLocation("Solidity", 2, OWNER SPENDER .IntList))) ) => doneLemma(#buf(32, #hashedLocation("Solidity", 2, OWNER SPENDER .IntList))) ... </k> requires #rangeUInt(256, OWNER) andBool #rangeUInt(256, SPENDER)

 // chop simplification
 // -------------------

    claim <k> runLemma ( chop( #lookup(M, KEY)   ) ) => doneLemma( #lookup(M, KEY) ) ... </k>
    claim <k> runLemma ( chop( bool2Word(B:Bool) ) ) => doneLemma( bool2Word(B)    ) ... </k>

    claim [chop-range-inferred]: <k> runLemma(X <Int chop(X *Int Y) /Int 1000000000000000000) => doneLemma(X <Int (X *Int Y) /Int 1000000000000000000) ... </k>
      requires #rangeUInt(256, X) andBool #rangeUInt(256, Y) andBool Y <=Int maxUInt256 /Int X

 // #padToWidth simplification
 // --------------------------

    claim <k> runLemma ( #padToWidth( 32 , #asByteStack( bool2Word ( B:Bool ) ) ) ) => doneLemma( #buf( 32 , bool2Word ( B ) ) ) ... </k>
    claim <k> runLemma ( #padToWidth( 32 , #asByteStack( maxUInt160 &Int #newAddr(ACCT, 1) ) ) )
           => doneLemma( #buf(32, #newAddr(ACCT, 1)) ) ... </k>

    //Required for ERC20 + solc5 + constructor call
    claim <k> runLemma ( 160 ==Int #asWord ( #buf( 4, 160 ) +Bytes ( #range( #buf( 32 , _BUF ), 0, 28 ) ) ) >>Int 224 )
           => doneLemma( true ) ... </k>

 // buffer range sinplification
 // ---------------------------
    claim <k> runLemma  ( #range((#buf(DATA_LEN, DATA) +Bytes _BUF), 0, DATA_LEN) )
           => doneLemma ( #range( #buf(DATA_LEN, DATA)             , 0, DATA_LEN) ) ... </k>
      requires #range(0 <= DATA < (2 ^Int (DATA_LEN *Int 8)))
       andBool 0 <=Int DATA_LEN

 // concatenation simplification
 // ----------------------------

    claim [bytes-reassociation]: <k> runLemma  ( ((((A +Bytes B) +Bytes C) +Bytes D) +Bytes E) +Bytes F )
                                  => doneLemma ( A +Bytes (B +Bytes (C +Bytes (D +Bytes (E +Bytes F)))) ) ... </k>

 // bitwise-and identity
 // --------------------

    claim <k> runLemma ( N &Int maxUInt256 ) => doneLemma ( N ) ... </k> requires #rangeUInt(256, N)
    claim <k> runLemma ( maxUInt256 &Int N ) => doneLemma ( N ) ... </k> requires #rangeUInt(256, N)
    claim <k> runLemma ( N &Int maxUInt248 ) => doneLemma ( N ) ... </k> requires #rangeUInt(248, N)
    claim <k> runLemma ( maxUInt248 &Int N ) => doneLemma ( N ) ... </k> requires #rangeUInt(248, N)
    claim <k> runLemma ( N &Int maxUInt240 ) => doneLemma ( N ) ... </k> requires #rangeUInt(240, N)
    claim <k> runLemma ( maxUInt240 &Int N ) => doneLemma ( N ) ... </k> requires #rangeUInt(240, N)
    claim <k> runLemma ( N &Int maxUInt232 ) => doneLemma ( N ) ... </k> requires #rangeUInt(232, N)
    claim <k> runLemma ( maxUInt232 &Int N ) => doneLemma ( N ) ... </k> requires #rangeUInt(232, N)
    claim <k> runLemma ( N &Int maxUInt224 ) => doneLemma ( N ) ... </k> requires #rangeUInt(224, N)
    claim <k> runLemma ( maxUInt224 &Int N ) => doneLemma ( N ) ... </k> requires #rangeUInt(224, N)
    claim <k> runLemma ( N &Int maxUInt216 ) => doneLemma ( N ) ... </k> requires #rangeUInt(216, N)
    claim <k> runLemma ( maxUInt216 &Int N ) => doneLemma ( N ) ... </k> requires #rangeUInt(216, N)
    claim <k> runLemma ( N &Int maxUInt208 ) => doneLemma ( N ) ... </k> requires #rangeUInt(208, N)
    claim <k> runLemma ( maxUInt208 &Int N ) => doneLemma ( N ) ... </k> requires #rangeUInt(208, N)
    claim <k> runLemma ( N &Int maxUInt200 ) => doneLemma ( N ) ... </k> requires #rangeUInt(200, N)
    claim <k> runLemma ( maxUInt200 &Int N ) => doneLemma ( N ) ... </k> requires #rangeUInt(200, N)
    claim <k> runLemma ( N &Int maxUInt192 ) => doneLemma ( N ) ... </k> requires #rangeUInt(192, N)
    claim <k> runLemma ( maxUInt192 &Int N ) => doneLemma ( N ) ... </k> requires #rangeUInt(192, N)
    claim <k> runLemma ( N &Int maxUInt184 ) => doneLemma ( N ) ... </k> requires #rangeUInt(184, N)
    claim <k> runLemma ( maxUInt184 &Int N ) => doneLemma ( N ) ... </k> requires #rangeUInt(184, N)
    claim <k> runLemma ( N &Int maxUInt176 ) => doneLemma ( N ) ... </k> requires #rangeUInt(176, N)
    claim <k> runLemma ( maxUInt176 &Int N ) => doneLemma ( N ) ... </k> requires #rangeUInt(176, N)
    claim <k> runLemma ( N &Int maxUInt168 ) => doneLemma ( N ) ... </k> requires #rangeUInt(168, N)
    claim <k> runLemma ( maxUInt168 &Int N ) => doneLemma ( N ) ... </k> requires #rangeUInt(168, N)
    claim <k> runLemma ( N &Int maxUInt160 ) => doneLemma ( N ) ... </k> requires #rangeUInt(160, N)
    claim <k> runLemma ( maxUInt160 &Int N ) => doneLemma ( N ) ... </k> requires #rangeUInt(160, N)
    claim <k> runLemma ( N &Int maxUInt152 ) => doneLemma ( N ) ... </k> requires #rangeUInt(152, N)
    claim <k> runLemma ( maxUInt152 &Int N ) => doneLemma ( N ) ... </k> requires #rangeUInt(152, N)
    claim <k> runLemma ( N &Int maxUInt144 ) => doneLemma ( N ) ... </k> requires #rangeUInt(144, N)
    claim <k> runLemma ( maxUInt144 &Int N ) => doneLemma ( N ) ... </k> requires #rangeUInt(144, N)
    claim <k> runLemma ( N &Int maxUInt136 ) => doneLemma ( N ) ... </k> requires #rangeUInt(136, N)
    claim <k> runLemma ( maxUInt136 &Int N ) => doneLemma ( N ) ... </k> requires #rangeUInt(136, N)
    claim <k> runLemma ( N &Int maxUInt128 ) => doneLemma ( N ) ... </k> requires #rangeUInt(128, N)
    claim <k> runLemma ( maxUInt128 &Int N ) => doneLemma ( N ) ... </k> requires #rangeUInt(128, N)
    claim <k> runLemma ( N &Int maxUInt120 ) => doneLemma ( N ) ... </k> requires #rangeUInt(120, N)
    claim <k> runLemma ( maxUInt120 &Int N ) => doneLemma ( N ) ... </k> requires #rangeUInt(120, N)
    claim <k> runLemma ( N &Int maxUInt112 ) => doneLemma ( N ) ... </k> requires #rangeUInt(112, N)
    claim <k> runLemma ( maxUInt112 &Int N ) => doneLemma ( N ) ... </k> requires #rangeUInt(112, N)
    claim <k> runLemma ( N &Int maxUInt104 ) => doneLemma ( N ) ... </k> requires #rangeUInt(104, N)
    claim <k> runLemma ( maxUInt104 &Int N ) => doneLemma ( N ) ... </k> requires #rangeUInt(104, N)
    claim <k> runLemma ( N &Int maxUInt96  ) => doneLemma ( N ) ... </k> requires #rangeUInt(96,  N)
    claim <k> runLemma ( maxUInt96 &Int N  ) => doneLemma ( N ) ... </k> requires #rangeUInt(96,  N)
    claim <k> runLemma ( N &Int maxUInt88  ) => doneLemma ( N ) ... </k> requires #rangeUInt(88,  N)
    claim <k> runLemma ( maxUInt88 &Int N  ) => doneLemma ( N ) ... </k> requires #rangeUInt(88,  N)
    claim <k> runLemma ( N &Int maxUInt80  ) => doneLemma ( N ) ... </k> requires #rangeUInt(80,  N)
    claim <k> runLemma ( maxUInt80 &Int N  ) => doneLemma ( N ) ... </k> requires #rangeUInt(80,  N)
    claim <k> runLemma ( N &Int maxUInt72  ) => doneLemma ( N ) ... </k> requires #rangeUInt(72,  N)
    claim <k> runLemma ( maxUInt72 &Int N  ) => doneLemma ( N ) ... </k> requires #rangeUInt(72,  N)
    claim <k> runLemma ( N &Int maxUInt64  ) => doneLemma ( N ) ... </k> requires #rangeUInt(64,  N)
    claim <k> runLemma ( maxUInt64 &Int N  ) => doneLemma ( N ) ... </k> requires #rangeUInt(64,  N)
    claim <k> runLemma ( N &Int maxUInt56  ) => doneLemma ( N ) ... </k> requires #rangeUInt(56,  N)
    claim <k> runLemma ( maxUInt56 &Int N  ) => doneLemma ( N ) ... </k> requires #rangeUInt(56,  N)
    claim <k> runLemma ( N &Int maxUInt48  ) => doneLemma ( N ) ... </k> requires #rangeUInt(48,  N)
    claim <k> runLemma ( maxUInt48 &Int N  ) => doneLemma ( N ) ... </k> requires #rangeUInt(48,  N)
    claim <k> runLemma ( N &Int maxUInt40  ) => doneLemma ( N ) ... </k> requires #rangeUInt(40,  N)
    claim <k> runLemma ( maxUInt40 &Int N  ) => doneLemma ( N ) ... </k> requires #rangeUInt(40,  N)
    claim <k> runLemma ( N &Int maxUInt32  ) => doneLemma ( N ) ... </k> requires #rangeUInt(32,  N)
    claim <k> runLemma ( maxUInt32 &Int N  ) => doneLemma ( N ) ... </k> requires #rangeUInt(32,  N)
    claim <k> runLemma ( N &Int maxUInt24  ) => doneLemma ( N ) ... </k> requires #rangeUInt(24,  N)
    claim <k> runLemma ( maxUInt24 &Int N  ) => doneLemma ( N ) ... </k> requires #rangeUInt(24,  N)
    claim <k> runLemma ( N &Int maxUInt16  ) => doneLemma ( N ) ... </k> requires #rangeUInt(16,  N)
    claim <k> runLemma ( maxUInt16 &Int N  ) => doneLemma ( N ) ... </k> requires #rangeUInt(16,  N)
    claim <k> runLemma ( N &Int maxUInt8   ) => doneLemma ( N ) ... </k> requires #rangeUInt(8,   N)
    claim <k> runLemma ( maxUInt8 &Int N   ) => doneLemma ( N ) ... </k> requires #rangeUInt(8,   N)

 // ecrecover
 // ---------
    claim [ecrec-length]: <k> runLemma  ( lengthBytes ( #ecrec ( _ , _ , _ , _ ) ) <=Int 32 )
                           => doneLemma ( true ) ... </k>

    claim [ecrec-split]: <k> runLemma  ( #range ( #buf(160, 0) +Bytes _BUF , lengthBytes ( #ecrec ( HASH , SIGV , SIGR , SIGS ) ) +Int 128 , 32 -Int lengthBytes ( #ecrec ( HASH , SIGV , SIGR , SIGS ) ) ) )
                          => doneLemma ( #range ( #buf( 32, 0)             , lengthBytes ( #ecrec ( HASH , SIGV , SIGR , SIGS ) )          , 32 -Int lengthBytes ( #ecrec ( HASH , SIGV , SIGR , SIGS ) ) ) ) ... </k>

    claim [ecrec-range]: <k> runLemma  ( #rangeUInt ( 160 , #asWord ( #ecrec ( _ , _ , _ , _ ) ) ) )
                          => doneLemma ( true ) ... </k>

    claim [ecrec-mask]: <k> runLemma  ( #asWord ( #ecrec ( HASH , SIGV , SIGR , SIGS ) ) &Int maxUInt160 )
                         => doneLemma ( #asWord ( #ecrec ( HASH , SIGV , SIGR , SIGS ) ) ) ... </k>

 // Address computation
 // -------------------

    claim [addr-from-private-key]: <k> runLemma  ( #addrFromPrivateKey(#unparseDataBytes(b"\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x01")) )
                                    => doneLemma ( 721457446580647751014191829380889690493307935711 ) ... </k>

endmodule
