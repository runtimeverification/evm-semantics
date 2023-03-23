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

    // claim <k> runLemma ( M:Map [ I1 <- 1 ] [ I2 <- 2 ] ) => doneLemma ( M [ I1 <- 1 ] [ I2 <- 2 ] ) ... </k> requires I1  <Int I2
    // claim <k> runLemma ( M:Map [ I1 <- 1 ] [ I2 <- 2 ] ) => doneLemma ( M [ I2 <- 2 ] [ I1 <- 1 ] ) ... </k> requires I1  >Int I2
    // claim <k> runLemma ( M:Map [ I1 <- 1 ] [ I2 <- 2 ] ) => doneLemma ( M [ I1 <- 2 ]             ) ... </k> requires I1 ==Int I2
    // claim <k> runLemma ( M:Map [ I1 <- 1 ] [ I2 <- 2 ] ) => doneLemma ( M [ I2 <- 2 ]             ) ... </k> requires I1 ==Int I2

    claim <k> runLemma( #writeRange( #writeRange( M:Bytes, 32, BA1 ), 32, BA2                                                                  )) => doneLemma(#writeRange(M:Bytes, 32, BA2                                                                  )) ... </k> requires lengthBytes(BA1) <=Int lengthBytes(BA2)
    claim <k> runLemma( #writeRange( #writeRange( M:Bytes, 32, BA1 ), 32, #padToWidth(32, #asByteStack(#hashedLocation("Solidity", 2, OWNER))) )) => doneLemma(#writeRange(M:Bytes, 32, #padToWidth(32, #asByteStack(#hashedLocation("Solidity", 2, OWNER))) )) ... </k> requires lengthBytes(BA1) ==Int 32 andBool #rangeUInt(256, OWNER)

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
    // claim <k> runLemma ( #lookup( _M:Map [ KEY <- 33 ] [ KEY' <- 728 ] [ KEY'' <- (pow256 +Int 5) ] [ KEY''' <- "hello" ] , KEY''  ) ) => doneLemma ( 5   ) ... </k> requires KEY =/=Int KEY' andBool KEY =/=Int KEY'' andBool KEY =/=Int KEY''' andBool KEY' =/=Int KEY'' andBool KEY' =/=Int KEY''' andBool KEY'' =/=Int KEY'''
    // claim <k> runLemma ( #lookup( _M:Map [ KEY <- 33 ] [ KEY' <- 728 ] [ KEY'' <- (pow256 +Int 5) ] [ KEY''' <- "hello" ] , KEY''' ) ) => doneLemma ( 0   ) ... </k> requires KEY =/=Int KEY' andBool KEY =/=Int KEY'' andBool KEY =/=Int KEY''' andBool KEY' =/=Int KEY'' andBool KEY' =/=Int KEY''' andBool KEY'' =/=Int KEY'''

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

 // head-tail simplification
 // ------------------------

    // [concatHead-base]
    // [concatHead-ind]
    claim [ht-1]: <k> runLemma ( concatHead((A +Bytes _) +Bytes _) ) => doneLemma(A)      ... </k>

    // [concatHead-base]
    // [concatHead-ind]
    claim [ht-2]: <k> runLemma ( concatTail((_ +Bytes B) +Bytes C) ) => doneLemma(B +Bytes C) ... </k>

    // [concatHead-base]
    // [concatHead-ind]
    claim [ht-3]:
      <k> runLemma (
            concatHead(( ( ( b"\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x80\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\xe9\xe0\\B\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00" +Bytes #buf ( 32 , _VV1__value_3c5818c8:Int ) ) +Bytes #buf ( 32 , _VV2__gasLimit_3c5818c8:Int ) +Bytes b"\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x01\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\xa0" ) +Bytes #buf ( 32 , lengthBytes ( VV6__data_3c5818c8:Bytes ) ) ) +Bytes VV6__data_3c5818c8:Bytes +Bytes b"\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00")
          ) =>
          doneLemma(
            b"\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x80\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\xe9\xe0\\B\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00"
          ) ...
      </k>

    // [concatTail-base]
    // [concatTail-ind]
    claim [ht-4]:
      <k> runLemma (
            concatTail(( ( ( b"\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x80\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\xe9\xe0\\B\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00" +Bytes #buf ( 32 , VV1__value_3c5818c8:Int ) ) +Bytes #buf ( 32 , VV2__gasLimit_3c5818c8:Int ) +Bytes b"\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x01\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\xa0" ) +Bytes #buf ( 32 , lengthBytes ( VV6__data_3c5818c8:Bytes ) ) ) +Bytes VV6__data_3c5818c8:Bytes +Bytes b"\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00")
          ) =>
          doneLemma(
            ( ( #buf ( 32 , VV1__value_3c5818c8 ) +Bytes #buf ( 32 , VV2__gasLimit_3c5818c8 ) +Bytes b"\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x01\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\xa0" ) +Bytes #buf ( 32 , lengthBytes ( VV6__data_3c5818c8 ) ) ) +Bytes VV6__data_3c5818c8 +Bytes b"\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00"
          ) ...
      </k>

    // [concatHead-base]
    // [concatHead-ind]
    claim [ht-5]:
      <k> runLemma (
            lengthBytes ( concatHead ( ( b"\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x80\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00E\xb5`x" +Bytes #buf ( 32 , VV5__txOrigin_3c5818c8 ) ) +Bytes #buf ( 32 , VV5__txOrigin_3c5818c8 ) ) )
          ) =>
          doneLemma(
            100
          ) ...
      </k>

    // [concatHead-base]
    // [concatHead-ind]
    // [lengthBytes-range]
    // [maxint-leq-split]
    claim [ht-7]:
      <k> runLemma (
            concatHead( #range ( ( ( #buf ( 32 , lengthBytes ( VV6__data_3c5818c8 ) +Int 73 ) +Bytes b"\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00" ) +Bytes #buf ( 32 , VV1__value_3c5818c8 ) +Bytes ( #buf ( 8 , VV2__gasLimit_3c5818c8 ) +Bytes b"\x01" ) +Bytes ( VV6__data_3c5818c8 +Bytes b"\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00" ) +Bytes ( #range ( b"\x01\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00" , lengthBytes ( VV6__data_3c5818c8 ) +Int 33 , 31 -Int lengthBytes ( VV6__data_3c5818c8 ) -Int lengthBytes ( #range ( b"\x01\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00" , lengthBytes ( VV6__data_3c5818c8 ) +Int 1 , 31 -Int lengthBytes ( VV6__data_3c5818c8 ) ) ) +Int 32 ) ) ) , 0 , lengthBytes ( #range ( b"\x01\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00" , lengthBytes ( VV6__data_3c5818c8 ) +Int 33 , 31 -Int lengthBytes ( VV6__data_3c5818c8 ) -Int lengthBytes ( #range ( b"\x01\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00" , lengthBytes ( VV6__data_3c5818c8 ) +Int 1 , 31 -Int lengthBytes ( VV6__data_3c5818c8 ) ) ) +Int 32 ) ) ) +Bytes b"\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00 " )
          ) =>
          doneLemma (
            #range ( #buf ( 32 , lengthBytes ( VV6__data_3c5818c8 ) +Int 73 ) , 0 , maxInt ( 0 , 31 -Int lengthBytes ( VV6__data_3c5818c8 ) -Int maxInt ( 0 , 31 -Int lengthBytes ( VV6__data_3c5818c8 ) ) +Int 32 ) )
          ) ...
      </k>
      requires 0 <=Int VV1__value_3c5818c8
       andBool VV1__value_3c5818c8:Int <Int pow256
       andBool 0 <=Int VV2__gasLimit_3c5818c8
       andBool VV2__gasLimit_3c5818c8 <Int pow64

    // [concatHead-base]
    // [lengthBytes-range]
    claim [index-1]:
      <k> runLemma(
            #range ( #range ( b"\x01\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00" , lengthBytes ( VV6__data_3c5818c8:Bytes ) +Int 1 , 31 -Int lengthBytes ( VV6__data_3c5818c8:Bytes ) ) , 32 , lengthBytes ( #range ( b"\x01\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00" , lengthBytes ( VV6__data_3c5818c8:Bytes ) +Int 1 , 31 -Int lengthBytes ( VV6__data_3c5818c8:Bytes ) ) ) +Int -32 )
          )
          => doneLemma(
            .Bytes
          ) ...
      </k>

    // [concatHead-base]
    // [concatHead-ind]
    // [concatTail-base]
    // [concatTail-ind]
    // [range-includes-concathead]
    // [range-outside-concatHead]
    claim [range-2]:
      <k> runLemma(
            #range ( #range ( ( b"\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x80\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00E\xb5`x" +Bytes #buf ( 32 , VV5__txOrigin_3c5818c8:Int ) ) +Bytes #buf ( 32 , VV5__txOrigin_3c5818c8:Int ) , 100 , 64 ) , 0 , 32 )
          )
          => doneLemma( #buf ( 32 , VV5__txOrigin_3c5818c8:Int )  ) ...
      </k>

    // [concatHead-base]
    // [concatHead-ind]
    // [concatTail-base]
    // [concatTail-ind]
    // [range-includes-concathead]
    // [range-outside-concatHead]
    claim [range-5]:
      <k> runLemma (
            #range ( ( b"\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x80\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00E\xb5`x" +Bytes #buf ( 32 , VV5__txOrigin_3c5818c8 ) ) +Bytes #buf ( 32 , VV5__txOrigin_3c5818c8 ) , 100 , 64 )
          ) =>
          doneLemma(
            #buf ( 32 , VV5__txOrigin_3c5818c8 ) +Bytes #buf ( 32 , VV5__txOrigin_3c5818c8 )
          ) ...
      </k>

    // [concatHead-base]
    claim [range-9]:
      <k> runLemma(
            b"\x01\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00" [ lengthBytes ( VV6__data_3c5818c8:Bytes ) +Int 1 .. 31 -Int lengthBytes ( VV6__data_3c5818c8:Bytes ) ]
          )
          => doneLemma(
            .Bytes
          ) ...
      </k>
      requires 119 <Int lengthBytes(VV6__data_3c5818c8)

    // [concatHead-base]
    claim [range-10]:
      <k> runLemma(
            b"\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00" [ 151 -Int lengthBytes ( VV6__data_3c5818c8:Bytes ) .. lengthBytes ( VV6__data_3c5818c8:Bytes ) +Int lengthBytes ( b"\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00" [ 119 -Int lengthBytes ( VV6__data_3c5818c8:Bytes ) .. lengthBytes ( VV6__data_3c5818c8:Bytes ) +Int lengthBytes ( b"\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00" [ 87 -Int lengthBytes ( VV6__data_3c5818c8:Bytes ) .. lengthBytes ( VV6__data_3c5818c8:Bytes ) +Int -55 ] ) +Int -87 ] ) +Int -119 ]
          )
          => doneLemma(
            b"\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00" [ 151 -Int lengthBytes ( VV6__data_3c5818c8 ) .. lengthBytes ( VV6__data_3c5818c8 ) +Int -119 ]
          ) ...
      </k>
      requires 0 <=Int VV1__value_3c5818c8
       andBool VV1__value_3c5818c8:Int <Int pow256
       andBool 0 <=Int VV2__gasLimit_3c5818c8
       andBool VV2__gasLimit_3c5818c8 <Int pow64
       andBool 119 <Int lengthBytes(VV6__data_3c5818c8)

    // [concatHead-base]
    // [concatHead-ind]
    // [concatTail-base]
    // [concatTail-ind]
    // [range-includes-concathead]
    // [range-inside-concatHead]
    // [range-outside-concatHead]
    claim [range-19]:
      <k> runLemma(
            #range ( #range ( ( ( b"\xc8\x8a^m\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x01H" +Bytes #buf ( 32 , VV0_value_3c5818c8 ) ) ) , 4 , 64 ) , 32 , 32 )
          )
          => doneLemma(
            #buf ( 32 , VV0_value_3c5818c8 )
          ) ...
      </k>

    // [concatHead-base]
    // [concatHead-ind]
    // [concatTail-base]
    // [concatTail-ind]
    // [range-non-pos-empty]
    // [range-outside-concatHead]
    // [writeRange-as-concat]
    claim [range-20]:
      <k> runLemma( #asWord ( ( #buf ( 32 , VV0_controller_3c5818c8 ) [ 28 .. 4 ] +Bytes ( #buf ( 32 , VV0_controller_3c5818c8 ) [ 0 .. 28 ] ) ) [ 0 := b"\x00\x00\x00\x00" ] ))
       => doneLemma( #asWord ( b"\x00\x00\x00\x00" +Bytes ( #buf ( 32 , VV0_controller_3c5818c8 ) [ 0 .. 28 ] ) ) ) ...
       </k>
       requires 0 <Int VV0_controller_3c5818c8 andBool VV0_controller_3c5818c8 <Int pow160

endmodule
