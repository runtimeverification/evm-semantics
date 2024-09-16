requires "edsl.md"
requires "lemmas/lemmas.k"

module VERIFICATION
    imports EDSL
    imports LEMMAS

    syntax StepSort ::= Map | Bytes | Int | Bool
 // --------------------------------------------

    syntax KItem ::= runLemma ( StepSort ) [symbol(runLemma)]
                   | doneLemma( StepSort )
 // --------------------------------------
    rule runLemma( T ) => doneLemma( T )

endmodule

module LEMMAS-SPEC
    imports VERIFICATION

 // sizeBytes
 // -------------

    claim <k> runLemma(lengthBytes(#padToWidth(32, #asByteStack(#hashedLocation("Solidity", 2, OWNER .IntList))))) => doneLemma(32) ... </k> requires #rangeUInt(256, OWNER)

    claim <k> runLemma(lengthBytes(#buf(X, 0) +Bytes #padRightToWidth(Y:Int, B:Bytes))) => doneLemma( X +Int Y ) ... </k>
      requires lengthBytes(B) <Int X andBool lengthBytes(B) <Int Y

 // Addresses
 // ---------

    // claim [newaddr.compare]: <k> runLemma(#isPrecompiledAccount(#newAddr(TESTER_ACCT, 1), ISTANBUL)) => doneLemma(false) ... </k> requires #rangeAddress(TESTER_ACCT)

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

    claim [cancellation-01]:
      <k> runLemma (
            ( ( ( ( ( X +Int X ) -Int Y ) -Int ( X -Int Y ) ) -Int Y ) -Int ( X -Int Y ) )
          ) => doneLemma (
            0
          ) ... </k>

    claim [cancellation-02]:
      <k> runLemma (
            ( ( A +Int ( ( B -Int A ) +Int B ) ) -Int ( B +Int B ) )
          ) => doneLemma (
            0
          ) ... </k>

    claim [buf-shift]:
      <k> runLemma (
            #buf ( 20, X <<Int 16 )
          ) => doneLemma (
            #buf ( 18 , X:Int ) +Bytes b"\x00\x00"
          ) ... </k>
          requires 0 <=Int X andBool X <Int 2 ^Int 144


 // Comparisons
 // -----------

    claim [comp-norm-01]:
      <k> runLemma (
            ( ( 20 -Int ( 10 +Int X:Int ) ) -Int 5 ) +Int 3 <=Int 7
          ) =>
          doneLemma (
            1 <=Int X
          ) ...
      </k>

    claim [comp-norm-02]:
      <k> runLemma (
            ( ( 20 -Int ( 10 +Int X:Int ) ) -Int 5 ) +Int 3 <Int 7
          ) =>
          doneLemma (
            1 <Int X
          ) ...
      </k>

    claim [comp-norm-03]:
      <k> runLemma (
            ( ( 20 -Int ( 10 +Int X:Int ) ) -Int 5 ) +Int 3 >Int 7
          ) =>
          doneLemma (
            1 >Int X
          ) ...
      </k>

    claim [comp-norm-04]:
      <k> runLemma (
            ( ( 20 -Int ( 10 +Int X:Int ) ) -Int 5 ) +Int 3 >=Int 7
          ) =>
          doneLemma (
            1 >=Int X
          ) ...
      </k>


 // Sets
 // ----

    claim [set-union-01]:
      <k> runLemma (
            notBool ( ( ((((S:Set |Set SetItem(X)) |Set SetItem (X)) |Set SetItem(Y)) |Set SetItem(X))
                          ==K
                          ((S:Set |Set SetItem(X)) |Set SetItem (Y))
                      ) ==Bool false
                    ) ==Bool true
          ) =>
          doneLemma (
            true
          ) ...
      </k>
      requires X =/=K Y


 // Buffer write simplifications
 // ----------------------------

    // claim <k> runLemma ( M [ L := .Bytes ] [ N := WS:Bytes ]                             ) => doneLemma ( M [ N := WS ]                        ) ... </k> requires L <=Int N
    // claim <k> runLemma ( M [ L := WS:Bytes ] [ N := .Bytes ]                             ) => doneLemma ( M [ L := WS ]                        ) ... </k> requires N <=Int L
    // claim <k> runLemma ( M [ 32 := (0 : 1 : 2 : .Bytes) ] [ 32 := (3 : 4 : 5 : .Bytes) ] ) => doneLemma ( M [ 32 := (3 : 4 : 5 : .Bytes) ] ) ... </k>

    claim <k> runLemma ( M:Map [ I1 <- 1 ] [ I2 <- 2 ] ) => doneLemma ( M [ I1 <- 1 ] [ I2 <- 2 ] ) ... </k> requires I1  <Int I2
    claim <k> runLemma ( M:Map [ I1 <- 1 ] [ I2 <- 2 ] ) => doneLemma ( M [ I2 <- 2 ] [ I1 <- 1 ] ) ... </k> requires I1  >Int I2
    claim <k> runLemma ( M:Map [ I1 <- 1 ] [ I2 <- 2 ] ) => doneLemma ( M [ I1 <- 2 ]             ) ... </k> requires I1 ==Int I2
    claim <k> runLemma ( M:Map [ I1 <- 1 ] [ I2 <- 2 ] ) => doneLemma ( M [ I2 <- 2 ]             ) ... </k> requires I1 ==Int I2

    claim <k> runLemma( M:Bytes [ 32 := BA1 ] [ 32 := BA2 ]                                                                  ) => doneLemma(M [ 32 := BA2 ]                                                                ) ... </k> requires lengthBytes(BA1) <=Int lengthBytes(BA2)
    claim <k> runLemma( M:Bytes [ 32 := BA1 ] [ 32 := #padToWidth(32, #asByteStack(#hashedLocation("Solidity", 2, OWNER))) ] ) => doneLemma(M [ 32 := #padToWidth(32, #asByteStack(#hashedLocation("Solidity", 2, OWNER))) ] ) ... </k> requires lengthBytes(BA1) ==Int 32 andBool #rangeUInt(256, OWNER)

    // Memory write past the end of the buffer
    claim [write-past-end]: <k> runLemma  ( #buf(160, A) [ 160 := #buf(32, B) ] [ 192 := #buf(32, C) ] [ 224 := #buf(32, D) ] [ 256 := #buf(32, E) ] )
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

    claim [lookup-key-neq]: <k> runLemma ( #lookup( ( (3 |-> 3) (5 |-> 5) (7 |-> 7) M:Map ) [ 9 <- 9 ] [ 11 <- 11 ] [ 13 <- 13 ], KEY ) ) => doneLemma ( #lookup (M, KEY) ) ... </k> requires 15 <=Int KEY

 // #range selection operation
 // --------------------------

    // Non-positive range
    claim [range-01]: <k> runLemma ( #range(_M, _N,  0) ) => doneLemma ( .Bytes ) ... </k>
    claim [range-02]: <k> runLemma ( #range(_M, _N, -3) ) => doneLemma ( .Bytes ) ... </k>

    // Range outside of previous buffer write
    claim [range-03]: <k> runLemma ( #range ( M [ 32 := _          ], 20, 4) ) => doneLemma ( #range(M, 20, 4) ) ... </k>
    claim [range-04]: <k> runLemma ( #range ( M [ 32 := BUF:Bytes  ], 48, 4) ) => doneLemma ( #range(M, 48, 4) ) ... </k> requires lengthBytes(BUF) <=Int 12
    claim [range-05]: <k> runLemma ( #range ( M [ 32 := _          ], 31, 1) ) => doneLemma ( #range(M, 31, 1) ) ... </k>
    claim [range-06]: <k> runLemma ( #range ( M [ 32 := #buf(1, _) ], 33, 1) ) => doneLemma ( #range(M, 33, 1) ) ... </k>

    // Range starting before buffer write
    claim [range-07]: <k> runLemma ( #range(M [ 32 := BUF:Bytes ]            , 30 , 8) ) => doneLemma ( #range(M, 30, 2) +Bytes (#range(BUF, 0, 6))                          ) ... </k> requires lengthBytes(BUF) >=Int 6
    claim [range-08]: <k> runLemma ( #range(M [ 32 := (0 : 1 : 2 : .Bytes) ] , 30 , 8) ) => doneLemma ( #range(M, 30, 2) +Bytes (0 : 1 : 2 : .Bytes) +Bytes #range(M, 35, 3) ) ... </k>
    claim [range-09]: <k> runLemma ( #range(M [ 32 := #buf(2, BUF) ]         , 31 , 2) ) => doneLemma ( #range(M, 31, 1) +Bytes (#range(#buf(2, BUF), 0, 1) )                ) ... </k>
    claim [range-10]: <k> runLemma ( #range(M [ 32 := #buf(1, BUF) ]         , 31 , 2) ) => doneLemma ( #range(M, 31, 1) +Bytes #buf(1, BUF)                                 ) ... </k>
    claim [range-11]: <k> runLemma ( #range(M [ 32 := #buf(1, BUF) ]         , 31 , 3) ) => doneLemma ( #range(M, 31, 1) +Bytes #buf(1, BUF) +Bytes #range(M, 33, 1)         ) ... </k>

    // Range starting at same point as buffer write
    claim [range-12]: <k> runLemma ( #range(_M [ 32 := BUF:Bytes ]            , 32 , 7) ) => doneLemma( #range( BUF, 0, 7 )                          ) ... </k> requires lengthBytes(BUF) >=Int 7
    claim [range-13]: <k> runLemma ( #range( M [ 32 := (0 : 1 : 2 : .Bytes) ] , 32 , 7) ) => doneLemma( (0 : 1 : 2 : .Bytes) +Bytes #range(M, 35, 4) ) ... </k>
    claim [range-14]: <k> runLemma ( #range(_M [ 32 := #buf(2, BUF) ]         , 32 , 1) ) => doneLemma( #range(#buf(2, BUF), 0, 1 )                  ) ... </k>
    claim [range-15]: <k> runLemma ( #range(_M [ 32 := #buf(1, BUF) ]         , 32 , 1) ) => doneLemma( #buf(1, BUF)                                 ) ... </k>
    claim [range-16]: <k> runLemma ( #range (M [ 32 := #buf(1, BUF) ]         , 32 , 2) ) => doneLemma( #buf(1, BUF) +Bytes #range(M, 33, 1)         ) ... </k>

    // Range starting in the middle of the buffer write
    claim [range-17]: <k> runLemma ( #range(_M [ 32 := (0 : 1 : 2 : 3 : 4 : .Bytes) ] , 35 , 2) ) => doneLemma( (3 : 4 : .Bytes)                          ) ... </k>
    claim [range-18]: <k> runLemma ( #range( M [ 32 := (0 : 1 : 2 : 3 : 4 : .Bytes) ] , 35 , 8) ) => doneLemma( (3 : 4 : .Bytes) +Bytes #range(M, 37, 6)  ) ... </k>
    claim [range-19]: <k> runLemma ( #range(_M [ 32 := (0 : 1 : 2 : .Bytes)         ] , 33 , 1) ) => doneLemma( (1 : .Bytes)                              ) ... </k>
    claim [range-20]: <k> runLemma ( #range(_M [ 32 := (0 : 1 : 2 : .Bytes)         ] , 33 , 2) ) => doneLemma( (1 : 2 : .Bytes)                          ) ... </k>
    claim [range-21]: <k> runLemma ( #range( M [ 32 := (0 : 1 : 2 : .Bytes)         ] , 33 , 3) ) => doneLemma( (1 : 2 :  .Bytes) +Bytes #range(M, 35, 1) ) ... </k>

    claim [range-22]: <k> runLemma ( #range ( #range ( BA:Bytes , 4 , 64 ) , 32 , 32 ) ) => doneLemma ( #range ( BA , 36 , 32 ) ) ... </k>

    claim [range-23]:
      <k> runLemma  ( #range((#buf(DATA_LEN, DATA) +Bytes _BUF), 0, DATA_LEN) ) =>
          doneLemma ( #range( #buf(DATA_LEN, DATA)             , 0, DATA_LEN) ) ... </k>
      requires #range(0 <= DATA < (2 ^Int (DATA_LEN *Int 8)))
       andBool 0 <=Int DATA_LEN

    claim [range-24]:
      <k> runLemma( #range ( #range ( b"\x01\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00" , lengthBytes ( VV6__data_3c5818c8:Bytes ) +Int 1 , 31 -Int lengthBytes ( VV6__data_3c5818c8:Bytes ) ) , 32 , lengthBytes ( #range ( b"\x01\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00" , lengthBytes ( VV6__data_3c5818c8:Bytes ) +Int 1 , 31 -Int lengthBytes ( VV6__data_3c5818c8:Bytes ) ) ) +Int -32 ) ) =>
          doneLemma( .Bytes ) ... </k>

    claim [range-25]:
      <k> runLemma( #range ( #range ( ( b"\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x80\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00E\xb5`x" +Bytes #buf ( 32 , VV5__txOrigin_3c5818c8:Int ) ) +Bytes #buf ( 32 , VV5__txOrigin_3c5818c8:Int ) , 100 , 64 ) , 0 , 32 ) ) =>
          doneLemma( #buf ( 32 , VV5__txOrigin_3c5818c8:Int )  ) ... </k>

    claim [range-26]:
      <k> runLemma ( #range ( ( b"\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x80\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00E\xb5`x" +Bytes #buf ( 32 , VV5__txOrigin_3c5818c8 ) ) +Bytes #buf ( 32 , VV5__txOrigin_3c5818c8 ) , 100 , 64 ) ) =>
          doneLemma( #buf ( 32 , VV5__txOrigin_3c5818c8 ) +Bytes #buf ( 32 , VV5__txOrigin_3c5818c8 ) ) ...
      </k>

    claim [range-27]:
      <k> runLemma( #range(b"\x01\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00", lengthBytes ( VV6__data_3c5818c8:Bytes ) +Int 1, 31 -Int lengthBytes ( VV6__data_3c5818c8:Bytes ) ) ) =>
          doneLemma( .Bytes ) ...
      </k>
      requires 119 <Int lengthBytes(VV6__data_3c5818c8)

    claim [range-28]:
      <k> runLemma( #range ( b"\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00", 151 -Int lengthBytes ( VV6__data_3c5818c8:Bytes ), lengthBytes ( VV6__data_3c5818c8:Bytes ) +Int lengthBytes ( #range ( b"\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00", 119 -Int lengthBytes ( VV6__data_3c5818c8:Bytes ), lengthBytes ( VV6__data_3c5818c8:Bytes ) +Int lengthBytes ( #range ( b"\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00", 87 -Int lengthBytes ( VV6__data_3c5818c8:Bytes ), lengthBytes ( VV6__data_3c5818c8:Bytes ) +Int -55 ) ) +Int -87 ) ) +Int -119 ) ) =>
          doneLemma( #range ( b"\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00", 151 -Int lengthBytes ( VV6__data_3c5818c8 ), lengthBytes ( VV6__data_3c5818c8 ) +Int -119 ) ) ... </k>
      requires 0 <=Int VV1__value_3c5818c8
       andBool VV1__value_3c5818c8:Int <Int pow256
       andBool 0 <=Int VV2__gasLimit_3c5818c8
       andBool VV2__gasLimit_3c5818c8 <Int pow64
       andBool 119 <Int lengthBytes(VV6__data_3c5818c8)

    claim [range-29]:
      <k> runLemma( #range ( #range ( ( ( b"\xc8\x8a^m\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x01H" +Bytes #buf ( 32 , VV0_value_3c5818c8 ) ) ) , 4 , 64 ) , 32 , 32 ) ) =>
          doneLemma( #buf ( 32 , VV0_value_3c5818c8 ) ) ... </k>

    claim [range-30]:
      <k> runLemma(
            #range ( b"\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x80\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00E\xb5`x\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00"
                       [ 132 := #buf ( 32 , _VV5__txOrigin_3c5818c8:Int ) ]
                       [ 128 := b"I\x1c\xc7\xc2\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00" ]
                       [ 128 := b"" ]
                       [ 132 := b"\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x01" ]
                       [ 128 := b"\xe9\xe0\\B\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00" ]
                       [ 164 := b"\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x01" ]
                       [ 160 := b"\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00" ]
                       [ 132 := b"\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00" ]
                       [ 164 := #buf ( 32 , _VV1__value_3c5818c8:Int ) ]
                       [ 196 := #buf ( 32 , _VV2__gasLimit_3c5818c8:Int ) ]
                       [ 228 := b"\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x01" ]
                       [ 260 := b"\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\xa0" ]
                       [ 292 := #buf ( 32 , lengthBytes ( VV6__data_3c5818c8:Bytes ) ) ]
                       [ 324 := VV6__data_3c5818c8:Bytes ] , 324 , minInt ( ( notMaxUInt5 &Int lengthBytes ( VV6__data_3c5818c8:Bytes ) +Int 31 ) +Int 196 , lengthBytes ( VV6__data_3c5818c8:Bytes ) +Int 196 ) +Int -196 )
          )
          => doneLemma( VV6__data_3c5818c8 ) ...
      </k>
      requires lengthBytes(VV6__data_3c5818c8:Bytes) <Int pow255

    claim [range-31]:
      <k> runLemma( #range(X, S1, 32) +Bytes #range( X [ S := Y ], S:Int, Z:Int ))
        => doneLemma( #range(X, S2 +Int 5, 32) +Bytes Y ) ...
      </k>
      requires lengthBytes(Y) +Int 20 ==Int Z +Int 20
       andBool S1 +Int 1 ==Int S2 +Int 6
       andBool 0 <Int lengthBytes(Y)
       andBool 0 <=Int S1 andBool 0 <=Int S

    claim [range-32]:
      <k> runLemma(
            #range ( #range ( #range ( ( ( ( b"\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x80\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\xe9\xe0\\B\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00" +Bytes _ ) +Bytes _ ) +Bytes _ ) +Bytes _ , 128 , ( notMaxUInt5 &Int lengthBytes ( X ) +Int 31 ) +Int 196 ), 0, 32 ), 0, 4 )
          )
          => doneLemma( b"\xe9\xe0\\B" ) ...
      </k>
      requires 0 <=Int VV1__value_3c5818c8
       andBool VV1__value_3c5818c8:Int <Int pow256
       andBool lengthBytes(X:Bytes) <Int pow255

    claim [range-33]:
      <k> runLemma(
            #asWord ( #range ( #range ( ( ( ( b"\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x80\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\xe9\xe0\\B\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00" +Bytes #buf ( 32 , VV1__value_3c5818c8:Int ) ) +Bytes #buf ( 32 , VV2__gasLimit_3c5818c8:Int ) +Bytes b"\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x01\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\xa0" ) +Bytes #buf ( 32 , lengthBytes ( VV6__data_3c5818c8:Bytes ) ) ) +Bytes VV6__data_3c5818c8:Bytes +Bytes b"\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00" , 128 , ( notMaxUInt5 &Int lengthBytes ( VV6__data_3c5818c8:Bytes ) +Int 31 ) +Int 196 ), 4, 32 ) )
              ==Int
            maxUInt160 &Int #asWord ( #range ( #range ( ( ( ( b"\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x80\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\xe9\xe0\\B\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00" +Bytes #buf ( 32 , VV1__value_3c5818c8:Int ) ) +Bytes #buf ( 32 , VV2__gasLimit_3c5818c8:Int ) +Bytes b"\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x01\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\xa0" ) +Bytes #buf ( 32 , lengthBytes ( VV6__data_3c5818c8:Bytes ) ) ) +Bytes VV6__data_3c5818c8:Bytes +Bytes b"\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00" , 128 , ( notMaxUInt5 &Int lengthBytes ( VV6__data_3c5818c8:Bytes ) +Int 31 ) +Int 196 ), 4, 32 ) )
          )
          => doneLemma( true ) ...
      </k>
      requires 0 <=Int VV1__value_3c5818c8
       andBool VV1__value_3c5818c8:Int <Int pow256
       andBool 0 <=Int VV2__gasLimit_3c5818c8
       andBool VV2__gasLimit_3c5818c8 <Int pow64
       andBool lengthBytes(VV6__data_3c5818c8:Bytes) <Int pow255

    claim [range-34]:
      <k> runLemma(
            #range ( ( ( ( b"\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x80\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\xe9\xe0\\B\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00" +Bytes #buf ( 32 , VV1__value_3c5818c8:Int ) ) +Bytes #buf ( 32 , VV2__gasLimit_3c5818c8:Int ) +Bytes b"\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x01\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\xa0" ) +Bytes #buf ( 32 , lengthBytes ( VV6__data_3c5818c8:Bytes ) ) ) +Bytes VV6__data_3c5818c8:Bytes +Bytes b"\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00" , 128 , ( notMaxUInt5 &Int lengthBytes ( VV6__data_3c5818c8:Bytes ) +Int 31 ) +Int 196 )
          )
          => doneLemma(
            b"\xe9\xe0\\B\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00" +Bytes #buf ( 32 , VV1__value_3c5818c8 ) +Bytes ( #buf ( 32 , VV2__gasLimit_3c5818c8 ) +Bytes b"\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x01\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\xa0" ) +Bytes #buf ( 32 , lengthBytes ( VV6__data_3c5818c8 ) ) +Bytes VV6__data_3c5818c8 +Bytes #range ( b"\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00" , 0 , ( notMaxUInt5 &Int lengthBytes ( VV6__data_3c5818c8 ) +Int 31 ) -Int lengthBytes ( VV6__data_3c5818c8 ) )
          ) ...
      </k>
      requires 0 <=Int VV1__value_3c5818c8
       andBool VV1__value_3c5818c8:Int <Int pow256
       andBool 0 <=Int VV2__gasLimit_3c5818c8
       andBool VV2__gasLimit_3c5818c8 <Int pow64
       andBool lengthBytes(VV6__data_3c5818c8:Bytes) <Int pow255

    claim [range-35]:
      <k> runLemma(
            #range ( #range ( ( ( ( b"\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x80\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00" +Bytes #buf ( 32 , _ ) ) +Bytes ( #range ( #buf ( 32 , _ ), 0, 8 ) ) +Bytes b"\x01" ) +Bytes ( #range ( #range ( ( ( ( b"\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x80\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\xe9\xe0\\B\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00" +Bytes #buf ( 32 , _ ) ) +Bytes #buf ( 32 , _ ) +Bytes b"\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x01\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\xa0" ) +Bytes #buf ( 32 , lengthBytes ( X ) ) ) +Bytes X +Bytes b"\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00" , 128 , ( notMaxUInt5 &Int lengthBytes ( X ) +Int 31 ) +Int 196 ), 196, lengthBytes ( X ) ) ) +Bytes ( #range ( b"\x01\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00", lengthBytes ( X ) +Int 1, 31 -Int lengthBytes ( X ) ) ) ), 0, lengthBytes ( X ) +Int 233 ) , 64 , 32 )
          )
          => doneLemma(
            b"\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x80"
          ) ...
      </k>
      requires lengthBytes(X:Bytes) <Int pow255

    claim [range-36]:
      <k> runLemma ( #range(B:Bytes, 5 +Int S2:Int, W:Int) ) => doneLemma ( #range(#range(B, 5, lengthBytes(B) -Int 5), S2, W) ) ... </k>
      requires 0 <=Int S2 andBool (5 +Int S2 <=Int lengthBytes(B))
       andBool B ==K #buf(512, 0)

    claim [range-37]:
      <k> runLemma( _B1:Bytes [ 1 := _B2:Bytes ] [ -1 := _B3:Bytes ]) => doneLemma(.Bytes) ... </k>

    claim [range-38]:
      <k> runLemma( #range (#buf(8, X:Int), -3, _:Int) ) => doneLemma( .Bytes ) ... </k>
      requires 0 <=Int X andBool X <Int pow64

 // #buf simplification
 // -------------------
    claim [bufExtractPadding]: <k> runLemma ( #asWord ( ( #range( #buf ( 32 , X ), 0, 28 ) ):Bytes ) ) => doneLemma ( 0 ) ... </k> requires #rangeUInt(32, X)

    claim <k> runLemma ( #buf( 32 , bool2Word ( B:Bool ) ) ==K #buf( 32 , 1 )     ) => doneLemma( B ==K true ) ... </k>
    claim <k> runLemma ( #buf( 32 , I:Int )                ==K #buf( 32 , 1 )     ) => doneLemma( I ==K 1    ) ... </k> requires #rangeUInt(256, I)
    claim <k> runLemma ( #buf( 32 , 1 )                    ==K #buf( 32 , I:Int ) ) => doneLemma( I ==K 1    ) ... </k> requires #rangeUInt(256, I)

    claim <k> runLemma ( #bufStrict( #ceil32(LEN) -Int LEN, 0 ) ) => doneLemma( #buf( #ceil32(LEN) -Int LEN, 0 ) ) ... </k> requires 0 <=Int LEN

    claim [bufstrict-simplify]:
          <k> runLemma ( #bufStrict(32, #getValue(#int256(X))) ) => doneLemma ( #buf(32, chop(X)) ) ... </k> requires #rangeSInt(256, X)

    claim <k> runLemma( #padToWidth(32, #asByteStack(#hashedLocation("Solidity", 2, OWNER         .IntList))) ) => doneLemma(#buf(32, #hashedLocation("Solidity", 2, OWNER         .IntList))) ... </k> requires #rangeUInt(256, OWNER)
    claim <k> runLemma( #padToWidth(32, #asByteStack(#hashedLocation("Solidity", 2, OWNER SPENDER .IntList))) ) => doneLemma(#buf(32, #hashedLocation("Solidity", 2, OWNER SPENDER .IntList))) ... </k> requires #rangeUInt(256, OWNER) andBool #rangeUInt(256, SPENDER)

    claim <k> runLemma( #buf(32, X +Int Y) +Bytes #buf(lengthBytes(B), 0) +Bytes #buf(32 +Int Y -Int Y, #asWord(B))) => doneLemma ( #buf(32, Z -Int Y) +Bytes #buf(32, ((3 *Int Y) -Int (2 *Int Y)) -Int Y) +Bytes B ) ... </k>
      requires lengthBytes(B) <=Int 4
       andBool 0 <=Int X andBool 0 <=Int Y andBool Y <=Int Z
       andBool X <Int 256 andBool Y <Int 256 andBool Z <Int 256
       andBool X +Int (2 *Int Y) -Int Z ==Int 0


 // chop simplification
 // -------------------

    claim <k> runLemma ( chop( #lookup(M, KEY)   ) ) => doneLemma( #lookup(M, KEY) ) ... </k>
    claim <k> runLemma ( chop( bool2Word(B:Bool) ) ) => doneLemma( bool2Word(B)    ) ... </k>

    claim [chop-chop]: <k> runLemma ( chop( chop ( X ) ) ) => doneLemma( chop ( X ) ) ... </k>

    claim [chop-range-inferred]: <k> runLemma(X <Int chop(X *Int Y) /Int 1000000000000000000) => doneLemma(X <Int (X *Int Y) /Int 1000000000000000000) ... </k>
      requires #rangeUInt(256, X) andBool #rangeUInt(256, Y) andBool Y <=Int maxUInt256 /Int X

    claim [chop-notMaxUInt5]:
      <k> runLemma (
            ( notBool ( notBool ( chop ( ( chop ( ( ( notMaxUInt5 &Int ( ( notMaxUInt5 &Int ( lengthBytes ( B:Bytes ) +Int maxUInt5 ) ) +Int 95 ) ) +Int 128 ) ) +Int ( notMaxUInt5 &Int ( ( notMaxUInt5 &Int ( lengthBytes ( B:Bytes ) +Int maxUInt5 ) ) +Int 63 ) ) ) ) <Int chop ( ( ( notMaxUInt5 &Int ( ( notMaxUInt5 &Int ( lengthBytes ( B:Bytes ) +Int maxUInt5 ) ) +Int 95 ) ) +Int 128 ) ) ) ) )
          ) => doneLemma (
            false
          ) ... </k>
      requires lengthBytes(B) <Int 2 ^Int 64

    claim [chop-additional-knowledge]: <k> runLemma (
                      X <=Int chop ( X +Int C ) andBool Y <=Int chop ( Y +Int C )
              andBool notBool ( ( X +Int C <Int pow256 ) andBool ( Y +Int C <Int pow256 ) )
          ) => doneLemma ( false ) ... </k>
    requires #rangeUInt(256, X) andBool #rangeUInt(256, Y) andBool #rangeUInt(256, C)

    claim [chop-sub-01]: <k> runLemma ( chop ( X -Int Y ) ) => doneLemma ( X -Int Y ) ... </k>
      requires #rangeUInt(256, X) andBool #rangeUInt(256, Y) andBool Y <=Int X

    claim [chop-mul-01]: <k> runLemma ( chop ( X *Int Y ) ) => doneLemma ( X *Int Y ) ... </k>
      requires 0 <=Int X andBool X <Int 2 ^Int 96
       andBool 0 <=Int Y andBool Y <Int 2 ^Int ( 256 -Int 96 )

    claim [chop-add-sub-conc]: <k> runLemma ( chop ( 0 -Int chop ( X +Int (-16)) ) ==Int 0 ) => doneLemma ( false ) ... </k>
      requires 0 <=Int X andBool X <Int 10

    claim [chop-overflow-01]: <k> runLemma ( X:Int <=Int chop ( X +Int Y:Int ) ) => doneLemma ( true ) ... </k>
      requires #rangeUInt(128, X) andBool #rangeUInt(128, Y)

    claim [chop-overflow-02]: <k> runLemma ( X:Int <=Int chop ( X *Int Y:Int ) /Int Y ) => doneLemma ( true ) ... </k>
      requires #rangeUInt(128, X) andBool #rangeUInt(128, Y)

    claim [chop-overflow-03]: <k> runLemma ( X:Int ==Int chop ( X *Int Y:Int ) /Int Y ) => doneLemma ( false ) ... </k>
      requires pow128 <=Int X andBool X <Int pow256 andBool pow256 <=Int Y

 // #padToWidth simplification
 // --------------------------

    claim <k> runLemma ( #padToWidth( 32 , #asByteStack( bool2Word ( B:Bool ) ) ) ) => doneLemma( #buf( 32 , bool2Word ( B ) ) ) ... </k>
    claim <k> runLemma ( #padToWidth( 32 , #asByteStack( maxUInt160 &Int #newAddr(ACCT, 1) ) ) )
           => doneLemma( #buf(32, #newAddr(ACCT, 1)) ) ... </k>

    //Required for ERC20 + solc5 + constructor call
    claim <k> runLemma ( 160 ==Int #asWord ( #buf( 4, 160 ) +Bytes ( #range( #buf( 32 , _BUF ), 0, 28 ) ) ) >>Int 224 )
           => doneLemma( true ) ... </k>

 // buffer range simplification
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

 // bitwise
 // -------

    claim [bit-n008-0]: <k> runLemma ( notMaxUInt8   &Int X ) => doneLemma( 0 ) ... </k> requires #rangeUInt (   8 , X )
    claim [bit-n016-0]: <k> runLemma ( notMaxUInt16  &Int X ) => doneLemma( 0 ) ... </k> requires #rangeUInt (  16 , X )
    claim [bit-n032-0]: <k> runLemma ( notMaxUInt32  &Int X ) => doneLemma( 0 ) ... </k> requires #rangeUInt (  32 , X )
    claim [bit-n064-0]: <k> runLemma ( notMaxUInt64  &Int X ) => doneLemma( 0 ) ... </k> requires #rangeUInt (  64 , X )
    claim [bit-n096-0]: <k> runLemma ( notMaxUInt96  &Int X ) => doneLemma( 0 ) ... </k> requires #rangeUInt (  96 , X )
    claim [bit-n128-0]: <k> runLemma ( notMaxUInt128 &Int X ) => doneLemma( 0 ) ... </k> requires #rangeUInt ( 128 , X )
    claim [bit-n160-0]: <k> runLemma ( notMaxUInt160 &Int X ) => doneLemma( 0 ) ... </k> requires #rangeUInt ( 160 , X )
    claim [bit-n192-0]: <k> runLemma ( notMaxUInt192 &Int X ) => doneLemma( 0 ) ... </k> requires #rangeUInt ( 192 , X )
    claim [bit-n208-0]: <k> runLemma ( notMaxUInt208 &Int X ) => doneLemma( 0 ) ... </k> requires #rangeUInt ( 208 , X )
    claim [bit-n224-0]: <k> runLemma ( notMaxUInt224 &Int X ) => doneLemma( 0 ) ... </k> requires #rangeUInt ( 224 , X )
    claim [bit-n240-0]: <k> runLemma ( notMaxUInt240 &Int X ) => doneLemma( 0 ) ... </k> requires #rangeUInt ( 240 , X )
    claim [bit-n248-0]: <k> runLemma ( notMaxUInt248 &Int X ) => doneLemma( 0 ) ... </k> requires #rangeUInt ( 248 , X )

    claim [bit-n008-shl]: <k> runLemma ( notMaxUInt8   &Int ( X <<Int   8 ) ) => doneLemma( X <<Int   8 ) ... </k> requires #rangeUInt ( 248 , X )
    claim [bit-n016-shl]: <k> runLemma ( notMaxUInt16  &Int ( X <<Int  16 ) ) => doneLemma( X <<Int  16 ) ... </k> requires #rangeUInt ( 240 , X )
    claim [bit-n032-shl]: <k> runLemma ( notMaxUInt32  &Int ( X <<Int  32 ) ) => doneLemma( X <<Int  32 ) ... </k> requires #rangeUInt ( 224 , X )
    claim [bit-n064-shl]: <k> runLemma ( notMaxUInt64  &Int ( X <<Int  64 ) ) => doneLemma( X <<Int  64 ) ... </k> requires #rangeUInt ( 192 , X )
    claim [bit-n096-shl]: <k> runLemma ( notMaxUInt96  &Int ( X <<Int  96 ) ) => doneLemma( X <<Int  96 ) ... </k> requires #rangeUInt ( 160 , X )
    claim [bit-n128-shl]: <k> runLemma ( notMaxUInt128 &Int ( X <<Int 128 ) ) => doneLemma( X <<Int 128 ) ... </k> requires #rangeUInt ( 128 , X )
    claim [bit-n160-shl]: <k> runLemma ( notMaxUInt160 &Int ( X <<Int 160 ) ) => doneLemma( X <<Int 160 ) ... </k> requires #rangeUInt (  96 , X )
    claim [bit-n192-shl]: <k> runLemma ( notMaxUInt192 &Int ( X <<Int 192 ) ) => doneLemma( X <<Int 192 ) ... </k> requires #rangeUInt (  64 , X )
    claim [bit-n208-shl]: <k> runLemma ( notMaxUInt208 &Int ( X <<Int 208 ) ) => doneLemma( X <<Int 208 ) ... </k> requires #rangeUInt (  48 , X )
    claim [bit-n224-shl]: <k> runLemma ( notMaxUInt224 &Int ( X <<Int 224 ) ) => doneLemma( X <<Int 224 ) ... </k> requires #rangeUInt (  32 , X )
    claim [bit-n240-shl]: <k> runLemma ( notMaxUInt240 &Int ( X <<Int 240 ) ) => doneLemma( X <<Int 240 ) ... </k> requires #rangeUInt (  16 , X )
    claim [bit-n248-shl]: <k> runLemma ( notMaxUInt248 &Int ( X <<Int 248 ) ) => doneLemma( X <<Int 248 ) ... </k> requires #rangeUInt (   8 , X )

    claim [bit-008-m-or-nm]: <k> runLemma ( maxUInt8   &Int ( X |Int ( notMaxUInt8   &Int T ) ) ) => doneLemma( X ) ... </k> requires #rangeUInt (   8 , X ) andBool #rangeUInt(256, T)
    claim [bit-016-m-or-nm]: <k> runLemma ( maxUInt16  &Int ( X |Int ( notMaxUInt16  &Int T ) ) ) => doneLemma( X ) ... </k> requires #rangeUInt (  16 , X ) andBool #rangeUInt(256, T)
    claim [bit-032-m-or-nm]: <k> runLemma ( maxUInt32  &Int ( X |Int ( notMaxUInt32  &Int T ) ) ) => doneLemma( X ) ... </k> requires #rangeUInt (  32 , X ) andBool #rangeUInt(256, T)
    claim [bit-064-m-or-nm]: <k> runLemma ( maxUInt64  &Int ( X |Int ( notMaxUInt64  &Int T ) ) ) => doneLemma( X ) ... </k> requires #rangeUInt (  64 , X ) andBool #rangeUInt(256, T)
    claim [bit-096-m-or-nm]: <k> runLemma ( maxUInt96  &Int ( X |Int ( notMaxUInt96  &Int T ) ) ) => doneLemma( X ) ... </k> requires #rangeUInt (  96 , X ) andBool #rangeUInt(256, T)
    claim [bit-128-m-or-nm]: <k> runLemma ( maxUInt128 &Int ( X |Int ( notMaxUInt128 &Int T ) ) ) => doneLemma( X ) ... </k> requires #rangeUInt ( 128 , X ) andBool #rangeUInt(256, T)
    claim [bit-160-m-or-nm]: <k> runLemma ( maxUInt160 &Int ( X |Int ( notMaxUInt160 &Int T ) ) ) => doneLemma( X ) ... </k> requires #rangeUInt ( 160 , X ) andBool #rangeUInt(256, T)
    claim [bit-192-m-or-nm]: <k> runLemma ( maxUInt192 &Int ( X |Int ( notMaxUInt192 &Int T ) ) ) => doneLemma( X ) ... </k> requires #rangeUInt ( 192 , X ) andBool #rangeUInt(256, T)
    claim [bit-208-m-or-nm]: <k> runLemma ( maxUInt208 &Int ( X |Int ( notMaxUInt208 &Int T ) ) ) => doneLemma( X ) ... </k> requires #rangeUInt ( 208 , X ) andBool #rangeUInt(256, T)
    claim [bit-224-m-or-nm]: <k> runLemma ( maxUInt224 &Int ( X |Int ( notMaxUInt224 &Int T ) ) ) => doneLemma( X ) ... </k> requires #rangeUInt ( 224 , X ) andBool #rangeUInt(256, T)
    claim [bit-240-m-or-nm]: <k> runLemma ( maxUInt240 &Int ( X |Int ( notMaxUInt240 &Int T ) ) ) => doneLemma( X ) ... </k> requires #rangeUInt ( 240 , X ) andBool #rangeUInt(256, T)
    claim [bit-248-m-or-nm]: <k> runLemma ( maxUInt248 &Int ( X |Int ( notMaxUInt248 &Int T ) ) ) => doneLemma( X ) ... </k> requires #rangeUInt ( 248 , X ) andBool #rangeUInt(256, T)

    // claim [bit-008-nm-or-m]: <k> runLemma ( notMaxUInt8   &Int ( X |Int ( maxUInt8   &Int T ) ) ) => doneLemma( 0 ) ... </k> requires #rangeUInt ( 248 , X ) andBool #rangeUInt(256, T)
    // claim [bit-016-nm-or-m]: <k> runLemma ( notMaxUInt16  &Int ( X |Int ( maxUInt16  &Int T ) ) ) => doneLemma( 0 ) ... </k> requires #rangeUInt ( 240 , X ) andBool #rangeUInt(256, T)
    // claim [bit-032-nm-or-m]: <k> runLemma ( notMaxUInt32  &Int ( X |Int ( maxUInt32  &Int T ) ) ) => doneLemma( 0 ) ... </k> requires #rangeUInt ( 224 , X ) andBool #rangeUInt(256, T)
    // claim [bit-064-nm-or-m]: <k> runLemma ( notMaxUInt64  &Int ( X |Int ( maxUInt64  &Int T ) ) ) => doneLemma( 0 ) ... </k> requires #rangeUInt ( 192 , X ) andBool #rangeUInt(256, T)
    // claim [bit-096-nm-or-m]: <k> runLemma ( notMaxUInt96  &Int ( X |Int ( maxUInt96  &Int T ) ) ) => doneLemma( 0 ) ... </k> requires #rangeUInt ( 160 , X ) andBool #rangeUInt(256, T)
    // claim [bit-128-nm-or-m]: <k> runLemma ( notMaxUInt128 &Int ( X |Int ( maxUInt128 &Int T ) ) ) => doneLemma( 0 ) ... </k> requires #rangeUInt ( 128 , X ) andBool #rangeUInt(256, T)
    // claim [bit-160-nm-or-m]: <k> runLemma ( notMaxUInt160 &Int ( X |Int ( maxUInt160 &Int T ) ) ) => doneLemma( 0 ) ... </k> requires #rangeUInt (  96 , X ) andBool #rangeUInt(256, T)
    // claim [bit-192-nm-or-m]: <k> runLemma ( notMaxUInt192 &Int ( X |Int ( maxUInt192 &Int T ) ) ) => doneLemma( 0 ) ... </k> requires #rangeUInt (  64 , X ) andBool #rangeUInt(256, T)
    // claim [bit-208-nm-or-m]: <k> runLemma ( notMaxUInt208 &Int ( X |Int ( maxUInt208 &Int T ) ) ) => doneLemma( 0 ) ... </k> requires #rangeUInt (  48 , X ) andBool #rangeUInt(256, T)
    // claim [bit-224-nm-or-m]: <k> runLemma ( notMaxUInt224 &Int ( X |Int ( maxUInt224 &Int T ) ) ) => doneLemma( 0 ) ... </k> requires #rangeUInt (  32 , X ) andBool #rangeUInt(256, T)
    // claim [bit-240-nm-or-m]: <k> runLemma ( notMaxUInt240 &Int ( X |Int ( maxUInt240 &Int T ) ) ) => doneLemma( 0 ) ... </k> requires #rangeUInt (  16 , X ) andBool #rangeUInt(256, T)
    // claim [bit-248-nm-or-m]: <k> runLemma ( notMaxUInt248 &Int ( X |Int ( maxUInt248 &Int T ) ) ) => doneLemma( 0 ) ... </k> requires #rangeUInt (   8 , X ) andBool #rangeUInt(256, T)

    claim [bit-008-m-aW]: <k> runLemma ( maxUInt8   &Int #asWord ( BA ) ) => doneLemma ( #asWord ( #range(BA, 31,  1) ) ) ... </k> requires lengthBytes(BA) ==Int 32
    claim [bit-016-m-aW]: <k> runLemma ( maxUInt16  &Int #asWord ( BA ) ) => doneLemma ( #asWord ( #range(BA, 30,  2) ) ) ... </k> requires lengthBytes(BA) ==Int 32
    claim [bit-024-m-aW]: <k> runLemma ( maxUInt24  &Int #asWord ( BA ) ) => doneLemma ( #asWord ( #range(BA, 29,  3) ) ) ... </k> requires lengthBytes(BA) ==Int 32
    claim [bit-032-m-aW]: <k> runLemma ( maxUInt32  &Int #asWord ( BA ) ) => doneLemma ( #asWord ( #range(BA, 28,  4) ) ) ... </k> requires lengthBytes(BA) ==Int 32
    claim [bit-040-m-aW]: <k> runLemma ( maxUInt40  &Int #asWord ( BA ) ) => doneLemma ( #asWord ( #range(BA, 27,  5) ) ) ... </k> requires lengthBytes(BA) ==Int 32
    claim [bit-048-m-aW]: <k> runLemma ( maxUInt48  &Int #asWord ( BA ) ) => doneLemma ( #asWord ( #range(BA, 26,  6) ) ) ... </k> requires lengthBytes(BA) ==Int 32
    claim [bit-056-m-aW]: <k> runLemma ( maxUInt56  &Int #asWord ( BA ) ) => doneLemma ( #asWord ( #range(BA, 25,  7) ) ) ... </k> requires lengthBytes(BA) ==Int 32
    claim [bit-064-m-aW]: <k> runLemma ( maxUInt64  &Int #asWord ( BA ) ) => doneLemma ( #asWord ( #range(BA, 24,  8) ) ) ... </k> requires lengthBytes(BA) ==Int 32
    claim [bit-072-m-aW]: <k> runLemma ( maxUInt72  &Int #asWord ( BA ) ) => doneLemma ( #asWord ( #range(BA, 23,  9) ) ) ... </k> requires lengthBytes(BA) ==Int 32
    claim [bit-080-m-aW]: <k> runLemma ( maxUInt80  &Int #asWord ( BA ) ) => doneLemma ( #asWord ( #range(BA, 22, 10) ) ) ... </k> requires lengthBytes(BA) ==Int 32
    claim [bit-088-m-aW]: <k> runLemma ( maxUInt88  &Int #asWord ( BA ) ) => doneLemma ( #asWord ( #range(BA, 21, 11) ) ) ... </k> requires lengthBytes(BA) ==Int 32
    claim [bit-096-m-aW]: <k> runLemma ( maxUInt96  &Int #asWord ( BA ) ) => doneLemma ( #asWord ( #range(BA, 20, 12) ) ) ... </k> requires lengthBytes(BA) ==Int 32
    claim [bit-104-m-aW]: <k> runLemma ( maxUInt104 &Int #asWord ( BA ) ) => doneLemma ( #asWord ( #range(BA, 19, 13) ) ) ... </k> requires lengthBytes(BA) ==Int 32
    claim [bit-112-m-aW]: <k> runLemma ( maxUInt112 &Int #asWord ( BA ) ) => doneLemma ( #asWord ( #range(BA, 18, 14) ) ) ... </k> requires lengthBytes(BA) ==Int 32
    claim [bit-120-m-aW]: <k> runLemma ( maxUInt120 &Int #asWord ( BA ) ) => doneLemma ( #asWord ( #range(BA, 17, 15) ) ) ... </k> requires lengthBytes(BA) ==Int 32
    claim [bit-128-m-aW]: <k> runLemma ( maxUInt128 &Int #asWord ( BA ) ) => doneLemma ( #asWord ( #range(BA, 16, 16) ) ) ... </k> requires lengthBytes(BA) ==Int 32
    claim [bit-136-m-aW]: <k> runLemma ( maxUInt136 &Int #asWord ( BA ) ) => doneLemma ( #asWord ( #range(BA, 15, 17) ) ) ... </k> requires lengthBytes(BA) ==Int 32
    claim [bit-144-m-aW]: <k> runLemma ( maxUInt144 &Int #asWord ( BA ) ) => doneLemma ( #asWord ( #range(BA, 14, 18) ) ) ... </k> requires lengthBytes(BA) ==Int 32
    claim [bit-152-m-aW]: <k> runLemma ( maxUInt152 &Int #asWord ( BA ) ) => doneLemma ( #asWord ( #range(BA, 13, 19) ) ) ... </k> requires lengthBytes(BA) ==Int 32
    claim [bit-160-m-aW]: <k> runLemma ( maxUInt160 &Int #asWord ( BA ) ) => doneLemma ( #asWord ( #range(BA, 12, 20) ) ) ... </k> requires lengthBytes(BA) ==Int 32
    claim [bit-168-m-aW]: <k> runLemma ( maxUInt168 &Int #asWord ( BA ) ) => doneLemma ( #asWord ( #range(BA, 11, 21) ) ) ... </k> requires lengthBytes(BA) ==Int 32
    claim [bit-176-m-aW]: <k> runLemma ( maxUInt176 &Int #asWord ( BA ) ) => doneLemma ( #asWord ( #range(BA, 10, 22) ) ) ... </k> requires lengthBytes(BA) ==Int 32
    claim [bit-184-m-aW]: <k> runLemma ( maxUInt184 &Int #asWord ( BA ) ) => doneLemma ( #asWord ( #range(BA,  9, 23) ) ) ... </k> requires lengthBytes(BA) ==Int 32
    claim [bit-192-m-aW]: <k> runLemma ( maxUInt192 &Int #asWord ( BA ) ) => doneLemma ( #asWord ( #range(BA,  8, 24) ) ) ... </k> requires lengthBytes(BA) ==Int 32
    claim [bit-200-m-aW]: <k> runLemma ( maxUInt200 &Int #asWord ( BA ) ) => doneLemma ( #asWord ( #range(BA,  7, 25) ) ) ... </k> requires lengthBytes(BA) ==Int 32
    claim [bit-208-m-aW]: <k> runLemma ( maxUInt208 &Int #asWord ( BA ) ) => doneLemma ( #asWord ( #range(BA,  6, 26) ) ) ... </k> requires lengthBytes(BA) ==Int 32
    claim [bit-216-m-aW]: <k> runLemma ( maxUInt216 &Int #asWord ( BA ) ) => doneLemma ( #asWord ( #range(BA,  5, 27) ) ) ... </k> requires lengthBytes(BA) ==Int 32
    claim [bit-224-m-aW]: <k> runLemma ( maxUInt224 &Int #asWord ( BA ) ) => doneLemma ( #asWord ( #range(BA,  4, 28) ) ) ... </k> requires lengthBytes(BA) ==Int 32
    claim [bit-232-m-aW]: <k> runLemma ( maxUInt232 &Int #asWord ( BA ) ) => doneLemma ( #asWord ( #range(BA,  3, 29) ) ) ... </k> requires lengthBytes(BA) ==Int 32
    claim [bit-240-m-aW]: <k> runLemma ( maxUInt240 &Int #asWord ( BA ) ) => doneLemma ( #asWord ( #range(BA,  2, 30) ) ) ... </k> requires lengthBytes(BA) ==Int 32
    claim [bit-248-m-aW]: <k> runLemma ( maxUInt248 &Int #asWord ( BA ) ) => doneLemma ( #asWord ( #range(BA,  1, 31) ) ) ... </k> requires lengthBytes(BA) ==Int 32
    claim [bit-256-m-aW]: <k> runLemma ( maxUInt256 &Int #asWord ( BA ) ) => doneLemma ( #asWord ( #range(BA,  0, 32) ) ) ... </k> requires lengthBytes(BA) ==Int 32

    claim [bit-008-nm-aW]: <k> runLemma ( notMaxUInt8   &Int #asWord ( BA ) ) => doneLemma ( #asWord ( #range(BA, 0, 31) +Bytes #buf (  1, 0 ) ) ) ... </k> requires lengthBytes(BA) ==Int 32
    claim [bit-016-nm-aW]: <k> runLemma ( notMaxUInt16  &Int #asWord ( BA ) ) => doneLemma ( #asWord ( #range(BA, 0, 30) +Bytes #buf (  2, 0 ) ) ) ... </k> requires lengthBytes(BA) ==Int 32
    claim [bit-032-nm-aW]: <k> runLemma ( notMaxUInt32  &Int #asWord ( BA ) ) => doneLemma ( #asWord ( #range(BA, 0, 28) +Bytes #buf (  4, 0 ) ) ) ... </k> requires lengthBytes(BA) ==Int 32
    claim [bit-064-nm-aW]: <k> runLemma ( notMaxUInt64  &Int #asWord ( BA ) ) => doneLemma ( #asWord ( #range(BA, 0, 24) +Bytes #buf (  8, 0 ) ) ) ... </k> requires lengthBytes(BA) ==Int 32
    claim [bit-096-nm-aW]: <k> runLemma ( notMaxUInt96  &Int #asWord ( BA ) ) => doneLemma ( #asWord ( #range(BA, 0, 20) +Bytes #buf ( 12, 0 ) ) ) ... </k> requires lengthBytes(BA) ==Int 32
    claim [bit-128-nm-aW]: <k> runLemma ( notMaxUInt128 &Int #asWord ( BA ) ) => doneLemma ( #asWord ( #range(BA, 0, 16) +Bytes #buf ( 16, 0 ) ) ) ... </k> requires lengthBytes(BA) ==Int 32
    claim [bit-160-nm-aW]: <k> runLemma ( notMaxUInt160 &Int #asWord ( BA ) ) => doneLemma ( #asWord ( #range(BA, 0, 12) +Bytes #buf ( 20, 0 ) ) ) ... </k> requires lengthBytes(BA) ==Int 32
    claim [bit-192-nm-aW]: <k> runLemma ( notMaxUInt192 &Int #asWord ( BA ) ) => doneLemma ( #asWord ( #range(BA, 0, 8)  +Bytes #buf ( 24, 0 ) ) ) ... </k> requires lengthBytes(BA) ==Int 32
    claim [bit-208-nm-aW]: <k> runLemma ( notMaxUInt208 &Int #asWord ( BA ) ) => doneLemma ( #asWord ( #range(BA, 0, 6)  +Bytes #buf ( 26, 0 ) ) ) ... </k> requires lengthBytes(BA) ==Int 32
    claim [bit-224-nm-aW]: <k> runLemma ( notMaxUInt224 &Int #asWord ( BA ) ) => doneLemma ( #asWord ( #range(BA, 0, 4)  +Bytes #buf ( 28, 0 ) ) ) ... </k> requires lengthBytes(BA) ==Int 32
    claim [bit-240-nm-aW]: <k> runLemma ( notMaxUInt240 &Int #asWord ( BA ) ) => doneLemma ( #asWord ( #range(BA, 0, 2)  +Bytes #buf ( 30, 0 ) ) ) ... </k> requires lengthBytes(BA) ==Int 32
    claim [bit-248-nm-aW]: <k> runLemma ( notMaxUInt248 &Int #asWord ( BA ) ) => doneLemma ( #asWord ( #range(BA, 0, 1)  +Bytes #buf ( 31, 0 ) ) ) ... </k> requires lengthBytes(BA) ==Int 32

    claim <k> runLemma ( #buf ( 32 , #asWord ( X ) ) ) => doneLemma( X ) </k> requires lengthBytes(X) ==Int 32
    claim <k> runLemma ( #buf ( 32 , X <<Int 248 ) ) => doneLemma( #buf ( 1 , X ) +Bytes #buf ( 31 , 0 ) ) ... </k> requires #rangeUInt (  8 , X )
    claim <k> runLemma ( #buf ( 32 , X <<Int 240 ) ) => doneLemma( #buf ( 2 , X ) +Bytes #buf ( 30 , 0 ) ) ... </k> requires #rangeUInt ( 16 , X )

    claim [band-maxUInt-lt-01]: <k> runLemma ( maxUInt8   &Int X <Int    256 ) => doneLemma ( true ) ... </k> requires 0 <=Int X
    claim [band-maxUInt-lt-02]: <k> runLemma ( maxUInt48  &Int X <Int  pow48 ) => doneLemma ( true ) ... </k> requires 0 <=Int X
    claim [band-maxUInt-lt-03]: <k> runLemma ( maxUInt160 &Int X <Int pow160 ) => doneLemma ( true ) ... </k> requires 0 <=Int X

 // shift
 // -----

    claim [shift-16] : <k> runLemma ( ( X <<Int  16 ) <Int pow256 ) => doneLemma ( true ) ... </k> requires #rangeUInt ( 240 , X )
    claim [shift-240]: <k> runLemma ( ( X <<Int 240 ) <Int pow256 ) => doneLemma ( true ) ... </k> requires #rangeUInt (  16 , X )
    claim [shift-248]: <k> runLemma ( ( X <<Int 248 ) <Int pow256 ) => doneLemma ( true ) ... </k> requires #rangeUInt (   8 , X )

    claim [shift-range]: <k> runLemma ( #rangeUInt ( 256 , X <<Int 16 ) ) => doneLemma ( true ) ... </k> requires #rangeUInt ( 16 , X )
    claim [shift-mod]: <k> runLemma ( ( X <<Int 16 ) modInt pow256 ) => doneLemma ( X <<Int 16 ) ... </k> requires #rangeUInt ( 16 , X )

 // concat
 // ------

    claim <k> runLemma ( lengthBytes ( #range ( #buf ( 32 , _X ) , 3 , 29 ) +Bytes b"\x01" +Bytes #buf ( 2 , Y ) ) )
        => doneLemma ( 32 ) ... </k>
        requires #rangeUInt ( 16 , Y )

    claim <k> runLemma ( #asWord ( #range ( #buf ( 32 , X ) , 0 , 29 ) +Bytes #range ( #buf ( 32 , X ) , 29 , 3 ) ) )
        => doneLemma ( X ) ... </k>
        requires #rangeUInt ( 256 , X )

 // #padRightToWidth
 // ----------------

    claim [pRTW-01]:
      <k> runLemma (
            notBool ( #asWord ( #padRightToWidth ( 32 , #buf ( 4 , VV0_x_114b9705:Int ) ) ) ==Int
              #asWord ( #buf ( 4 , VV0_x_114b9705:Int ) +Bytes b"\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00" ) )
          ) => doneLemma(
            false
          ) ... </k>
        requires #rangeUInt(32, VV0_x_114b9705)

 // #asWord
 // ----------------

    claim [buf-asWord-invert]:
      <k> runLemma(
            #asWord ( #buf ( 63 , lengthBytes ( VV0_data_114b9705:Bytes ) ) ) <=Int maxUInt64
          ) => doneLemma(
            true
          ) ... </k>
        requires lengthBytes ( VV0_data_114b9705:Bytes ) <=Int 1073741824

 // bool2Word
 // ---------

    // b2w-gt-zero, b2w-lt-b2w, b2w-band-one, b2w-band, b2w-mul-lt-l
    claim [b2w-01]:
      <k> runLemma (
            ( bool2Word( 0 <=Int X:Int ) &Int 1 ) *Int bool2Word( X <Int -5 ) <Int ( bool2Word( 5 <=Int X ) &Int bool2Word( X <=Int 10 ) )
          ) => doneLemma (
            5 <=Int X andBool X <=Int 10
          ) ... </k>

    // b2w-eq-zero, b2w-xor-zero, b2w-xor-one, b2w-xor, b2w-mul-eq-l
    claim [b2w-02]:
      <k> runLemma (
            ( bool2Word( 0 <=Int X:Int ) *Int ( 0 xorInt bool2Word( X <=Int 0 ) ) ) ==Int 1 xorInt ( bool2Word( X <=Int 0 ) xorInt bool2Word( X >=Int 0 ) )
          ) => doneLemma (
            true
          ) ... </k>

    // b2w-lt-one, b2w-bor-one, b2w-mul-le-l
    claim [b2w-03]:
      <k> runLemma (
            ( bool2Word ( 0 <=Int X:Int ) *Int bool2Word( 0 <Int X ) ) <Int 1 |Int bool2Word( X =/=Int X )
          ) => doneLemma (
            X <=Int 0
          ) ... </k>

    // b2w-gt-false, b2w-mul-lt-r
    claim [b2w-04]:
      <k> runLemma (
            ( bool2Word ( notBool X ) *Int 42 ) <Int bool2Word ( Y )
          ) => doneLemma (
            X andBool Y
          ) ... </k>

    // b2w-lt-true
    claim [b2w-05]:
      <k> runLemma (
            bool2Word ( _X ) *Int bool2Word ( _Y ) <Int 42
          ) => doneLemma (
            true
          ) ... </k>

 // ecrecover
 // ---------

    claim [ecrec-length]: <k> runLemma  ( lengthBytes ( #ecrec ( _ , _ , _ , _ ) ) <=Int 32 )
                           => doneLemma ( true ) ... </k>

    claim [ecrec-split]: <k> runLemma  ( #range ( #buf(160, 0) +Bytes _BUF , lengthBytes ( #ecrec ( HASH , SIGV , SIGR , SIGS ) ) +Int 128 , 32 -Int lengthBytes ( #ecrec ( HASH , SIGV , SIGR , SIGS ) ) ) )
                          => doneLemma ( #range ( #buf( 32, 0)             , lengthBytes ( #ecrec ( HASH , SIGV , SIGR , SIGS ) )          , 32 -Int lengthBytes ( #ecrec ( HASH , SIGV , SIGR , SIGS ) ) ) ) ... </k>

    claim [ecrec-range]: <k> runLemma  ( #rangeUInt ( 160 , #asWord ( #ecrec ( _ , _ , _ , _ ) ) ) )
                          => doneLemma ( true ) ... </k>

    // claim [ecrec-mask]: <k> runLemma  ( #asWord ( #ecrec ( HASH , SIGV , SIGR , SIGS ) ) &Int maxUInt160 )
    //                      => doneLemma ( #asWord ( #ecrec ( HASH , SIGV , SIGR , SIGS ) ) ) ... </k>

 // Address computation
 // -------------------

    claim [addr-from-private-key]: <k> runLemma  ( #addrFromPrivateKey(#unparseDataBytes(b"\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x01")) )
                                    => doneLemma ( 721457446580647751014191829380889690493307935711 ) ... </k>

 // Precompiled accounts
 // --------------------

    claim [precompiledAccountsSet-correctness]:
          <k> runLemma (
                         #precompiledAccountsSet(DEFAULT)           ==K SetItem (1) ( SetItem (2) ( SetItem (3) SetItem (4) ) )
                 andBool #precompiledAccountsSet(FRONTIER)          ==K SetItem (1) ( SetItem (2) ( SetItem (3) SetItem (4) ) )
                 andBool #precompiledAccountsSet(HOMESTEAD)         ==K SetItem (1) ( SetItem (2) ( SetItem (3) SetItem (4) ) )
                 andBool #precompiledAccountsSet(TANGERINE_WHISTLE) ==K SetItem (1) ( SetItem (2) ( SetItem (3) SetItem (4) ) )
                 andBool #precompiledAccountsSet(SPURIOUS_DRAGON)   ==K SetItem (1) ( SetItem (2) ( SetItem (3) SetItem (4) ) )
                 andBool #precompiledAccountsSet(BYZANTIUM)         ==K SetItem (1) ( SetItem (2) ( SetItem (3) ( SetItem (4) ( SetItem (5) ( SetItem (6) ( SetItem (7) SetItem (8) ) ) ) ) ) )
                 andBool #precompiledAccountsSet(CONSTANTINOPLE)    ==K SetItem (1) ( SetItem (2) ( SetItem (3) ( SetItem (4) ( SetItem (5) ( SetItem (6) ( SetItem (7) SetItem (8) ) ) ) ) ) )
                 andBool #precompiledAccountsSet(PETERSBURG)        ==K SetItem (1) ( SetItem (2) ( SetItem (3) ( SetItem (4) ( SetItem (5) ( SetItem (6) ( SetItem (7) SetItem (8) ) ) ) ) ) )
                 andBool #precompiledAccountsSet(ISTANBUL)          ==K SetItem (1) ( SetItem (2) ( SetItem (3) ( SetItem (4) ( SetItem (5) ( SetItem (6) ( SetItem (7) ( SetItem (8) SetItem (9) ) ) ) ) ) ) )
                 andBool #precompiledAccountsSet(BERLIN)            ==K SetItem (1) ( SetItem (2) ( SetItem (3) ( SetItem (4) ( SetItem (5) ( SetItem (6) ( SetItem (7) ( SetItem (8) SetItem (9) ) ) ) ) ) ) )
                 andBool #precompiledAccountsSet(LONDON)            ==K SetItem (1) ( SetItem (2) ( SetItem (3) ( SetItem (4) ( SetItem (5) ( SetItem (6) ( SetItem (7) ( SetItem (8) SetItem (9) ) ) ) ) ) ) )
                 andBool #precompiledAccountsSet(MERGE)             ==K SetItem (1) ( SetItem (2) ( SetItem (3) ( SetItem (4) ( SetItem (5) ( SetItem (6) ( SetItem (7) ( SetItem (8) SetItem (9) ) ) ) ) ) ) )
                 andBool #precompiledAccountsSet(SHANGHAI)          ==K SetItem (1) ( SetItem (2) ( SetItem (3) ( SetItem (4) ( SetItem (5) ( SetItem (6) ( SetItem (7) ( SetItem (8) SetItem (9) ) ) ) ) ) ) )
              ) => doneLemma ( true ) ... </k>

    claim [precompiledAccounts-slowdown]: <k> runLemma  ( X:Bool ) => doneLemma ( X:Bool ) ... </k>
      requires #isPrecompiledAccount(_A00, SHANGHAI) andBool #isPrecompiledAccount(_A01, SHANGHAI) andBool #isPrecompiledAccount(_A02, SHANGHAI) andBool #isPrecompiledAccount(_A03, SHANGHAI) andBool #isPrecompiledAccount(_A04, SHANGHAI)
       andBool #isPrecompiledAccount(_A05, SHANGHAI) andBool #isPrecompiledAccount(_A06, SHANGHAI) andBool #isPrecompiledAccount(_A07, SHANGHAI) andBool #isPrecompiledAccount(_A08, SHANGHAI) andBool #isPrecompiledAccount(_A09, SHANGHAI)
       andBool #isPrecompiledAccount(_A10, SHANGHAI) andBool #isPrecompiledAccount(_A11, SHANGHAI) andBool #isPrecompiledAccount(_A12, SHANGHAI) andBool #isPrecompiledAccount(_A13, SHANGHAI) andBool #isPrecompiledAccount(_A14, SHANGHAI)
       andBool #isPrecompiledAccount(_A15, SHANGHAI) andBool #isPrecompiledAccount(_A16, SHANGHAI) andBool #isPrecompiledAccount(_A17, SHANGHAI) andBool #isPrecompiledAccount(_A18, SHANGHAI) andBool #isPrecompiledAccount(_A19, SHANGHAI)
       andBool #isPrecompiledAccount(_A20, SHANGHAI) andBool #isPrecompiledAccount(_A21, SHANGHAI) andBool #isPrecompiledAccount(_A22, SHANGHAI) andBool #isPrecompiledAccount(_A23, SHANGHAI) andBool #isPrecompiledAccount(_A24, SHANGHAI)
       andBool #isPrecompiledAccount(_A25, SHANGHAI) andBool #isPrecompiledAccount(_A26, SHANGHAI) andBool #isPrecompiledAccount(_A27, SHANGHAI) andBool #isPrecompiledAccount(_A28, SHANGHAI) andBool #isPrecompiledAccount(_A29, SHANGHAI)
       andBool #isPrecompiledAccount(_A30, SHANGHAI) andBool #isPrecompiledAccount(_A31, SHANGHAI) andBool #isPrecompiledAccount(_A32, SHANGHAI) andBool #isPrecompiledAccount(_A33, SHANGHAI) andBool #isPrecompiledAccount(_A34, SHANGHAI)
       andBool #isPrecompiledAccount(_A35, SHANGHAI) andBool #isPrecompiledAccount(_A36, SHANGHAI) andBool #isPrecompiledAccount(_A37, SHANGHAI) andBool #isPrecompiledAccount(_A38, SHANGHAI) andBool #isPrecompiledAccount(_A39, SHANGHAI)
       andBool #isPrecompiledAccount(_A40, SHANGHAI) andBool #isPrecompiledAccount(_A41, SHANGHAI) andBool #isPrecompiledAccount(_A42, SHANGHAI) andBool #isPrecompiledAccount(_A43, SHANGHAI) andBool #isPrecompiledAccount(_A44, SHANGHAI)
       andBool #isPrecompiledAccount(_A45, SHANGHAI) andBool #isPrecompiledAccount(_A46, SHANGHAI) andBool #isPrecompiledAccount(_A47, SHANGHAI) andBool #isPrecompiledAccount(_A48, SHANGHAI) andBool #isPrecompiledAccount(_A49, SHANGHAI)

endmodule
