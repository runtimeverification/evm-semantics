requires "edsl.md"
requires "lemmas/lemmas.k"

module VERIFICATION
    imports EDSL
    imports LEMMAS
endmodule

module LEMMAS-SPEC
    imports VERIFICATION

 // bool2Word
 // ---------

    claim bool2Word((UINT8 ==K 0) ==K false) => UINT8 requires #rangeBool(UINT8)

 // sizeBytes
 // -------------

    claim lengthBytes(#padToWidth(32, #asByteStack(#hashedLocation("Solidity", 2, OWNER .IntList)))) => 32 requires #rangeUInt(256, OWNER)

    claim lengthBytes(#buf(X, 0) +Bytes #padRightToWidth(Y:Int, B:Bytes)) => X +Int Y requires lengthBytes(B) <Int X andBool lengthBytes(B) <Int Y

 // Addresses
 // ---------

    claim #isPrecompiledAccount(#newAddr(TESTER_ACCT, 1), ISTANBUL) => false requires #rangeAddress(TESTER_ACCT)

 // Arithmetic
 // ----------

    claim #rangeUInt(256, #lookup(M, KX) -Int #lookup(M, KY)) => true
      requires #rangeUInt(256, X) andBool X ==Int #lookup(M,  KX)
       andBool #rangeUInt(256, Y) andBool Y ==Int #lookup(M,  KY)
       andBool #rangeUInt(256, Z) andBool Z ==Int #lookup(M, _KZ)
       andBool #rangeUInt(256, (X -Int Y) -Int Z)

    claim [address-reprojection]: (maxUInt160 &Int ((368263281805664599098893944405654396525700029268 |Int (notMaxUInt160 &Int X:Int)) modInt pow256)) modInt pow160
                               => 368263281805664599098893944405654396525700029268
                                requires #rangeUInt(256, X)

    claim [address-reprojection-1]: 0 <=Int (368263281805664599098893944405654396525700029268 |Int (notMaxUInt160 &Int X:Int)) => true requires #rangeUInt(256, X)
    claim [address-reprojection-2]: 0 <=Int (notMaxUInt160 &Int X:Int) => true requires #rangeUInt(256, X)
    claim [address-reprojection-4]: 368263281805664599098893944405654396525700029268 |Int (notMaxUInt160 &Int X:Int) <Int pow256 => true requires #rangeUInt(256, X)
    claim [address-reprojection-5]: notMaxUInt160 &Int X:Int <Int pow256 => true requires #rangeUInt(256, X)

    claim [address-reprojection-6]: maxUInt160 &Int (368263281805664599098893944405654396525700029268 |Int (notMaxUInt160 &Int X:Int))
                                 => 368263281805664599098893944405654396525700029268
                                  requires #rangeUInt(256, X)

    claim [address-insertion-1]: 368263281805664599098893944405654396525700029268 |Int (notMaxUInt160 &Int #lookup(ACCT_STORAGE:Map, 8))
                              => 368263281805664599098893944405654396525700029268
                               requires #lookup(ACCT_STORAGE, 8) <Int pow160

 // Buffer write simplifications
 // ----------------------------

    // claim M [ L := .Bytes ] [ N := WS:Bytes ]                             => M [ N := WS ]                    requires L <=Int N
    // claim M [ L := WS:Bytes ] [ N := .Bytes ]                             => M [ L := WS ]                    requires N <=Int L
    // claim M [ 32 := (0 : 1 : 2 : .Bytes) ] [ 32 := (3 : 4 : 5 : .Bytes) ] => M [ 32 := (3 : 4 : 5 : .Bytes) ]

    claim M:Map [ I1 <- 1 ] [ I2 <- 2 ] => M [ I1 <- 1 ] [ I2 <- 2 ] requires I1  <Int I2
    claim M:Map [ I1 <- 1 ] [ I2 <- 2 ] => M [ I2 <- 2 ] [ I1 <- 1 ] requires I1  >Int I2
    claim M:Map [ I1 <- 1 ] [ I2 <- 2 ] => M [ I1 <- 2 ]             requires I1 ==Int I2
    claim M:Map [ I1 <- 1 ] [ I2 <- 2 ] => M [ I2 <- 2 ]             requires I1 ==Int I2

    claim M:Bytes [ 32 := BA1 ] [ 32 := BA2 ]                                                                  => M [ 32 := BA2 ]                                                                  requires lengthBytes(BA1) <=Int lengthBytes(BA2)
    claim M:Bytes [ 32 := BA1 ] [ 32 := #padToWidth(32, #asByteStack(#hashedLocation("Solidity", 2, OWNER))) ] => M [ 32 := #padToWidth(32, #asByteStack(#hashedLocation("Solidity", 2, OWNER))) ] requires lengthBytes(BA1) ==Int 32 andBool #rangeUInt(256, OWNER)

    // Memory write past the end of the buffer
    claim [write-past-end]: #buf(160, A) [ 160 := #buf(32, B) ] [ 192 := #buf(32, C) ] [ 224 := #buf(32, D) ] [ 256 := #buf(32, E) ]
                         => #buf(160, A) +Bytes #buf(32, B) +Bytes #buf(32, C) +Bytes #buf(32, D) +Bytes #buf(32, E)

 // #lookup simplifications
 // -----------------------

    claim #lookupMemory(( KEY |-> 33) (_KEY' |-> 728) (_KEY'' |-> (pow256 +Int 5)) (_KEY''' |-> "hello"), KEY)    =>  33
    claim #lookupMemory((_KEY |-> 33) ( KEY' |-> 728) (_KEY'' |-> (pow256 +Int 5)) (_KEY''' |-> "hello"), KEY')   =>  216
    claim #lookupMemory((_KEY |-> 33) (_KEY' |-> 728) ( KEY'' |-> (pow256 +Int 5)) (_KEY''' |-> "hello"), KEY'')  =>  5
    claim #lookupMemory((_KEY |-> 33) (_KEY' |-> 728) (_KEY'' |-> (pow256 +Int 5)) ( KEY''' |-> "hello"), KEY''') =>  0
    //TODO Haskell limitation? https://github.com/runtimeverification/haskell-backend/issues/1948
    //claim #lookupMemory((KEY |-> 33), KEY') => 0 requires notBool KEY' in_keys(KEY |-> 33)

    claim #lookup(( KEY |-> 33) (_KEY' |-> 728) (_KEY'' |-> (pow256 +Int 5)) (_KEY''' |-> "hello"), KEY)    => 33
    claim #lookup((_KEY |-> 33) ( KEY' |-> 728) (_KEY'' |-> (pow256 +Int 5)) (_KEY''' |-> "hello"), KEY')   => 728
    claim #lookup((_KEY |-> 33) (_KEY' |-> 728) ( KEY'' |-> (pow256 +Int 5)) (_KEY''' |-> "hello"), KEY'')  => 5
    claim #lookup((_KEY |-> 33) (_KEY' |-> 728) (_KEY'' |-> (pow256 +Int 5)) ( KEY''' |-> "hello"), KEY''') => 0
    //claim #lookup((KEY |-> 33), KEY') => 0 requires notBool KEY' in_keys(KEY |-> 33)

    claim #lookup( _M:Map [ KEY <- 33 ] [ KEY' <- 728 ] [ KEY'' <- (pow256 +Int 5) ] [ KEY''' <- "hello" ] , KEY    ) => 33  requires KEY =/=Int KEY' andBool KEY =/=Int KEY'' andBool KEY =/=Int KEY''' andBool KEY' =/=Int KEY'' andBool KEY' =/=Int KEY''' andBool KEY'' =/=Int KEY'''
    claim #lookup( _M:Map [ KEY <- 33 ] [ KEY' <- 728 ] [ KEY'' <- (pow256 +Int 5) ] [ KEY''' <- "hello" ] , KEY'   ) => 728 requires KEY =/=Int KEY' andBool KEY =/=Int KEY'' andBool KEY =/=Int KEY''' andBool KEY' =/=Int KEY'' andBool KEY' =/=Int KEY''' andBool KEY'' =/=Int KEY'''
    claim #lookup( _M:Map [ KEY <- 33 ] [ KEY' <- 728 ] [ KEY'' <- (pow256 +Int 5) ] [ KEY''' <- "hello" ] , KEY''  ) => 5   requires KEY =/=Int KEY' andBool KEY =/=Int KEY'' andBool KEY =/=Int KEY''' andBool KEY' =/=Int KEY'' andBool KEY' =/=Int KEY''' andBool KEY'' =/=Int KEY'''
    claim #lookup( _M:Map [ KEY <- 33 ] [ KEY' <- 728 ] [ KEY'' <- (pow256 +Int 5) ] [ KEY''' <- "hello" ] , KEY''' ) => 0   requires KEY =/=Int KEY' andBool KEY =/=Int KEY'' andBool KEY =/=Int KEY''' andBool KEY' =/=Int KEY'' andBool KEY' =/=Int KEY''' andBool KEY'' =/=Int KEY'''

 // #range selection operation
 // --------------------------

    // Non-positive range
    claim [range-01]: #range(_M, _N,  0) => .Bytes
    claim [range-02]: #range(_M, _N, -3) => .Bytes

    // Range outside of previous buffer write
    claim [range-03]: #range ( M [ 32 := _          ], 20, 4) => #range(M, 20, 4)
    claim [range-04]: #range ( M [ 32 := BUF:Bytes  ], 48, 4) => #range(M, 48, 4) requires lengthBytes(BUF) <=Int 12
    claim [range-05]: #range ( M [ 32 := _          ], 31, 1) => #range(M, 31, 1)
    claim [range-06]: #range ( M [ 32 := #buf(1, _) ], 33, 1) => #range(M, 33, 1)

    // Range starting before buffer write
    claim [range-07]: #range(M [ 32 := BUF:Bytes ]            , 30 , 8) => #range(M, 30, 2) +Bytes (#range(BUF, 0, 6))                          requires lengthBytes(BUF) >=Int 6
    claim [range-08]: #range(M [ 32 := (0 : 1 : 2 : .Bytes) ] , 30 , 8) => #range(M, 30, 2) +Bytes (0 : 1 : 2 : .Bytes) +Bytes #range(M, 35, 3)
    claim [range-09]: #range(M [ 32 := #buf(2, BUF) ]         , 31 , 2) => #range(M, 31, 1) +Bytes (#range(#buf(2, BUF), 0, 1) )
    claim [range-10]: #range(M [ 32 := #buf(1, BUF) ]         , 31 , 2) => #range(M, 31, 1) +Bytes #buf(1, BUF)
    claim [range-11]: #range(M [ 32 := #buf(1, BUF) ]         , 31 , 3) => #range(M, 31, 1) +Bytes #buf(1, BUF) +Bytes #range(M, 33, 1)

    // Range starting at same point as buffer write
    claim [range-12]: #range(_M [ 32 := BUF:Bytes ]            , 32 , 7) => #range( BUF, 0, 7 )                          requires lengthBytes(BUF) >=Int 7
    claim [range-13]: #range( M [ 32 := (0 : 1 : 2 : .Bytes) ] , 32 , 7) => (0 : 1 : 2 : .Bytes) +Bytes #range(M, 35, 4)
    claim [range-14]: #range(_M [ 32 := #buf(2, BUF) ]         , 32 , 1) => #range(#buf(2, BUF), 0, 1 )
    claim [range-15]: #range(_M [ 32 := #buf(1, BUF) ]         , 32 , 1) => #buf(1, BUF)
    claim [range-16]: #range (M [ 32 := #buf(1, BUF) ]         , 32 , 2) => #buf(1, BUF) +Bytes #range(M, 33, 1)

    // Range starting in the middle of the buffer write
    claim [range-17]: #range(_M [ 32 := (0 : 1 : 2 : 3 : 4 : .Bytes) ] , 35 , 2) => (3 : 4 : .Bytes)
    claim [range-18]: #range( M [ 32 := (0 : 1 : 2 : 3 : 4 : .Bytes) ] , 35 , 8) => (3 : 4 : .Bytes) +Bytes #range(M, 37, 6)
    claim [range-19]: #range(_M [ 32 := (0 : 1 : 2 : .Bytes)         ] , 33 , 1) => (1 : .Bytes)
    claim [range-20]: #range(_M [ 32 := (0 : 1 : 2 : .Bytes)         ] , 33 , 2) => (1 : 2 : .Bytes)
    claim [range-21]: #range( M [ 32 := (0 : 1 : 2 : .Bytes)         ] , 33 , 3) => (1 : 2 :  .Bytes) +Bytes #range(M, 35, 1)

    claim [range-22]: #range ( #range ( BA:Bytes , 4 , 64 ) , 32 , 32 ) => #range ( BA , 36 , 32 )

    claim [range-23]: #range(#buf(DATA_LEN, DATA) +Bytes _BUF, 0, DATA_LEN) => #range( #buf(DATA_LEN, DATA) , 0, DATA_LEN)
      requires #range(0 <= DATA < (2 ^Int (DATA_LEN *Int 8)))
       andBool 0 <=Int DATA_LEN

    claim [range-24]: #range ( #range ( b"\x01\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00" , lengthBytes ( VV6__data_3c5818c8:Bytes ) +Int 1 , 31 -Int lengthBytes ( VV6__data_3c5818c8:Bytes ) ) , 32 , lengthBytes ( #range ( b"\x01\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00" , lengthBytes ( VV6__data_3c5818c8:Bytes ) +Int 1 , 31 -Int lengthBytes ( VV6__data_3c5818c8:Bytes ) ) ) +Int -32 )
                   => .Bytes

    claim [range-25]: #range ( #range ( ( b"\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x80\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00E\xb5`x" +Bytes #buf ( 32 , VV5__txOrigin_3c5818c8:Int ) ) +Bytes #buf ( 32 , VV5__txOrigin_3c5818c8:Int ) , 100 , 64 ) , 0 , 32 )
                   => #buf ( 32 , VV5__txOrigin_3c5818c8:Int )

    claim [range-26]: #range ( ( b"\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x80\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00E\xb5`x" +Bytes #buf ( 32 , VV5__txOrigin_3c5818c8 ) ) +Bytes #buf ( 32 , VV5__txOrigin_3c5818c8 ) , 100 , 64 )
                   => #buf ( 32 , VV5__txOrigin_3c5818c8 ) +Bytes #buf ( 32 , VV5__txOrigin_3c5818c8 )

    claim [range-27]: #range(b"\x01\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00", lengthBytes ( VV6__data_3c5818c8:Bytes ) +Int 1, 31 -Int lengthBytes ( VV6__data_3c5818c8:Bytes ) )
                   => .Bytes
      requires 119 <Int lengthBytes(VV6__data_3c5818c8)

    claim [range-28]: #range ( b"\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00", 151 -Int lengthBytes ( VV6__data_3c5818c8:Bytes ), lengthBytes ( VV6__data_3c5818c8:Bytes ) +Int lengthBytes ( #range ( b"\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00", 119 -Int lengthBytes ( VV6__data_3c5818c8:Bytes ), lengthBytes ( VV6__data_3c5818c8:Bytes ) +Int lengthBytes ( #range ( b"\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00", 87 -Int lengthBytes ( VV6__data_3c5818c8:Bytes ), lengthBytes ( VV6__data_3c5818c8:Bytes ) +Int -55 ) ) +Int -87 ) ) +Int -119 )
                   => #range ( b"\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00", 151 -Int lengthBytes ( VV6__data_3c5818c8 ), lengthBytes ( VV6__data_3c5818c8 ) +Int -119 )
      requires 0 <=Int VV1__value_3c5818c8
       andBool VV1__value_3c5818c8:Int <Int pow256
       andBool 0 <=Int VV2__gasLimit_3c5818c8
       andBool VV2__gasLimit_3c5818c8 <Int pow64
       andBool 119 <Int lengthBytes(VV6__data_3c5818c8)

    claim [range-29]: #range ( #range ( ( ( b"\xc8\x8a^m\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x01H" +Bytes #buf ( 32 , VV0_value_3c5818c8 ) ) ) , 4 , 64 ) , 32 , 32 )
                   => #buf ( 32 , VV0_value_3c5818c8 )

    claim [range-30]: #range ( b"\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x80\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00E\xb5`x\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00"
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
                   => VV6__data_3c5818c8
      requires lengthBytes(VV6__data_3c5818c8:Bytes) <Int pow255

    claim [range-31]:#range(X, S1, 32) +Bytes #range( X [ S := Y ], S:Int, Z:Int ) => #range(X, S2 +Int 5, 32) +Bytes Y
      requires lengthBytes(Y) +Int 20 ==Int Z +Int 20
       andBool S1 +Int 1 ==Int S2 +Int 6
       andBool 0 <Int lengthBytes(Y)
       andBool 0 <=Int S1 andBool 0 <=Int S

    claim [range-32]: #range ( #range ( #range ( ( ( ( b"\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x80\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\xe9\xe0\\B\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00" +Bytes _ ) +Bytes _ ) +Bytes _ ) +Bytes _ , 128 , ( notMaxUInt5 &Int lengthBytes ( X ) +Int 31 ) +Int 196 ), 0, 32 ), 0, 4 )
                   => b"\xe9\xe0\\B"
      requires 0 <=Int VV1__value_3c5818c8
       andBool VV1__value_3c5818c8:Int <Int pow256
       andBool lengthBytes(X:Bytes) <Int pow255

    claim [range-33]:       #asWord ( #range ( #range ( ( ( ( b"\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x80\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\xe9\xe0\\B\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00" +Bytes #buf ( 32 , VV1__value_3c5818c8:Int ) ) +Bytes #buf ( 32 , VV2__gasLimit_3c5818c8:Int ) +Bytes b"\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x01\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\xa0" ) +Bytes #buf ( 32 , lengthBytes ( VV6__data_3c5818c8:Bytes ) ) ) +Bytes VV6__data_3c5818c8:Bytes +Bytes b"\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00" , 128 , ( notMaxUInt5 &Int lengthBytes ( VV6__data_3c5818c8:Bytes ) +Int 31 ) +Int 196 ), 4, 32 ) )
                      ==Int maxUInt160 &Int #asWord ( #range ( #range ( ( ( ( b"\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x80\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\xe9\xe0\\B\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00" +Bytes #buf ( 32 , VV1__value_3c5818c8:Int ) ) +Bytes #buf ( 32 , VV2__gasLimit_3c5818c8:Int ) +Bytes b"\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x01\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\xa0" ) +Bytes #buf ( 32 , lengthBytes ( VV6__data_3c5818c8:Bytes ) ) ) +Bytes VV6__data_3c5818c8:Bytes +Bytes b"\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00" , 128 , ( notMaxUInt5 &Int lengthBytes ( VV6__data_3c5818c8:Bytes ) +Int 31 ) +Int 196 ), 4, 32 ) )
                   => true
      requires 0 <=Int VV1__value_3c5818c8
       andBool VV1__value_3c5818c8:Int <Int pow256
       andBool 0 <=Int VV2__gasLimit_3c5818c8
       andBool VV2__gasLimit_3c5818c8 <Int pow64
       andBool lengthBytes(VV6__data_3c5818c8:Bytes) <Int pow255

    claim [range-34]: #range ( ( ( ( b"\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x80\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\xe9\xe0\\B\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00" +Bytes #buf ( 32 , VV1__value_3c5818c8:Int ) ) +Bytes #buf ( 32 , VV2__gasLimit_3c5818c8:Int ) +Bytes b"\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x01\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\xa0" ) +Bytes #buf ( 32 , lengthBytes ( VV6__data_3c5818c8:Bytes ) ) ) +Bytes VV6__data_3c5818c8:Bytes +Bytes b"\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00" , 128 , ( notMaxUInt5 &Int lengthBytes ( VV6__data_3c5818c8:Bytes ) +Int 31 ) +Int 196 )
                   => b"\xe9\xe0\\B\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00" +Bytes #buf ( 32 , VV1__value_3c5818c8 ) +Bytes ( #buf ( 32 , VV2__gasLimit_3c5818c8 ) +Bytes b"\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x01\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\xa0" ) +Bytes #buf ( 32 , lengthBytes ( VV6__data_3c5818c8 ) ) +Bytes VV6__data_3c5818c8 +Bytes #range ( b"\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00" , 0 , ( notMaxUInt5 &Int lengthBytes ( VV6__data_3c5818c8 ) +Int 31 ) -Int lengthBytes ( VV6__data_3c5818c8 ) )
      requires 0 <=Int VV1__value_3c5818c8
       andBool VV1__value_3c5818c8:Int <Int pow256
       andBool 0 <=Int VV2__gasLimit_3c5818c8
       andBool VV2__gasLimit_3c5818c8 <Int pow64
       andBool lengthBytes(VV6__data_3c5818c8:Bytes) <Int pow255

    claim [range-35]: #range ( #range ( ( ( ( b"\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x80\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00" +Bytes #buf ( 32 , _ ) ) +Bytes ( #range ( #buf ( 32 , _ ), 0, 8 ) ) +Bytes b"\x01" ) +Bytes ( #range ( #range ( ( ( ( b"\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x80\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\xe9\xe0\\B\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00" +Bytes #buf ( 32 , _ ) ) +Bytes #buf ( 32 , _ ) +Bytes b"\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x01\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\xa0" ) +Bytes #buf ( 32 , lengthBytes ( X ) ) ) +Bytes X +Bytes b"\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00" , 128 , ( notMaxUInt5 &Int lengthBytes ( X ) +Int 31 ) +Int 196 ), 196, lengthBytes ( X ) ) ) +Bytes ( #range ( b"\x01\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00", lengthBytes ( X ) +Int 1, 31 -Int lengthBytes ( X ) ) ) ), 0, lengthBytes ( X ) +Int 233 ) , 64 , 32 )
                   => b"\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x80"
      requires lengthBytes(X:Bytes) <Int pow255

    claim [range-36]: #range(B:Bytes, 5 +Int S2:Int, W:Int) => #range(#range(B, 5, lengthBytes(B) -Int 5), S2, W)
      requires 0 <=Int S2 andBool (5 +Int S2 <=Int lengthBytes(B))
       andBool B ==K #buf(512, 0)

    claim [range-37]: _B1:Bytes [ 1 := _B2:Bytes ] [ -1 := _B3:Bytes ] => .Bytes

    claim [range-38]: #range (#buf(8, X:Int), -3, _:Int) => .Bytes requires 0 <=Int X andBool X <Int pow64

 // #buf simplification
 // -------------------
    claim [bufExtractPadding]: #asWord ( ( #range( #buf ( 32 , X ), 0, 28 ) ):Bytes ) => 0 requires #rangeUInt(32, X)

    claim #buf( 32 , bool2Word ( B:Bool ) ) ==K #buf( 32 , 1 )     => B ==K true
    claim #buf( 32 , I:Int )                ==K #buf( 32 , 1 )     => I ==K 1    requires #rangeUInt(256, I)
    claim #buf( 32 , 1 )                    ==K #buf( 32 , I:Int ) => I ==K 1    requires #rangeUInt(256, I)

    claim #bufStrict( #ceil32(LEN) -Int LEN, 0 ) => #buf( #ceil32(LEN) -Int LEN, 0 ) requires 0 <=Int LEN

    claim [bufstrict-simplify]: #bufStrict(32, #getValue(#int256(X))) => #buf(32, chop(X)) requires #rangeSInt(256, X)

    claim #padToWidth(32, #asByteStack(#hashedLocation("Solidity", 2, OWNER         .IntList))) => #buf(32, #hashedLocation("Solidity", 2, OWNER         .IntList)) requires #rangeUInt(256, OWNER)
    claim #padToWidth(32, #asByteStack(#hashedLocation("Solidity", 2, OWNER SPENDER .IntList))) => #buf(32, #hashedLocation("Solidity", 2, OWNER SPENDER .IntList)) requires #rangeUInt(256, OWNER) andBool #rangeUInt(256, SPENDER)

    claim #buf(32, X +Int Y) +Bytes #buf(lengthBytes(B), 0) +Bytes #buf(32 +Int Y -Int Y, #asWord(B)) => #buf(32, Z -Int Y) +Bytes #buf(32, ((3 *Int Y) -Int (2 *Int Y)) -Int Y) +Bytes B
      requires lengthBytes(B) <=Int 4
       andBool 0 <=Int X andBool 0 <=Int Y andBool Y <=Int Z
       andBool X <Int 256 andBool Y <Int 256 andBool Z <Int 256
       andBool X +Int (2 *Int Y) -Int Z ==Int 0


 // chop simplification
 // -------------------

    claim chop( #lookup(M, KEY)   ) => #lookup(M, KEY)
    claim chop( bool2Word(B:Bool) ) => bool2Word(B)

    claim [chop-range-inferred]: X <Int chop(X *Int Y) /Int 1000000000000000000 => X <Int (X *Int Y) /Int 1000000000000000000
      requires #rangeUInt(256, X) andBool #rangeUInt(256, Y) andBool Y <=Int maxUInt256 /Int X

 // #padToWidth simplification
 // --------------------------

    claim #padToWidth( 32 , #asByteStack( bool2Word ( B:Bool ) ) ) => #buf( 32 , bool2Word ( B ) )
    claim #padToWidth( 32 , #asByteStack( maxUInt160 &Int #newAddr(ACCT, 1) ) ) => #buf(32, #newAddr(ACCT, 1))

    //Required for ERC20 + solc5 + constructor call
    claim 160 ==Int #asWord ( #buf( 4, 160 ) +Bytes ( #range( #buf( 32 , _BUF ), 0, 28 ) ) ) >>Int 224 => true

 // buffer range sinplification
 // ---------------------------
    claim #range((#buf(DATA_LEN, DATA) +Bytes _BUF), 0, DATA_LEN) => #range( #buf(DATA_LEN, DATA), 0, DATA_LEN)
      requires #range(0 <= DATA < (2 ^Int (DATA_LEN *Int 8)))
       andBool 0 <=Int DATA_LEN

 // concatenation simplification
 // ----------------------------

    claim [bytes-reassociation]: ((((A +Bytes B) +Bytes C) +Bytes D) +Bytes E) +Bytes F => A +Bytes (B +Bytes (C +Bytes (D +Bytes (E +Bytes F))))

 // bitwise-and identity
 // --------------------

    claim N &Int maxUInt256 => N requires #rangeUInt(256, N)
    claim maxUInt256 &Int N => N requires #rangeUInt(256, N)
    claim N &Int maxUInt248 => N requires #rangeUInt(248, N)
    claim maxUInt248 &Int N => N requires #rangeUInt(248, N)
    claim N &Int maxUInt240 => N requires #rangeUInt(240, N)
    claim maxUInt240 &Int N => N requires #rangeUInt(240, N)
    claim N &Int maxUInt232 => N requires #rangeUInt(232, N)
    claim maxUInt232 &Int N => N requires #rangeUInt(232, N)
    claim N &Int maxUInt224 => N requires #rangeUInt(224, N)
    claim maxUInt224 &Int N => N requires #rangeUInt(224, N)
    claim N &Int maxUInt216 => N requires #rangeUInt(216, N)
    claim maxUInt216 &Int N => N requires #rangeUInt(216, N)
    claim N &Int maxUInt208 => N requires #rangeUInt(208, N)
    claim maxUInt208 &Int N => N requires #rangeUInt(208, N)
    claim N &Int maxUInt200 => N requires #rangeUInt(200, N)
    claim maxUInt200 &Int N => N requires #rangeUInt(200, N)
    claim N &Int maxUInt192 => N requires #rangeUInt(192, N)
    claim maxUInt192 &Int N => N requires #rangeUInt(192, N)
    claim N &Int maxUInt184 => N requires #rangeUInt(184, N)
    claim maxUInt184 &Int N => N requires #rangeUInt(184, N)
    claim N &Int maxUInt176 => N requires #rangeUInt(176, N)
    claim maxUInt176 &Int N => N requires #rangeUInt(176, N)
    claim N &Int maxUInt168 => N requires #rangeUInt(168, N)
    claim maxUInt168 &Int N => N requires #rangeUInt(168, N)
    claim N &Int maxUInt160 => N requires #rangeUInt(160, N)
    claim maxUInt160 &Int N => N requires #rangeUInt(160, N)
    claim N &Int maxUInt152 => N requires #rangeUInt(152, N)
    claim maxUInt152 &Int N => N requires #rangeUInt(152, N)
    claim N &Int maxUInt144 => N requires #rangeUInt(144, N)
    claim maxUInt144 &Int N => N requires #rangeUInt(144, N)
    claim N &Int maxUInt136 => N requires #rangeUInt(136, N)
    claim maxUInt136 &Int N => N requires #rangeUInt(136, N)
    claim N &Int maxUInt128 => N requires #rangeUInt(128, N)
    claim maxUInt128 &Int N => N requires #rangeUInt(128, N)
    claim N &Int maxUInt120 => N requires #rangeUInt(120, N)
    claim maxUInt120 &Int N => N requires #rangeUInt(120, N)
    claim N &Int maxUInt112 => N requires #rangeUInt(112, N)
    claim maxUInt112 &Int N => N requires #rangeUInt(112, N)
    claim N &Int maxUInt104 => N requires #rangeUInt(104, N)
    claim maxUInt104 &Int N => N requires #rangeUInt(104, N)
    claim N &Int maxUInt96  => N requires #rangeUInt(96,  N)
    claim maxUInt96 &Int N  => N requires #rangeUInt(96,  N)
    claim N &Int maxUInt88  => N requires #rangeUInt(88,  N)
    claim maxUInt88 &Int N  => N requires #rangeUInt(88,  N)
    claim N &Int maxUInt80  => N requires #rangeUInt(80,  N)
    claim maxUInt80 &Int N  => N requires #rangeUInt(80,  N)
    claim N &Int maxUInt72  => N requires #rangeUInt(72,  N)
    claim maxUInt72 &Int N  => N requires #rangeUInt(72,  N)
    claim N &Int maxUInt64  => N requires #rangeUInt(64,  N)
    claim maxUInt64 &Int N  => N requires #rangeUInt(64,  N)
    claim N &Int maxUInt56  => N requires #rangeUInt(56,  N)
    claim maxUInt56 &Int N  => N requires #rangeUInt(56,  N)
    claim N &Int maxUInt48  => N requires #rangeUInt(48,  N)
    claim maxUInt48 &Int N  => N requires #rangeUInt(48,  N)
    claim N &Int maxUInt40  => N requires #rangeUInt(40,  N)
    claim maxUInt40 &Int N  => N requires #rangeUInt(40,  N)
    claim N &Int maxUInt32  => N requires #rangeUInt(32,  N)
    claim maxUInt32 &Int N  => N requires #rangeUInt(32,  N)
    claim N &Int maxUInt24  => N requires #rangeUInt(24,  N)
    claim maxUInt24 &Int N  => N requires #rangeUInt(24,  N)
    claim N &Int maxUInt16  => N requires #rangeUInt(16,  N)
    claim maxUInt16 &Int N  => N requires #rangeUInt(16,  N)
    claim N &Int maxUInt8   => N requires #rangeUInt(8,   N)
    claim maxUInt8 &Int N   => N requires #rangeUInt(8,   N)

 // ecrecover
 // ---------

    claim [ecrec-length]: lengthBytes ( #ecrec ( _ , _ , _ , _ ) ) <=Int 32 => true

    claim [ecrec-split]: #range ( #buf(160, 0) +Bytes _BUF , lengthBytes ( #ecrec ( HASH , SIGV , SIGR , SIGS ) ) +Int 128 , 32 -Int lengthBytes ( #ecrec ( HASH , SIGV , SIGR , SIGS ) ) )
                      => #range ( #buf( 32, 0)             , lengthBytes ( #ecrec ( HASH , SIGV , SIGR , SIGS ) )          , 32 -Int lengthBytes ( #ecrec ( HASH , SIGV , SIGR , SIGS ) ) )

    claim [ecrec-range]: #rangeUInt ( 160 , #asWord ( #ecrec ( _ , _ , _ , _ ) ) )
                      => true

    claim [ecrec-mask]: #asWord ( #ecrec ( HASH , SIGV , SIGR , SIGS ) ) &Int maxUInt160
                     => #asWord ( #ecrec ( HASH , SIGV , SIGR , SIGS ) )

 // Address computation
 // -------------------

    claim [addr-from-private-key]: #addrFromPrivateKey(#unparseDataBytes(b"\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x01"))
                                => 721457446580647751014191829380889690493307935711

endmodule
