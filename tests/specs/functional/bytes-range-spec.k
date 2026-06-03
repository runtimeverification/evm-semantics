requires "verification.k"

module BYTES-RANGE-SPEC
    imports VERIFICATION

 // sizeBytes
 // -------------

    claim <k> runLemma(lengthBytes(#padToWidth(32, #asByteStack(#hashedLocation("Solidity", 2, OWNER .IntList))))) => doneLemma(32) ... </k> requires #rangeUInt(256, OWNER)

    claim <k> runLemma(lengthBytes(#buf(X, 0) +Bytes #padRightToWidth(Y:Int, B:Bytes))) => doneLemma( X +Int Y ) ... </k>
      requires lengthBytes(B) <Int X andBool lengthBytes(B) <Int Y

 // Memory update simplifications
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

    claim [memUpdate-past-end]: <k> runLemma  ( #buf(160, A) [ 160 := #buf(32, B) ] [ 192 := #buf(32, C) ] [ 224 := #buf(32, D) ] [ 256 := #buf(32, E) ] )
                                 => doneLemma ( #buf(160, A) +Bytes #buf(32, B) +Bytes #buf(32, C) +Bytes #buf(32, D) +Bytes #buf(32, E) ) ... </k>

    claim [memUpdate-pinpoint]: <k> runLemma  ( ( B1 +Bytes B2 +Bytes B3 +Bytes B4 ) [ 70 := #buf(16, X:Int) ] )
                                 => doneLemma ( ( B1 +Bytes B2 +Bytes ( B3 [ 10 := #buf(16, X:Int) ] ) +Bytes B4 ) ) ... </k>
                                    requires lengthBytes(B1) ==Int 20
                                     andBool lengthBytes(B2) ==Int 40
                                     andBool lengthBytes(B3) ==Int 60

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

    claim [range-39]:
      <k> runLemma( b"\xaa" ==K #range ( ( BYTES:Bytes +Bytes b"\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00" ) [ ( lengthBytes ( BYTES:Bytes ) /Int 2 ) := b"\xaa" ] , ( lengthBytes ( BYTES:Bytes ) /Int 2 ) , 1 ) )
            => doneLemma(true) ... </k>
      requires lengthBytes ( BYTES:Bytes ) <Int 32

 // buffer range simplification
 // ---------------------------
    claim <k> runLemma  ( #range((#buf(DATA_LEN, DATA) +Bytes _BUF), 0, DATA_LEN) )
           => doneLemma ( #range( #buf(DATA_LEN, DATA)             , 0, DATA_LEN) ) ... </k>
      requires #range(0 <= DATA < (2 ^Int (DATA_LEN *Int 8)))
       andBool 0 <=Int DATA_LEN

endmodule
