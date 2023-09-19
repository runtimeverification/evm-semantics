requires "verification.k"

module FUNCTIONAL-SPEC
    imports VERIFICATION

    claim #range (_B [ 128 := #ecrec ( #buf ( 32 , HASH ) , #buf ( 32 , SIGV ) , #buf ( 32 , SIGR ) , #buf ( 32 , SIGS ) ) ] [ 160 := #buf ( 32 , HASH ) ] [ 192 := #buf ( 32 , SIGV ) ] [ 224 := #buf ( 32 , SIGR ) ] [ 256 := #buf ( 32 , SIGS ) ] [ 160 := #padToWidth ( 32 , #asByteStack ( #asWord ( #ecrec ( #buf ( 32 , HASH ) , #buf ( 32 , SIGV ) , #buf ( 32 , SIGR ) , #buf ( 32 , SIGS ) ) ) ) ) ] , 160 , 32 )
       => #buf(32, RECOVERED)
      requires notBool #ecrecEmpty(#bufStrict(32, HASH), #bufStrict(32, SIGV), #bufStrict(32, SIGR), #bufStrict(32, SIGS))
       andBool RECOVERED ==Int #asWord(#ecrec(#bufStrict(32, HASH), #bufStrict(32, SIGV), #bufStrict(32, SIGR), #bufStrict(32, SIGS)))
       andBool #rangeUInt(256, HASH)
       andBool #rangeUInt(8, SIGV)
       andBool #rangeBytes(32, SIGR)
       andBool #rangeBytes(32, SIGS)

    claim lengthBytes ( #ecrec ( #buf ( 32 , HASH ) , #buf ( 32 , 255 &Int SIGV ) , #buf ( 32 , SIGR ) , #buf ( 32 , SIGS ) ) )
       => 0
      requires #rangeUInt(256, HASH)
       andBool #rangeUInt(8, SIGV)
       andBool #rangeBytes(32, SIGR)
       andBool #rangeBytes(32, SIGS)
       andBool #ecrecEmpty ( #buf ( 32 , HASH ) , #buf ( 32 , SIGV ) , #buf ( 32 , SIGR ) , #buf ( 32 , SIGS ) )

    claim #encodeArgs(#bytes32(keccak(1 : #encodeArgs(#uint256(A0)))))
       => #buf(32, keccak(#buf(1,1) +Bytes #buf(32, A0)))
     requires #rangeUInt(256, A0)

    claim #buf(32, maxUInt256 &Int keccak(#buf(32, maxUInt256 &Int A0) +Bytes #buf(32, maxUInt256 &Int A1)))
       => #buf(32, keccak(#buf(32,A0) +Bytes #buf(32,A1)))
      requires #rangeUInt(256, A0)
       andBool #rangeUInt(256, A1)

    claim       chop( #ceil32(DATA_LEN) +Int 64 )          => #ceil32(DATA_LEN) +Int 64 requires #range(0 <= DATA_LEN < pow16)
    claim chop( chop( #ceil32(DATA_LEN) +Int 64 ) +Int 4 ) => #ceil32(DATA_LEN) +Int 68 requires #range(0 <= DATA_LEN < pow16)

    claim #ceil32(DATA_LEN) +Int 292 <Int DATA_LEN +Int 292 => false requires #range(0 <= DATA_LEN < pow16)

    claim #buf(4, 0) +Bytes (#buf(32, 6) +Bytes BA:Bytes) => #buf(36, 6) +Bytes BA:Bytes

    claim #range( (112 : 190 : 104 : 75 : (#buf(32, A0) +Bytes #buf(32, A1))), 0, 32) => 112 : 190 : 104 : 75 : (#range(#buf(32, A0), 0, 28)) requires #rangeUInt(256, A0) andBool #rangeUInt(256, A1)
    claim #range( (112 : 190 : 104 : 75 : (#buf(32, A0) +Bytes #buf(32, A1))), 0, 4)  => 112 : 190 : 104 : 75 : .Bytes                        requires #rangeUInt(256, A0) andBool #rangeUInt(256, A1)

    claim #asWord(112 : 190 : 104 : 74 : #buf(28, A0)) /Int pow224 => 1891526730 requires #rangeUInt(224, A0)

    claim minInt(32, lengthBytes(#ecrec(#bufStrict(32, HASH), #bufStrict(1, SIGV), #bufStrict(32, SIGR), #bufStrict(32, SIGS)))) => 32
      requires #rangeUInt(256, HASH)
       andBool #rangeUInt(8, SIGV)
       andBool #rangeBytes(32, SIGR)
       andBool #rangeBytes(32, SIGS)
       andBool notBool #ecrecEmpty(#bufStrict(32, HASH), #bufStrict(1, SIGV), #bufStrict(32, SIGR), #bufStrict(32, SIGS))

    claim #range( _:Bytes [ 128 := #ecrec(#bufStrict(32, HASH), #bufStrict(1, SIGV), #bufStrict(32, SIGR), #bufStrict(32, SIGS)) ], 128, 32) => #ecrec(#buf(32, HASH), #buf(1, SIGV), #buf(32, SIGR), #buf(32, SIGS))
      requires #rangeUInt(256, HASH)
       andBool #rangeUInt(8, SIGV)
       andBool #rangeBytes(32, SIGR)
       andBool #rangeBytes(32, SIGS)
       andBool notBool #ecrecEmpty(#bufStrict(32, HASH), #bufStrict(1, SIGV), #bufStrict(32, SIGR), #bufStrict(32, SIGS))

    claim lengthBytes(#ecrec(#bufStrict(32, HASH), #bufStrict(32, SIGV), #bufStrict(32, SIGR), #bufStrict(32, SIGS))) => 0
      requires #rangeUInt(256, HASH)
       andBool #rangeUInt(8, SIGV)
       andBool #rangeBytes(32, SIGR)
       andBool #rangeBytes(32, SIGS)
       andBool #ecrecEmpty(#bufStrict(32, HASH), #bufStrict(32, SIGV), #bufStrict(32, SIGR), #bufStrict(32, SIGS))

    claim lengthBytes(#ecrec(#bufStrict(32, HASH), #bufStrict(32, SIGV), #bufStrict(32, SIGR), #bufStrict(32, SIGS))) => 32
      requires #rangeUInt(256, HASH)
       andBool #rangeUInt(8, SIGV)
       andBool #rangeBytes(32, SIGR)
       andBool #rangeBytes(32, SIGS)
       andBool notBool #ecrecEmpty(#bufStrict(32, HASH), #bufStrict(32, SIGV), #bufStrict(32, SIGR), #bufStrict(32, SIGS))


    claim 0 <Int (maxUInt160 &Int #asWord(#ecrec(#bufStrict(32, HASH), #bufStrict(32, SIGV), #bufStrict(32, SIGR), #bufStrict(32, SIGS)))) => true
      requires #rangeUInt(256, HASH)
       andBool #rangeUInt(8, SIGV)
       andBool #rangeBytes(32, SIGR)
       andBool #rangeBytes(32, SIGS)
       andBool notBool #ecrecEmpty(#bufStrict(32, HASH), #bufStrict(32, SIGV), #bufStrict(32, SIGR), #bufStrict(32, SIGS))

    claim maxUInt160 &Int #asWord(#ecrec(#bufStrict(32, HASH), #bufStrict(32, SIGV), #bufStrict(32, SIGR), #bufStrict(32, SIGS))) => #asWord(#ecrec(#bufStrict(32, HASH), #bufStrict(32, SIGV), #bufStrict(32, SIGR), #bufStrict(32, SIGS)))
      requires #rangeUInt(256, HASH)
       andBool #rangeUInt(8, SIGV)
       andBool #rangeBytes(32, SIGR)
       andBool #rangeBytes(32, SIGS)
       andBool notBool #ecrecEmpty(#bufStrict(32, HASH), #bufStrict(32, SIGV), #bufStrict(32, SIGR), #bufStrict(32, SIGS))

    claim #range( .Bytes [ 0 := #bufStrict(0, 0)  ], 0, 1) => #buf(1, 0)
    claim #range( .Bytes [ 0 := #bufStrict(2, 0)  ], 0, 1) => #buf(1, 0)
    claim #range( .Bytes [ 0 := #bufStrict(10, 0) ], 5, 1) => #buf(1, 0)
    claim #range( .Bytes [ 0 := #bufStrict(5, 0)  ], 0, 3) => #buf(3, 0)

    claim #range( .Bytes [ 0 := #bufStrict(100, 0) ] [ 10 := #bufStrict(N, 0) ], 10, 5 )
       => #range(#bufStrict(N, 0), 10 -Int 10, minInt(5, lengthBytes(#bufStrict(N, 0)) -Int (10 -Int 10)) ) +Bytes #range( .Bytes [ 0 := #bufStrict(100, 0) ], 10 +Int lengthBytes(#bufStrict(N, 0)), 5 -Int minInt(5, lengthBytes(#bufStrict(N, 0)) -Int (10 -Int 10)))
      requires N >=Int 0
       andBool N <=Int 5

    claim #range( .Bytes [0 := #bufStrict(100, 0) ] [ 10 := #bufStrict(N, 0) ], 13, 5 )
       => #range(#bufStrict(N, 0), 13 -Int 10, minInt(5, lengthBytes(#bufStrict(N, 0)) -Int (13 -Int 10)) ) +Bytes #range( .Bytes [ 0 := #bufStrict(100, 0) ], 10 +Int lengthBytes(#bufStrict(N, 0)), 5 -Int minInt(5, lengthBytes(#bufStrict(N, 0)) -Int (13 -Int 10)))
      requires N >=Int 5
       andBool N <=Int 10

endmodule
