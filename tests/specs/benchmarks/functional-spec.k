requires "verification.k"

module FUNCTIONAL-SPEC-SYNTAX
    imports VERIFICATION

    syntax KItem ::= runLemma ( Step ) | doneLemma ( Step )
 // -------------------------------------------------------
    rule <k> runLemma(S) => doneLemma(S) ... </k>

    syntax Step ::= Bytes | Int | Bool
 // ----------------------------------

endmodule

module FUNCTIONAL-SPEC
    imports FUNCTIONAL-SPEC-SYNTAX

    claim <k> runLemma (#range (_B [ 128 := #ecrec ( #buf ( 32 , HASH ) , #buf ( 32 , SIGV ) , #buf ( 32 , SIGR ) , #buf ( 32 , SIGS ) ) ] [ 160 := #buf ( 32 , HASH ) ] [ 192 := #buf ( 32 , SIGV ) ] [ 224 := #buf ( 32 , SIGR ) ] [ 256 := #buf ( 32 , SIGS ) ] [ 160 := #padToWidth ( 32 , #asByteStack ( #asWord ( #ecrec ( #buf ( 32 , HASH ) , #buf ( 32 , SIGV ) , #buf ( 32 , SIGR ) , #buf ( 32 , SIGS ) ) ) ) ) ] , 160 , 32 )) => doneLemma (#buf(32, RECOVERED)) ... </k>
      requires notBool #ecrecEmpty(#bufStrict(32, HASH), #bufStrict(32, SIGV), #bufStrict(32, SIGR), #bufStrict(32, SIGS))
       andBool RECOVERED ==Int #asWord(#ecrec(#bufStrict(32, HASH), #bufStrict(32, SIGV), #bufStrict(32, SIGR), #bufStrict(32, SIGS)))
       andBool #rangeUInt(256, HASH)
       andBool #rangeUInt(8, SIGV)
       andBool #rangeBytes(32, SIGR)
       andBool #rangeBytes(32, SIGS)

    claim <k> runLemma ( lengthBytes ( #ecrec ( #buf ( 32 , HASH ) , #buf ( 32 , 255 &Int SIGV ) , #buf ( 32 , SIGR ) , #buf ( 32 , SIGS ) ) ) ) => doneLemma ( 0 ) ... </k>
      requires #rangeUInt(256, HASH)
       andBool #rangeUInt(8, SIGV)
       andBool #rangeBytes(32, SIGR)
       andBool #rangeBytes(32, SIGS)
       andBool #ecrecEmpty ( #buf ( 32 , HASH ) , #buf ( 32 , SIGV ) , #buf ( 32 , SIGR ) , #buf ( 32 , SIGS ) )

    claim <k> runLemma(#encodeArgs(#bytes32(keccak(1 : #encodeArgs(#uint256(A0)))))) => doneLemma(#buf(32, keccak(#buf(1,1) +Bytes #buf(32, A0)))) ... </k> requires #rangeUInt(256, A0)

    claim <k> runLemma(#buf(32, maxUInt256 &Int keccak(#buf(32, maxUInt256 &Int A0) +Bytes #buf(32, maxUInt256 &Int A1))))
           => doneLemma(#buf(32, keccak(#buf(32,A0) +Bytes #buf(32,A1)))) ... </k>
      requires #rangeUInt(256, A0)
       andBool #rangeUInt(256, A1)

    claim <k> runLemma(       chop( #ceil32(DATA_LEN) +Int 64 )          ) => doneLemma ( #ceil32(DATA_LEN) +Int 64 ) ... </k> requires #range(0 <= DATA_LEN < pow16)
    claim <k> runLemma( chop( chop( #ceil32(DATA_LEN) +Int 64 ) +Int 4 ) ) => doneLemma ( #ceil32(DATA_LEN) +Int 68 ) ... </k> requires #range(0 <= DATA_LEN < pow16)

    claim <k> runLemma(#ceil32(DATA_LEN) +Int 292 <Int DATA_LEN +Int 292) => doneLemma(false) ... </k> requires #range(0 <= DATA_LEN < pow16)

    claim <k> runLemma(#buf(4, 0) +Bytes (#buf(32, 6) +Bytes BA:Bytes)) => doneLemma(#buf(36, 6) +Bytes BA:Bytes) ... </k>

    claim <k> runLemma(#range( (112 : 190 : 104 : 75 : (#buf(32, A0) +Bytes #buf(32, A1))), 0, 32)) => doneLemma(112 : 190 : 104 : 75 : (#range(#buf(32, A0), 0, 28))) ... </k> requires #rangeUInt(256, A0) andBool #rangeUInt(256, A1)
    claim <k> runLemma(#range( (112 : 190 : 104 : 75 : (#buf(32, A0) +Bytes #buf(32, A1))), 0, 4))  => doneLemma(112 : 190 : 104 : 75 : .Bytes)               ... </k> requires #rangeUInt(256, A0) andBool #rangeUInt(256, A1)

    claim <k> runLemma(#asWord(112 : 190 : 104 : 74 : #buf(28, A0)) /Int pow224) => doneLemma(1891526730) ... </k> requires #rangeUInt(224, A0)

    claim <k> runLemma( minInt(32, lengthBytes(#ecrec(#bufStrict(32, HASH), #bufStrict(1, SIGV), #bufStrict(32, SIGR), #bufStrict(32, SIGS))))) => doneLemma(32) ... </k>
      requires #rangeUInt(256, HASH)
       andBool #rangeUInt(8, SIGV)
       andBool #rangeBytes(32, SIGR)
       andBool #rangeBytes(32, SIGS)
       andBool notBool #ecrecEmpty(#bufStrict(32, HASH), #bufStrict(1, SIGV), #bufStrict(32, SIGR), #bufStrict(32, SIGS))

    claim <k> runLemma( #range( _:Bytes [ 128 := #ecrec(#bufStrict(32, HASH), #bufStrict(1, SIGV), #bufStrict(32, SIGR), #bufStrict(32, SIGS)) ], 128, 32))
           => doneLemma(#ecrec(#buf(32, HASH), #buf(1, SIGV), #buf(32, SIGR), #buf(32, SIGS))) ... </k>
      requires #rangeUInt(256, HASH)
       andBool #rangeUInt(8, SIGV)
       andBool #rangeBytes(32, SIGR)
       andBool #rangeBytes(32, SIGS)
       andBool notBool #ecrecEmpty(#bufStrict(32, HASH), #bufStrict(1, SIGV), #bufStrict(32, SIGR), #bufStrict(32, SIGS))

    claim <k> runLemma(lengthBytes(#ecrec(#bufStrict(32, HASH), #bufStrict(32, SIGV), #bufStrict(32, SIGR), #bufStrict(32, SIGS)))) => doneLemma(0) ... </k>
      requires #rangeUInt(256, HASH)
       andBool #rangeUInt(8, SIGV)
       andBool #rangeBytes(32, SIGR)
       andBool #rangeBytes(32, SIGS)
       andBool #ecrecEmpty(#bufStrict(32, HASH), #bufStrict(32, SIGV), #bufStrict(32, SIGR), #bufStrict(32, SIGS))

    claim <k> runLemma(lengthBytes(#ecrec(#bufStrict(32, HASH), #bufStrict(32, SIGV), #bufStrict(32, SIGR), #bufStrict(32, SIGS)))) => doneLemma(32) ... </k>
      requires #rangeUInt(256, HASH)
       andBool #rangeUInt(8, SIGV)
       andBool #rangeBytes(32, SIGR)
       andBool #rangeBytes(32, SIGS)
       andBool notBool #ecrecEmpty(#bufStrict(32, HASH), #bufStrict(32, SIGV), #bufStrict(32, SIGR), #bufStrict(32, SIGS))


    claim <k> runLemma(0 <Int (maxUInt160 &Int #asWord(#ecrec(#bufStrict(32, HASH), #bufStrict(32, SIGV), #bufStrict(32, SIGR), #bufStrict(32, SIGS))))) => doneLemma(true) ... </k>
      requires #rangeUInt(256, HASH)
       andBool #rangeUInt(8, SIGV)
       andBool #rangeBytes(32, SIGR)
       andBool #rangeBytes(32, SIGS)
       andBool notBool #ecrecEmpty(#bufStrict(32, HASH), #bufStrict(32, SIGV), #bufStrict(32, SIGR), #bufStrict(32, SIGS))

    claim <k> runLemma(maxUInt160 &Int #asWord(#ecrec(#bufStrict(32, HASH), #bufStrict(32, SIGV), #bufStrict(32, SIGR), #bufStrict(32, SIGS)))) => doneLemma(#asWord(#ecrec(#bufStrict(32, HASH), #bufStrict(32, SIGV), #bufStrict(32, SIGR), #bufStrict(32, SIGS)))) ... </k>
      requires #rangeUInt(256, HASH)
       andBool #rangeUInt(8, SIGV)
       andBool #rangeBytes(32, SIGR)
       andBool #rangeBytes(32, SIGS)
       andBool notBool #ecrecEmpty(#bufStrict(32, HASH), #bufStrict(32, SIGV), #bufStrict(32, SIGR), #bufStrict(32, SIGS))

    claim <k> runLemma(#range( .Bytes [ 0 := #bufStrict(0, 0) ], 0, 1))
           => doneLemma(#buf(1, 0)) ... </k>

    claim <k> runLemma(#range( .Bytes [ 0 := #bufStrict(2, 0) ], 0, 1))
           => doneLemma(#buf(1, 0)) ... </k>

    claim <k> runLemma(#range( .Bytes [ 0 := #bufStrict(10, 0) ], 5, 1))
           => doneLemma(#buf(1, 0)) ... </k>

    claim <k> runLemma(#range( .Bytes [ 0 := #bufStrict(5, 0) ], 0, 3))
           => doneLemma(#buf(3, 0)) ... </k>

    claim <k> runLemma(#range( .Bytes [ 0 := #bufStrict(100, 0) ] [ 10 := #bufStrict(N, 0) ], 10, 5 )) =>
              doneLemma(#range(#bufStrict(N, 0), 10 -Int 10, minInt(5, lengthBytes(#bufStrict(N, 0)) -Int (10 -Int 10)) ) +Bytes #range( .Bytes [ 0 := #bufStrict(100, 0) ], 10 +Int lengthBytes(#bufStrict(N, 0)), 5 -Int minInt(5, lengthBytes(#bufStrict(N, 0)) -Int (10 -Int 10))))
         </k>
      requires N >=Int 0
       andBool N <=Int 5

    claim <k> runLemma(#range( .Bytes [0 := #bufStrict(100, 0) ] [ 10 := #bufStrict(N, 0) ], 13, 5 )) =>
              doneLemma(#range(#bufStrict(N, 0), 13 -Int 10, minInt(5, lengthBytes(#bufStrict(N, 0)) -Int (13 -Int 10)) ) +Bytes #range( .Bytes [ 0 := #bufStrict(100, 0) ], 10 +Int lengthBytes(#bufStrict(N, 0)), 5 -Int minInt(5, lengthBytes(#bufStrict(N, 0)) -Int (13 -Int 10))))
          </k>
      requires N >=Int 5
       andBool N <=Int 10

endmodule
