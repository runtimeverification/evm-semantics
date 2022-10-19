requires "verification.k"

module FUNCTIONAL-SPEC-SYNTAX
    imports VERIFICATION

    syntax KItem ::= runLemma ( Step ) | doneLemma ( Step )
 // -------------------------------------------------------
    rule <k> runLemma(S) => doneLemma(S) ... </k>

    syntax Step ::= ByteArray | Int | Bool
 // --------------------------------------

endmodule

module FUNCTIONAL-SPEC
    imports FUNCTIONAL-SPEC-SYNTAX

    claim <k> runLemma(#range(_MEM [ 96 := #padToWidth(32, #asByteStack(BS)) ], 96, 32))
           => doneLemma(#buf(32, BS)) ... </k>
      requires #rangeUInt(256, BS)

    claim <k> runLemma(chop ( COLLECTED:Int +Int BAL:Int *Int 10 /Int 100 *Int NOW:Int -Int START:Int /Int 31536000 -Int COLLECTED:Int ) <=Int COLLECTED:Int +Int BAL:Int *Int 10 /Int 100 *Int NOW:Int -Int START:Int /Int 31536000) =>
      doneLemma(true) ...</k>
      requires
         #Not ( { 0 #Equals COLLECTED:Int +Int BAL:Int *Int 10 /Int 100 } )
         andBool #Not ( { 0 #Equals COLLECTED:Int +Int BAL:Int } )

         andBool #Not ( { true #Equals NOW:Int -Int START:Int <=Int 0 } )
         andBool #Not ( { true #Equals NOW:Int <=Int START:Int } )

         andBool #Not ( { true #Equals 115792089237316195423570985008687907853269984665640564039457584007913129639936 <=Int COLLECTED:Int +Int BAL:Int *Int 3153600 } )
         andBool #Not ( { true #Equals 115792089237316195423570985008687907853269984665640564039457584007913129639936 <=Int BAL:Int } )
         andBool #Not ( { true #Equals 115792089237316195423570985008687907853269984665640564039457584007913129639936 <=Int COLLECTED:Int } )
         andBool #Not ( { true #Equals 115792089237316195423570985008687907853269984665640564039457584007913129639936 <=Int NOW:Int } )
         andBool #Not ( { true #Equals 115792089237316195423570985008687907853269984665640564039457584007913129639936 <=Int NOW:Int -Int START:Int } )
         andBool #Not ( { true #Equals 115792089237316195423570985008687907853269984665640564039457584007913129639936 <=Int START:Int } )

         andBool { true #Equals 0 <=Int BAL:Int }

         andBool { true #Equals 0 <=Int COLLECTED:Int }
         andBool { true #Equals 0 <=Int COLLECTED:Int +Int BAL:Int }
         andBool { true #Equals 0 <=Int NOW:Int }

         andBool { true #Equals 0 <=Int START:Int }
         andBool { true #Equals #accumulatedReleasedTokens ( BAL:Int , COLLECTED:Int , START:Int , NOW:Int ) <Int BAL:Int +Int COLLECTED:Int +Int -10 }
         andBool { true #Equals #accumulatedReleasedTokens ( BAL:Int , COLLECTED:Int , START:Int , NOW:Int ) >Int COLLECTED:Int +Int 3 }
         andBool { true #Equals NOW:Int -Int START:Int /Int 31536000 <=Int 0 }

endmodule
