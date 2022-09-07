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

   rule <k> runLemma(
      chop (
         chop (
            #roundpower (
               COLLECTED +Int BAL ,
               90 ,
               100 ,
               ( NOW -Int START ) /Int 31536000 ) *Int 10 /Int 100 *Int (
                  ( NOW -Int START ) modInt 31536000
               ) /Int 31536000 +Int COLLECTED +Int BAL -Int #roundpower ( COLLECTED +Int BAL ,
               90 ,
               100 ,
               ( NOW -Int START ) /Int 31536000 )
            ) -Int COLLECTED
         )
      ) => doneLemma(
         chop (
            #roundpower (
               COLLECTED +Int BAL ,
               90 ,
               100 ,
               ( NOW -Int START ) /Int 31536000
            ) /Int 10 *Int (
               ( NOW -Int START ) modInt 31536000
            ) /Int 31536000 +Int COLLECTED +Int BAL -Int #roundpower (
               COLLECTED +Int BAL ,
               90 ,
               100 ,
               ( NOW -Int START ) /Int 31536000
            )
         ) -Int COLLECTED
      ) ... </k>
      <accounts>
          <account>
            <acctID>
              _
            </acctID>
            <storage>
               0 |-> COLLECTED:Int
               1 |-> BAL:Int
               ...
            </storage>
         </account>
      </accounts>
      <timestamp>
         NOW
      </timestamp>
      <callData>
            b"\xb9>,\xdb" ++ #buf ( 32 , NOW ) ++ #buf ( 32 , START )
      </callData>

   requires 0 <=Int COLLECTED +Int BAL
   andBool  0 <=Int COLLECTED
   andBool  COLLECTED <Int pow256
   andBool  #Ceil ( #roundpower ( COLLECTED +Int BAL , 90 , 100 , ( NOW -Int START ) /Int 31536000 ) )
   andBool  #accumulatedReleasedTokens ( BAL , COLLECTED , START , NOW ) <Int BAL +Int COLLECTED +Int -10
   andBool  #accumulatedReleasedTokens ( BAL , COLLECTED , START , NOW ) >Int COLLECTED +Int 3
   andBool  ( COLLECTED +Int BAL ) *Int 90 <Int pow256
   andBool  ( COLLECTED +Int BAL ) *Int 3153600 <Int pow256
   andBool  3650 <=Int GASCAP -Int 293 *Int ( ( NOW -Int START ) /Int 31536000 )
   andBool  ( NOW -Int START ) modInt 31536000 <Int pow256
   andBool  NOW -Int START <Int pow256
   andBool  START <Int pow256
   andBool  293 *Int ( ( NOW -Int START ) /Int 31536000 ) +Int 43000 <=Int GASCAP
   andBool  293 *Int ( ( NOW -Int START ) /Int 31536000 ) +Int 26 <=Int GASCAP +Int -2235
   andBool  0 <Int NOW -Int START
   andBool  0 <=Int START
   andBool  0 <=Int ( NOW -Int START ) modInt 31536000
   andBool  BAL <Int pow256
   andBool  0 <=Int BAL

   // COLLECT ALL SIDE_CONDITIONS FROM ABOVE TERM THAT TALK ABOUT VARIABLES PRESENT IN THIS REWRITE

endmodule
