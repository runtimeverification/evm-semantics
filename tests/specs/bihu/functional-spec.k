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
    claim <k>  runLemma( #range(_MEM [ 96 := #padToWidth(32, #asByteStack(BS)) ], 96, 32) )
           => doneLemma( #buf(32, BS) ) ... </k>
      requires #rangeUInt(256, BS)

    claim <k> runLemma( chop((((((((RPOWER *Int 10) /Int 100) *Int ((NOW -Int START) modInt 31536000)) /Int 31536000) +Int  COLLECTED) +Int BAL) -Int RPOWER)))
           => doneLemma(       (((((RPOWER *Int 10) /Int 100) *Int ((NOW -Int START) modInt 31536000)) /Int 31536000) +Int ((COLLECTED +Int BAL) -Int RPOWER))) ... </k>
      requires #rangeUInt(256, NOW)
       andBool #rangeUInt(256, COLLECTED)
       andBool #rangeUInt(256, BAL)
       andBool 0 <=Int (COLLECTED +Int BAL) andBool (COLLECTED +Int BAL) *Int 3153600 <Int pow256
       andBool 0 <Int (NOW -Int START) andBool (NOW -Int START) <Int pow256
       andBool COLLECT +Int 3 <Int #accumulatedReleasedTokens(BAL, COLLECTED, START, NOW)
       andBool #accumulatedReleasedTokens(BAL, COLLECTED, START, NOW) <Int (BAL +Int COLLECTED) +Int -10
       andBool (COLLECTED +Int BAL) *Int 90 <Int pow256
       andBool 0 <=Int (NOW -Int START) modInt 31536000
       andBool RPOWER ==Int #roundpower(COLLECTED +Int BAL, 90, 100, (NOW -Int START) /Int 31536000)

    claim <k>  runLemma( chop(((RPOWER *Int 10 /Int 100) *Int (((NOW:Int -Int START:Int) modInt 31536000) /Int 31536000)) +Int COLLECTED:Int +Int BAL:Int -Int RPOWER) )
           => doneLemma(      ((RPOWER *Int 10 /Int 100) *Int (((NOW:Int -Int START:Int) modInt 31536000) /Int 31536000)) +Int COLLECTED:Int +Int BAL:Int -Int RPOWER  ) ... </k>
      requires #rangeUInt(256, NOW) andBool #rangeUInt(256, START) andBool #rangeUInt(256, (NOW -Int START)) andBool 0 <Int (NOW -Int START)
       andBool #rangeUInt(256, COLLECTED) andBool #rangeUInt(256, BAL) andBool #rangeUInt(256, (COLLECTED +Int BAL) *Int 3153600)
       andBool RPOWER ==Int #roundpower(COLLECTED:Int +Int BAL:Int, 90, 100, (NOW:Int -Int START:Int) /Int 31536000)
       // canExtract >= 0
       andBool #accumulatedReleasedTokens(BAL, COLLECTED, START, NOW) >Int COLLECTED +Int 3
       // canExtract > balance
       andBool #accumulatedReleasedTokens(BAL, COLLECTED, START, NOW) <Int (BAL +Int COLLECTED) -Int 10

endmodule
