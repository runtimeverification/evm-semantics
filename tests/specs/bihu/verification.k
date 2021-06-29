requires "abstract-semantics-direct-gas.k"
requires "edsl.md"
requires "../lemmas.k"

module VERIFICATION
    imports ABSTRACT-SEMANTICS-DIRECT-GAS
    imports EDSL
    imports LEMMAS

  // ########################
  // Buffer Reasoning
  // ########################

    //semantics of #buf
    rule #buf(LEN, BYTES) => #padToWidth(LEN, #asByteStack( BYTES )) [simplification, concrete]

    //Rules for #padToWidth with non-regular symbolic arguments.
    rule #padToWidth(32, #asByteStack(V)) => #buf(32, V)
      requires 0 <=Int V andBool V <Int pow256
      [simplification]

  // ########################
  // Arithmetic
  // ########################

    rule N -Int N => 0 [simplification]

    rule (I1 *Int I2) /Int I3 <=Int I4 => true
      requires  0  <=Int I1
       andBool  0  <=Int I2
       andBool  0   <Int I3
       andBool  I1 <=Int I4
       andBool  I2 <=Int I3
      [simplification]

    rule 0 <=Int X /Int Y             => true requires 0 <=Int X andBool X <Int pow256 andBool 0 <Int  Y andBool Y <Int pow256 [simplification]
    rule         X /Int Y <Int pow256 => true requires 0 <=Int X andBool X <Int pow256 andBool 0 <Int  Y andBool Y <Int pow256 [simplification]

    rule I1 +Int I2 <Int I1 => false requires 0 <=Int I2 [simplification]

    rule I1 <Int I1 -Int I2 => false requires 0 <=Int I2 [simplification]

    rule chop(I1 -Int I2) => I1 -Int I2 requires 0 <=Int I1 andBool I2 <Int pow256 andBool I1 >=Int I2 [simplification]

    rule chop(I1 +Int (I2 -Int I3)) => I1 +Int (I2 -Int I3)
      requires  0 <=Int I2
       andBool I2  <Int pow256
       andBool  0 <=Int I3
       andBool I1 <=Int I3
       andBool I2 >=Int I3
      [simplification]

  // ########################
  // #roundpower
  // ########################

    syntax Int ::= "#roundpower" "(" Int "," Int "," Int "," Int ")"  [function, smtlib(smt_roundpower)]
 // ----------------------------------------------------------------------------------------------------
    rule #roundpower(0,                           BASEN, BASED, EXPONENT) => 0                                                requires BASEN >Int 0 andBool BASED >=Int BASEN andBool EXPONENT >=Int 0
    rule #roundpower(ACC,                         BASEN, BASED, 0       ) => ACC                                              requires BASEN >Int 0 andBool BASED >=Int BASEN
    rule #roundpower((ACC *Int BASEN) /Int BASED, BASEN, BASED, EXPONENT) => #roundpower(ACC, BASEN, BASED, EXPONENT +Int 1)  requires BASEN >Int 0 andBool BASED >=Int BASEN andBool EXPONENT >=Int 0 [simplification]

    rule 0 <=Int #roundpower(ACC, BASEN, BASED, EXPONENT)              => true  requires ACC >=Int 0 andBool BASEN >Int 0 andBool BASED >=Int BASEN andBool EXPONENT >=Int 0                             [simplification]
    rule         #roundpower(ACC, BASEN, BASED, EXPONENT) <=Int ACC    => true  requires ACC >=Int 0 andBool BASEN >Int 0 andBool BASED >=Int BASEN andBool EXPONENT >=Int 0                             [simplification]
    rule         #roundpower(ACC, BASEN, BASED, EXPONENT)  <Int pow256 => true  requires ACC >=Int 0 andBool BASEN >Int 0 andBool BASED >=Int BASEN andBool EXPONENT >=Int 0 andBool ACC <Int 2 ^Int 256 [simplification]

    rule 0 <=Int (#roundpower(ACC, BASEN, BASED, EXPONENT) *Int 10)             => true  requires  ACC >=Int 0 andBool BASEN >Int 0 andBool BASED >=Int BASEN andBool EXPONENT >=Int 0                                     [simplification]
    rule         (#roundpower(ACC, BASEN, BASED, EXPONENT) *Int 10) <Int pow256 => true  requires  ACC >=Int 0 andBool BASEN >Int 0 andBool BASED >=Int BASEN andBool EXPONENT >=Int 0 andBool ACC *Int 10 <Int 2 ^Int 256 [simplification]

    rule 0 <=Int (#roundpower(ACC, BASEN, BASED, EXPONENT) *Int A /Int B *Int C)            => true  requires  ACC >=Int 0 andBool BASEN >Int 0 andBool BASED >=Int BASEN andBool EXPONENT >=Int 0 andBool A >=Int 0 andBool B >Int 0 andBool C >=Int 0                                                  [simplification]
    rule          #roundpower(ACC, BASEN, BASED, EXPONENT) *Int A /Int B *Int C <Int pow256 => true  requires  ACC >=Int 0 andBool BASEN >Int 0 andBool BASED >=Int BASEN andBool EXPONENT >=Int 0 andBool A >=Int 0 andBool B >Int 0 andBool C >=Int 0 andBool ACC *Int A /Int B *Int C <Int 2 ^Int 256 [simplification]


    syntax Int ::= "@remainingTokens" "(" Int "," Int "," Int ")"
                 | "@canExtractThisYear" "(" Int "," Int "," Int ")"
 // ----------------------------------------------------------------
    rule @remainingTokens(TOTAL, NOW, START) => #roundpower(TOTAL, 90, 100, (NOW -Int START) /Int 31536000)  [macro]
    rule @canExtractThisYear(TOTAL, NOW, START) => ((#roundpower(TOTAL, 90, 100, (NOW -Int START) /Int 31536000) *Int 10 /Int 100) *Int ((NOW -Int START) modInt 31536000)) /Int 31536000  [macro]

  // ###############################
  // #accumulatedReleasedTokens
  // ###############################

    syntax Int ::= "#accumulatedReleasedTokens" "(" Int "," Int "," Int "," Int ")"  [function]
 // -------------------------------------------------------------------------------------------
    // proved manually
    rule COLLECTED <=Int @canExtractThisYear(COLLECTED +Int BAL, NOW, START) +Int ((COLLECTED +Int BAL) -Int @remainingTokens(COLLECTED +Int BAL, NOW, START))                => true  requires #accumulatedReleasedTokens(BAL, COLLECTED, START, NOW) >Int COLLECTED +Int 3 [simplification]
    rule 0         <=Int @canExtractThisYear(COLLECTED +Int BAL, NOW, START) +Int ((COLLECTED +Int BAL) -Int @remainingTokens(COLLECTED +Int BAL, NOW, START))                => true  requires #accumulatedReleasedTokens(BAL, COLLECTED, START, NOW) >Int COLLECTED +Int 3 [simplification]
    rule 0         <=Int @canExtractThisYear(COLLECTED +Int BAL, NOW, START) +Int ((COLLECTED +Int BAL) -Int @remainingTokens(COLLECTED +Int BAL, NOW, START)) -Int COLLECTED => true  requires #accumulatedReleasedTokens(BAL, COLLECTED, START, NOW) >Int COLLECTED +Int 3 [simplification]

    // proved manually (canExtract > balance) --- if condition
    rule BAL        <Int @canExtractThisYear(COLLECTED +Int BAL, NOW, START) +Int ((COLLECTED +Int BAL) -Int @remainingTokens(COLLECTED +Int BAL, NOW, START)) -Int COLLECTED           => false  requires #accumulatedReleasedTokens(BAL, COLLECTED, START, NOW) <Int (BAL +Int COLLECTED) -Int 10 [simplification]
    // proved manually (balance >= canExtract) --- balance = sub(balance, canExtract)
    rule                 @canExtractThisYear(COLLECTED +Int BAL, NOW, START) +Int ((COLLECTED +Int BAL) -Int @remainingTokens(COLLECTED +Int BAL, NOW, START)) -Int COLLECTED <=Int BAL => true   requires #accumulatedReleasedTokens(BAL, COLLECTED, START, NOW) <Int (BAL +Int COLLECTED) -Int 10 [simplification]

    rule                 @canExtractThisYear(COLLECTED +Int BAL, NOW, START) +Int ((COLLECTED +Int BAL) -Int @remainingTokens(COLLECTED +Int BAL, NOW, START)) -Int COLLECTED <Int pow256 => true  requires #accumulatedReleasedTokens(BAL, COLLECTED, START, NOW) >Int COLLECTED +Int 3 [simplification]
    rule                 @canExtractThisYear(COLLECTED +Int BAL, NOW, START) +Int ((COLLECTED +Int BAL) -Int @remainingTokens(COLLECTED +Int BAL, NOW, START)) <Int pow256                => true  requires #accumulatedReleasedTokens(BAL, COLLECTED, START, NOW) >Int COLLECTED +Int 3 [simplification]

endmodule
