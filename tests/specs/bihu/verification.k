requires "edsl.md"
requires "lemmas/lemmas.k"

module VERIFICATION
    imports EDSL
    imports LEMMAS
    imports VERIFICATION-JAVA
    imports VERIFICATION-HASKELL

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

    rule 0 <=Int X /Int Y             => true requires 0 <=Int X andBool X <Int pow256 andBool 0 <Int  Y andBool Y <Int pow256 [simplification]
    rule         X /Int Y <Int pow256 => true requires 0 <=Int X andBool X <Int pow256 andBool 0 <Int  Y andBool Y <Int pow256 [simplification]

    rule chop(I1 -Int I2) => I1 -Int I2 requires #rangeUInt(256, I1) andBool #rangeUInt(256, I2) andBool I2 <=Int I1 [simplification]

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


    syntax Int ::= "@remainingTokens" "(" Int "," Int "," Int ")"    [macro]
                 | "@canExtractThisYear" "(" Int "," Int "," Int ")" [macro]
 // ------------------------------------------------------------------------
    rule @remainingTokens(TOTAL, NOW, START) => #roundpower(TOTAL, 90, 100, (NOW -Int START) /Int 31536000)
    rule @canExtractThisYear(TOTAL, NOW, START) => ((#roundpower(TOTAL, 90, 100, (NOW -Int START) /Int 31536000) *Int 10 /Int 100) *Int ((NOW -Int START) modInt 31536000)) /Int 31536000

  // ###############################
  // #accumulatedReleasedTokens
  // ###############################

    syntax Int ::= "#accumulatedReleasedTokens" "(" Int "," Int "," Int "," Int ")"  [function, no-evaluators]
 // ----------------------------------------------------------------------------------------------------------
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

module VERIFICATION-HASKELL [symbolic, kore]
    imports EVM

    rule X <Int Csstore(SCHED, _, _, _) => false
      requires Gsload       < SCHED > <=Int X
       andBool Gsstoreset   < SCHED > <=Int X
       andBool Gsstorereset < SCHED > <=Int X
      [simplification]

    rule Csstore(SCHED, _, _, _) <=Int X => true
      requires Gsload       < SCHED > <=Int X
       andBool Gsstoreset   < SCHED > <=Int X
       andBool Gsstorereset < SCHED > <=Int X
      [simplification]

    rule X -Int Y <Int Z  => X -Int Z <Int Y  [concrete(X, Z), symbolic(Y), simplification]
    rule X <=Int Y -Int Z => Z <=Int Y -Int X [concrete(X, Y), symbolic(Z), simplification]

endmodule

module VERIFICATION-JAVA [symbolic, kast]
    imports EVM

 // Csstore rule

    rule Csstore(SCHED, NEW, CURR, ORIG)
      => #if CURR ==Int NEW orBool ORIG =/=Int CURR
           #then Gsload < SCHED >
           #else #if ORIG ==Int 0
                   #then Gsstoreset < SCHED >
                   #else Gsstorereset < SCHED >
                 #fi
         #fi
      requires Ghasdirtysstore << SCHED >>
      [simplification]

    rule Csstore(SCHED, NEW, CURR, _ORIG)
      => #if CURR ==Int 0 andBool NEW =/=Int 0
           #then Gsstoreset < SCHED >
           #else Gsstorereset < SCHED >
         #fi
      requires notBool Ghasdirtysstore << SCHED >>
      [simplification]

endmodule
