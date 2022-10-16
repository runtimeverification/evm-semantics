requires "lemmas/lemmas.k"

module VERIFICATION-COMMON
    imports LEMMAS

  // ########################
  // Ecrecover
  // ########################

    //Symbolic predicate representing whether output of #ecrec is empty. No implementation.
    syntax Bool ::= #ecrecEmpty( ByteArray , ByteArray , ByteArray , ByteArray ) [function, no-evaluators, smtlib(ecrecEmpty)]
 // --------------------------------------------------------------------------------------------------------------------------
    rule #sizeByteArray(#ecrec(HASH, SIGV, SIGR, SIGS)) => 32 requires notBool #ecrecEmpty(HASH, SIGV, SIGR, SIGS) [simplification]
    rule #sizeByteArray(#ecrec(HASH, SIGV, SIGR, SIGS)) => 0  requires         #ecrecEmpty(HASH, SIGV, SIGR, SIGS) [simplification]

    rule         #asWord(#ecrec(HASH, SIGV, SIGR, SIGS))                  => 0    requires         #ecrecEmpty(HASH, SIGV, SIGR, SIGS) [simplification]
    rule 0  <Int #asWord(#ecrec(HASH, SIGV, SIGR, SIGS))                  => true requires notBool #ecrecEmpty(HASH, SIGV, SIGR, SIGS) [simplification]
    rule 0 <=Int #asWord(#ecrec(_   , _   , _   , _   ))                  => true                                                      [simplification]
    rule         #asWord(#ecrec(_   , _   , _   , _   )) <=Int maxUInt160 => true                                                      [simplification]

endmodule

module VERIFICATION
    imports VERIFICATION-COMMON
    imports VERIFICATION-JAVA
    imports VERIFICATION-HASKELL
    imports INFINITE-GAS-JAVA-EXTRA

  // ########################
  // Map Reasoning
  // ########################

    rule M:Map [ K1 <- _  ] [ K2 <- V2 ] => M [ K1 <- V2 ]               requires K1 ==Int K2 [simplification]
    rule M:Map [ K1 <- V1 ] [ K2 <- V2 ] => M [ K2 <- V2 ] [ K1 <- V1 ]  requires K2  <Int K1 [simplification]

  // ########################
  // Gas Calculation
  // ########################

    rule Rsstore(_BYZANTIUM, NEW, _CURR, _ORIG) => 0  requires NEW =/=Int 0 [simplification]

  // ########################
  // ABI Encoding
  // ########################

    syntax ByteArray ::= #abiCallData2 ( String , TypedArgs ) [function]

    rule #abiCallData2(FSIG, ARGS)
      => #parseByteStack(substrString(Keccak256(FSIG), 0, 8))
      ++ #encodeArgs(ARGS)

    rule chop(I) => 0 requires I ==Int pow256 [simplification]

  // ########################
  // Memory Usage
  // ########################

    rule #memoryUsageUpdate(#memoryUsageUpdate(MU, START0, WIDTH0), START1, WIDTH1) => #memoryUsageUpdate(MU, START0, WIDTH0) requires START1 +Int WIDTH1 <=Int START0 +Int WIDTH0 andBool 0  <Int WIDTH0 andBool 0 <=Int WIDTH1 [simplification]
    rule #memoryUsageUpdate(#memoryUsageUpdate(MU, START0, WIDTH0), START1, WIDTH1) => #memoryUsageUpdate(MU, START1, WIDTH1) requires START0 +Int WIDTH0  <Int START1 +Int WIDTH1 andBool 0 <=Int WIDTH0 andBool 0  <Int WIDTH1 [simplification]

    rule 0 <=Int #memoryUsageUpdate(_MU, _START, _WIDTH) => true [simplification]

  // ########################
  // Buffer Reasoning
  // ########################

    // ++-identity-right
    rule WS ++ .ByteArray => WS [simplification]

    // ++-associativity
    rule ( WS1 ++ WS2 ) ++ WS3 => WS1 ++ ( WS2 ++ WS3 ) [simplification]

    rule #sizeWordStack(WS, N) <Int SIZE => #sizeWordStack(WS, 0) +Int N <Int SIZE  requires N =/=Int 0 [simplification]

    rule SIZELIMIT <Int #sizeWordStack(WS, N) +Int DELTA  => SIZELIMIT <Int (#sizeWordStack(WS, 0) +Int N) +Int DELTA  requires N =/=Int 0 [simplification]
    rule SIZELIMIT <Int #sizeWordStack(WS, N)             => SIZELIMIT <Int  #sizeWordStack(WS, 0) +Int N              requires N =/=Int 0 [simplification]

    rule #sizeWordStack(WS, N) <=Int SIZE => #sizeWordStack(WS, 0) +Int N <=Int SIZE  requires N =/=Int 0 [simplification]

  // ########################
  // Range
  // ########################

    rule 0 <=Int (_X modInt _Y)         => true                    [simplification]
    rule         (_X modInt  Y) <Int Y  => true  requires Y >Int 0 [simplification]

    rule 0 <=Int 2 ^Int _X             => true                      [simplification]
    rule         2 ^Int  X <Int pow256 => true  requires X <Int 256 [simplification]

    rule 0 <=Int X &Int Y             => true  requires #rangeUInt(256, X) andBool #rangeUInt(256, Y) [simplification]
    rule         X &Int Y <Int pow256 => true  requires #rangeUInt(256, X) andBool #rangeUInt(256, Y) [simplification]

    rule 0 <=Int X |Int Y             => true  requires #rangeUInt(256, X) andBool #rangeUInt(256, Y) [simplification]
    rule         X |Int Y <Int pow256 => true  requires #rangeUInt(256, X) andBool #rangeUInt(256, Y) [simplification]

    rule 0 <=Int #blockhash(_, _, _, _)             => true [simplification]
    rule         #blockhash(_, _, _, _) <Int pow256 => true [simplification]

    rule 0 <=Int X xorInt maxUInt256             => true  requires #rangeUInt(256, X) [simplification]
    rule         X xorInt maxUInt256 <Int pow256 => true  requires #rangeUInt(256, X) [simplification]

  // ########################
  // Simplification
  // ########################

    rule #range(_M [ N := #buf(WIDTH, DATA) ], N, WIDTH) => #buf(WIDTH, DATA) [simplification]

    rule #asWord(WS) &Int maxUInt256 => #asWord(WS) [simplification]

    rule maxUInt256 &Int X => X requires #rangeUInt(256, X) [simplification]

    // 2^256 - 2^160 = 0xff..ff00..00 (96 1's followed by 160 0's)
    rule 115792089237316195423570985007226406215939081747436879206741300988257197096960 &Int ADDR => 0
      requires #rangeAddress(ADDR)
      [simplification]

    rule chop((ADDR &Int maxUInt160) modInt pow160) => ADDR
      requires #rangeAddress(ADDR)
      [simplification]

  // ########################
  // Arithmetic
  // ########################

    rule 2 ^%Int X pow256 => 2 ^Int X  requires 0 <=Int X andBool X <Int 256 [simplification]

    // X &Int (NOT 31)
    rule X &Int 115792089237316195423570985008687907853269984665640564039457584007913129639904 => (X /Int 32) *Int 32  requires 0 <=Int X [simplification]

    rule X +Int Y <Int pow256 => true  requires X <=Int pow16 andBool Y <Int pow16 [simplification]

    rule X <=Int #ceil32(X)     => true   requires 0 <=Int X                       [simplification]
    rule #ceil32(X) <Int X      => false  requires 0 <=Int X                       [simplification]
    rule #ceil32(X) <=Int pow16 => true   requires 0 <=Int X andBool X <=Int pow16 [simplification]

endmodule

module VERIFICATION-HASKELL [symbolic, kore]
    imports VERIFICATION-COMMON

  // ########################
  // Buffer Reasoning
  // ########################

    rule BA1 ++ (BA2 ++ BA3) => (BA1 ++ BA2) ++ BA3 [concrete(BA1, BA2), simplification]

    rule maxUInt160 &Int Y => Y requires 0 <=Int Y andBool Y <=Int maxUInt160 [simplification]

    rule ( #sizeByteArray(#ecrec( HASH, SIGV, SIGR, SIGS )) ==Int 0  ) =>           #ecrecEmpty ( HASH, SIGV, SIGR, SIGS )  [simplification]
    rule ( #sizeByteArray(#ecrec( HASH, SIGV, SIGR, SIGS )) ==Int 32 ) => notBool ( #ecrecEmpty ( HASH, SIGV, SIGR, SIGS )) [simplification]

    rule ( #sizeByteArray(#ecrec( _, _, _, _ )) <=Int K ) => true requires 32 <=Int K [simplification]

    rule 0 <Int #asWord ( #ecrec( HASH, SIGV, SIGR, SIGS ) ) => notBool ( #ecrecEmpty ( HASH, SIGV, SIGR, SIGS ) )  [simplification]

endmodule

module VERIFICATION-JAVA [symbolic, kast]
    imports VERIFICATION-COMMON
    imports K-REFLECTION

  // ########################
  // Arithmetic
  // ########################

    rule chop(X +Int Y) => X +Int Y
      requires #range(0 <= X <= pow16)
       andBool #range(0 <= Y <  pow16)
      [simplification]

    rule X +Int Y <Int Z => X <Int Z -Int Y requires #isConcrete(Y) [simplification]

endmodule
