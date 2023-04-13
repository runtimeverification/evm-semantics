module TEST-HELPER-LEMMAS
  imports ASSERTTEST-BIN-RUNTIME

  syntax Bytes ::= testFunction() [function]
  syntax Set ::= testFunction2(Bytes) [function]

  rule testFunction() => AssertTest.test_assert_true() [simplification]
  rule testFunction() => #binRuntime(AssertTest) [simplification]
  rule testFunction2(PGM) => #computeValidJumpDests(PGM) [simplification]

endmodule
