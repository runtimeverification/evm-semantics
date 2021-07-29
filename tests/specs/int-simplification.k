module INT-SIMPLIFICATION
    imports INT-SIMPLIFICATION-JAVA
    imports INT-SIMPLIFICATION-HASKELL

  // ###########################################################################
  // lemmas.k
  // ###########################################################################    

    //Inequality sign normalization
    rule          X  >Int Y  => Y  <Int X            [simplification]
    rule          X >=Int Y  => Y <=Int X            [simplification]
    rule notBool (X  <Int Y) => Y <=Int X            [simplification]
    rule notBool (X <=Int Y) => Y  <Int X            [simplification]

    rule N /Int 1 => N  [simplification]

  // ###########################################################################
  // infinite-gas.k
  // ###########################################################################
endmodule

module INT-SIMPLIFICATION-JAVA
    imports INT-SIMPLIFICATION-COMMON

  // ###########################################################################
  // lemmas.k
  // ###########################################################################

    rule 1 *Int N => N
    rule N *Int 1 => N
    rule 0 *Int _ => 0
    rule _ *Int 0 => 0

    rule 0 |Int N => N
    rule N |Int 0 => N
    rule N |Int N => N

    rule  0 &Int _N => 0
    rule _N &Int  0 => 0
    rule  N &Int  N => N

    //For #bufStrict simplification in benchmarks
    rule 0  <Int 2 ^Int I => true       requires 0 <=Int I [simplification]
    rule 0 <=Int I *Int 8 => 0 <=Int I                     [simplification]

  // ###########################################################################
  // infinite-gas.k
  // ###########################################################################
endmodule

module INT-SIMPLIFICATION-HASKELL
    imports INT-SIMPLIFICATION-COMMON

  // ###########################################################################
  // lemmas.k
  // ###########################################################################

  rule N <=Int maxInt(P, Q) => true requires N <=Int P orBool N <=Int Q  [simplification]

  rule minInt(P, Q)         => P    requires P <=Int Q                   [simplification]

  // ###########################################################################
  // infinite-gas.k
  // ###########################################################################
endmodule

module INT-SIMPLIFICATION-COMMON
    imports INT
    imports BOOL
endmodule