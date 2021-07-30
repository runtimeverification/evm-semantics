module INT-SIMPLIFICATION
    imports INT-SIMPLIFICATION-JAVA
    imports INT-SIMPLIFICATION-HASKELL
endmodule

module INT-SIMPLIFICATION-JAVA [symbolic, kast]
    imports INT-SIMPLIFICATION-COMMON
    imports K-REFLECTION

  // ###########################################################################
  // lemmas.k
  // ###########################################################################

    //For #bufStrict simplification in benchmarks
    rule 0  <Int 2 ^Int I => true       requires 0 <=Int I [simplification]
    rule 0 <=Int I *Int 8 => 0 <=Int I                     [simplification]

  // ###########################################################################
  // infinite-gas.k
  // ###########################################################################

    rule I1 +Int C2  <Int C3         => I1          <Int C3 -Int C2 requires #isConcrete(C2) andBool #isConcrete(C3) [simplification]
    rule C1          <Int I2 +Int C3 => C1 -Int C3  <Int I2         requires #isConcrete(C1) andBool #isConcrete(C3) [simplification]
    rule C1         <=Int I2 +Int C3 => C1 -Int C3 <=Int I2         requires #isConcrete(C1) andBool #isConcrete(C3) [simplification]
endmodule

module INT-SIMPLIFICATION-HASKELL [symbolic, kore]
    imports INT-SIMPLIFICATION-COMMON

  // ###########################################################################
  // lemmas.k
  // ###########################################################################

  // ###########################################################################
  // infinite-gas.k
  // ###########################################################################

    rule I1 +Int C2  <Int C3         => I1          <Int C3 -Int C2 [concrete(C2, C3), simplification]
    rule C1          <Int I2 +Int C3 => C1 -Int C3  <Int I2         [concrete(C1, C3), simplification]
    rule C1         <=Int I2 +Int C3 => C1 -Int C3 <=Int I2         [concrete(C1, C3), simplification]

    rule C1 +Int S2 => S2 +Int C1 [concrete(C1), symbolic(S2), simplification]

    rule S1 +Int (S2 +Int I3) => (S1 +Int S2) +Int I3 [symbolic(S1, S2), simplification]
    rule S1 +Int (S2 -Int I3) => (S1 +Int S2) -Int I3 [symbolic(S1, S2), simplification]
    rule S1 -Int (S2 +Int I3) => (S1 -Int S2) -Int I3 [symbolic(S1, S2), simplification]
    rule S1 -Int (S2 -Int I3) => (S1 -Int S2) +Int I3 [symbolic(S1, S2), simplification]

    rule S1 +Int (C2 -Int S3) => (S1 -Int S3) +Int C2 [symbolic(S1, S3), concrete(C2), simplification]
    rule S1 -Int (C2 -Int S3) => (S1 +Int S3) -Int C2 [symbolic(S1, S3), concrete(C2), simplification]

    rule (I1 +Int C2) +Int S3 => (I1 +Int S3) +Int C2 [concrete(C2), symbolic(S3), simplification]
    rule (I1 +Int C2) -Int S3 => (I1 -Int S3) +Int C2 [concrete(C2), symbolic(S3), simplification]
    rule (I1 -Int C2) +Int S3 => (I1 +Int S3) -Int C2 [concrete(C2), symbolic(S3), simplification]
    rule (I1 -Int C2) -Int S3 => (I1 -Int S3) -Int C2 [concrete(C2), symbolic(S3), simplification]

    rule (S1 +Int C2) +Int C3 => S1 +Int (C2 +Int C3) [concrete(C2, C3), symbolic(S1), simplification]
    rule (S1 +Int C2) -Int C3 => S1 +Int (C2 -Int C3) [concrete(C2, C3), symbolic(S1), simplification]
    rule (S1 -Int C2) +Int C3 => S1 +Int (C3 -Int C2) [concrete(C2, C3), symbolic(S1), simplification]
    rule (S1 -Int C2) -Int C3 => S1 -Int (C2 +Int C3) [concrete(C2, C3), symbolic(S1), simplification]

endmodule

module INT-SIMPLIFICATION-COMMON
    imports INT
    imports BOOL

  // ###########################################################################
  // lemmas.k
  // ###########################################################################    

    //Inequality sign normalization
    rule          X  >Int Y  => Y  <Int X            [simplification]
    rule          X >=Int Y  => Y <=Int X            [simplification]
    rule notBool (X  <Int Y) => Y <=Int X            [simplification]
    rule notBool (X <=Int Y) => Y  <Int X            [simplification]

    rule N /Int 1 => N  [simplification]

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

    rule N <=Int maxInt(P, Q) => true requires N <=Int P orBool N <=Int Q  [simplification]

    rule minInt(P, Q)         => P    requires P <=Int Q                   [simplification]

  // ###########################################################################
  // infinite-gas.k
  // ###########################################################################

    rule I -Int I => 0                                                    [simplification]
    rule   (I1 -Int I2)                   +Int I2 =>  I1                  [simplification]
    rule  ((I1 -Int I2) -Int I3)          +Int I2 =>  I1 -Int I3          [simplification]
    rule (((I1 -Int I2) -Int I3) -Int I4) +Int I2 => (I1 -Int I3) -Int I4 [simplification]

    rule X -Int Y +Int Z <=Int A => false requires A <Int X -Int Y andBool 0 <=Int Z [simplification]

    rule minInt(G, G') <Int G''  => G <Int G'' orBool G' <Int G''  [simplification]
    rule G  <Int minInt(G', G'') => G  <Int G' andBool G  <Int G'' [simplification]
    rule G <=Int minInt(G', G'') => G <=Int G' andBool G <=Int G'' [simplification]

    rule 0 <=Int X *Int Y => true requires 0 <=Int X andBool 0 <=Int Y [simplification]
endmodule