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

  // ###########################################################################
  // benchmarks/verification.k
  // ###########################################################################

    rule ((A +Int I1) +Int B) +Int I2 => (A +Int B) +Int (I1 +Int I2)
      requires notBool #isConcrete(A)
       andBool notBool #isConcrete(B)
       andBool #isConcrete(I1)
       andBool #isConcrete(I2)
      [simplification]

    rule (A +Int I1) +Int (B +Int I2) => (A +Int B) +Int (I1 +Int I2)
      requires notBool #isConcrete(A)
       andBool notBool #isConcrete(B)
       andBool #isConcrete(I1)
       andBool #isConcrete(I2)
      [simplification]
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

  // ###########################################################################
  // benchmarks/verification.k
  // ###########################################################################

    rule X +Int Y <Int Z => X <Int Z -Int Y [concrete(Y), simplification]
endmodule

module INT-SIMPLIFICATION-COMMON
    imports INT
    imports BOOL

  // ###########################################################################
  // reorganized
  // ###########################################################################    

  // add, sub
    rule (A +Int I2) +Int (I3 -Int A) => I2 +Int I3 [simplification]
    rule (A +Int I2) -Int (A +Int I3) => I2 -Int I3 [simplification]
    rule (A +Int I2) -Int (I3 +Int A) => I2 -Int I3 [simplification]
    rule (I1 +Int I2) -Int (I3 +Int I1) => I2 -Int I3 [simplification]
    rule A -Int (A -Int I1) => I1 [simplification]
    rule (A +Int I1) -Int A => I1 [simplification]
    rule (A +Int B) +Int (C -Int B) => A +Int C [simplification]
    rule (A +Int B +Int C) -Int (A +Int D) => B +Int (C -Int D) [simplification]
    rule (A +Int B +Int C +Int D +Int E) -Int (A +Int C +Int F) => B +Int D +Int E -Int F [simplification]
    rule A +Int (I1 -Int A) => I1 [simplification]
    rule (I1 +Int (A -Int I0)) +Int (I2 -Int A) => I1 +Int (I2 -Int I0) [simplification]
    rule N -Int N => 0 [simplification]
    rule N -Int N => 0 [simplification]
    rule I -Int 0 => I [simplification]
    rule 0 +Int I => I [simplification]
    rule I +Int 0 => I [simplification]
    rule I -Int I => 0                                                    [simplification]
    rule   (I1 -Int I2)                   +Int I2 =>  I1                  [simplification]
    rule  ((I1 -Int I2) -Int I3)          +Int I2 =>  I1 -Int I3          [simplification]
    rule (((I1 -Int I2) -Int I3) -Int I4) +Int I2 => (I1 -Int I3) -Int I4 [simplification]

  // mul
    rule 1 *Int N => N
    rule N *Int 1 => N
    rule 0 *Int _ => 0
    rule _ *Int 0 => 0
    rule I1 *Int A +Int I2 *Int A => (I1 +Int I2) *Int A [simplification]
    rule I1 *Int A +Int B +Int C +Int D +Int I2 *Int A => (I1 +Int I2) *Int A +Int B +Int C +Int D [simplification]

  // div
    rule N /Int 1 => N  [simplification]
    // safeMath mul check c / a == b where c == a * b
    rule (X *Int Y) /Int X => Y  requires X =/=Int 0 [simplification]
    rule ((X *Int Y) /Int Z) /Int Y => X /Int Z  requires Y =/=Int 0 [simplification]
    rule (X /Int 32) *Int 32 => X  requires X modInt 32 ==Int 0 [simplification]
    rule (I1 *Int I2) /Int I3 <=Int I4 => true
      requires  0  <=Int I1
       andBool  0  <=Int I2
       andBool  0   <Int I3
       andBool  I1 <=Int I4
       andBool  I2 <=Int I3
      [simplification]

  // inc-or
    rule 0 |Int N => N
    rule N |Int 0 => N
    rule N |Int N => N

  // bit-and
    rule  0 &Int _N => 0
    rule _N &Int  0 => 0
    rule  N &Int  N => N

  // mod
    rule X modInt Y => X  requires 0 <=Int X andBool X <Int Y [simplification]

  // max, min
    rule minInt(P, Q)         => P    requires P <=Int Q                   [simplification]


  // inequality
    rule I1 +Int I2 <Int I1 => false requires 0 <=Int I2 [simplification]
    rule I1 <Int I1 -Int I2 => false requires 0 <=Int I2 [simplification]
    rule 0 <Int 1 <<Int N => true  requires 0 <=Int N [simplification]
    //Inequality sign normalization
    rule          X  >Int Y  => Y  <Int X            [simplification]
    rule          X >=Int Y  => Y <=Int X            [simplification]
    rule notBool (X  <Int Y) => Y <=Int X            [simplification]
    rule notBool (X <=Int Y) => Y  <Int X            [simplification]
    rule N <=Int maxInt(P, Q) => true requires N <=Int P orBool N <=Int Q  [simplification]
    rule X -Int Y +Int Z <=Int A => false requires A <Int X -Int Y andBool 0 <=Int Z [simplification]
    rule minInt(G, G') <Int G''  => G <Int G'' orBool G' <Int G''  [simplification]
    rule G  <Int minInt(G', G'') => G  <Int G' andBool G  <Int G'' [simplification]
    rule G <=Int minInt(G', G'') => G <=Int G' andBool G <=Int G'' [simplification]
    rule 0 <=Int X *Int Y => true requires 0 <=Int X andBool 0 <=Int Y [simplification]

  // ###########################################################################
  // lemmas.k
  // ###########################################################################    

  // ###########################################################################
  // infinite-gas.k
  // ###########################################################################

  // ###########################################################################
  // benchmarks/verification.k
  // ###########################################################################

  // ###########################################################################
  // bihu/verification.k
  // ###########################################################################

  // ###########################################################################
  // opcodes/verification.k
  // ###########################################################################

  // ###########################################################################
  // bihu/verification.k
  // ###########################################################################

    // NOTE: there are no rules to pull out here
endmodule