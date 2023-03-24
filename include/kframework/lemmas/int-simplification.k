requires "evm-types.md"

module INT-SIMPLIFICATION
    imports INT-SIMPLIFICATION-HASKELL
endmodule

module INT-SIMPLIFICATION-HASKELL [symbolic, kore]
    imports INT-SIMPLIFICATION-COMMON

  // ###########################################################################
  // add, sub
  // ###########################################################################

    // associativity normalization

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
  // inequality
  // ###########################################################################

    rule I1 +Int C   <Int I2         => I1          <Int I2 -Int C  [concrete(C), simplification]
    rule C1          <Int I2 +Int C3 => C1 -Int C3  <Int I2         [concrete(C1, C3), simplification]
    rule C1         <=Int I2 +Int C3 => C1 -Int C3 <=Int I2         [concrete(C1, C3), simplification]
    rule C1 -Int I2  <Int C3         => C1 -Int C3  <Int I2         [concrete(C1, C3), simplification]
    rule C1         <=Int C2 -Int I3 => I3         <=Int C2 -Int C1 [concrete(C1, C2), simplification]

endmodule

module INT-SIMPLIFICATION-COMMON
    imports INT
    imports BOOL
    imports EVM-TYPES

  // ###########################################################################
  // add, sub
  // ###########################################################################

  // 2 terms
    rule A -Int A => 0 [simplification]
    rule A -Int 0 => A [simplification]
    rule 0 +Int A => A [simplification]
    rule A +Int 0 => A [simplification]

  // 3 terms
    rule  (A -Int  B) +Int B  => A [simplification]
    rule   A -Int (A  -Int B) => B [simplification]
    rule   A +Int (B  -Int A) => B [simplification]
    rule  (A +Int  B) -Int A  => B [simplification]

  // 4 terms
    // NOTE: these rules appear to be necessary for tests/specs/benchmarks/ecrecoverloop02-sig1-invalid-spec.k
    rule  (A +Int B) +Int (C  -Int A) => B +Int C [simplification]
    rule  (A +Int B) -Int (A  +Int C) => B -Int C [simplification]
    rule  (A +Int B) -Int (C  +Int A) => B -Int C [simplification]
    rule  (A +Int B) +Int (C  -Int B) => A +Int C [simplification]
    rule ((A -Int B) -Int  C) +Int B  => A -Int C [simplification]

  // 5 terms
    // NOTE: required for `tests/specs/functional/infinite-gas-spec.k.prove` (haskell)
    rule   (A +Int  B  +Int C)  -Int (A  +Int D) =>  B +Int (C  -Int D) [simplification]
    rule   (C +Int (A  -Int D)) +Int (B  -Int A) =>  C +Int (B  -Int D) [simplification]
    rule (((A -Int  B) -Int C)  -Int  D) +Int B  => (A -Int  C) -Int D  [simplification]

  // ###########################################################################
  // mul
  // ###########################################################################

    rule 1 *Int A => A [simplification]
    rule A *Int 1 => A [simplification]
    rule 0 *Int _ => 0 [simplification]
    rule _ *Int 0 => 0 [simplification]

    rule (C *Int A) +Int (B *Int A) => (C +Int B) *Int A [simplification]

    rule (E *Int A) +Int B +Int C +Int D +Int (F *Int A) => ((E +Int F) *Int A) +Int B +Int C +Int D [simplification]

  // ###########################################################################
  // div
  // ###########################################################################

    rule A /Int 1 => A  [simplification]

    // safeMath mul check c / a == b where c == a * b
    rule (A *Int B) /Int A => B  requires A =/=Int 0 [simplification]

    rule ((A *Int B) /Int C) /Int B => A /Int C  requires B =/=Int 0 [simplification]

    rule (A /Int 32) *Int 32 => A  requires A modInt 32 ==Int 0 [simplification]

    rule (A *Int B) /Int C <=Int D => true requires 0 <=Int A andBool 0 <=Int B andBool 0 <Int C andBool A <=Int D andBool B <=Int C [simplification]

  // ###########################################################################
  // mod
  // ###########################################################################

    rule A modInt B => A requires 0 <=Int A andBool A <Int B [simplification]

  // ###########################################################################
  // max, min
  // ###########################################################################

    rule minInt(A, B) => A requires A <=Int B [simplification]

  // ###########################################################################
  // inequality
  // ###########################################################################

    rule A +Int B <Int A => false requires 0 <=Int B [simplification]
    rule A +Int B <Int B => false requires 0 <=Int A [simplification]

    rule A <Int A -Int B => false requires 0 <=Int B [simplification]

    rule 0 <Int 1 <<Int A => true requires 0 <=Int A [simplification]

    // inequality sign normalization
    rule          A  >Int B  => B  <Int A [simplification]
    rule          A >=Int B  => B <=Int A [simplification]
    rule notBool (A  <Int B) => B <=Int A [simplification]
    rule notBool (A <=Int B) => B  <Int A [simplification]

    rule 0 <=Int A *Int B => true requires 0 <=Int A andBool 0 <=Int B [simplification]

    rule A -Int B +Int C <=Int D => false requires D <Int A -Int B andBool 0 <=Int C [simplification]

    rule minInt(A, B) <Int C  => true requires A  <Int C  orBool B  <Int C [simplification]
    rule A  <Int minInt(B, C) => true requires A  <Int B andBool A  <Int C [simplification]
    rule A <=Int minInt(B, C) => true requires A <=Int B andBool A <=Int C [simplification]

    rule A <=Int maxInt(B, C) => true requires A <=Int B orBool A <=Int C [simplification]

  //
  // Arithmetic
  //

    // Distributivity of minInt against +Int
    rule [minInt-factor-left]:  minInt ( A:Int +Int B:Int, A:Int +Int C:Int ) => A +Int minInt ( B, C ) [simplification]
    rule [minInt-factor-right]: minInt ( A:Int +Int B:Int, C:Int +Int B:Int ) => minInt ( A, C ) +Int B [simplification]

    // Definition of maxInt
    rule [maxint-left]:  maxInt(I1:Int, I2:Int) => I2 requires I1 <=Int I2 [simplification]
    rule [maxint-right]: maxInt(I1:Int, I2:Int) => I1 requires I1 >=Int I2 [simplification]

    // Maximum is not greater than if both operands are not greater than
    rule [maxint-leq-split]: maxInt(A:Int, B:Int) <=Int X:Int => A <=Int X andBool B <=Int X [simplification]

  //
  // up/Int
  //

    // Upper bound on the up/Int *Int operation
    rule [upInt-lt-true]:
      ((X up/Int Y) *Int Y) <Int Z => true
      requires X <=Int (Z -Int Y)
        andBool 0 <Int Y
      [simplification]

    // X up/Int Y always rounds up
    rule [upInt-lt-false]:
      ((X up/Int Y) *Int Y) <Int X => false
      requires 0 <Int Y
      [simplification]

endmodule
