module INT-SIMPLIFICATION
    imports INT-SIMPLIFICATION-HASKELL
endmodule

module INT-SIMPLIFICATION-HASKELL [symbolic, kore]
    imports INT-SIMPLIFICATION-COMMON

  // ###########################################################################
  // add, sub
  // ###########################################################################

    // associativity normalization

    rule A +Int B => B +Int A [concrete(A), symbolic(B), simplification]

    rule A +Int (B +Int C) => (A +Int B) +Int C [symbolic(A, B), simplification]
    rule A +Int (B -Int C) => (A +Int B) -Int C [symbolic(A, B), simplification]
    rule A -Int (B +Int C) => (A -Int B) -Int C [symbolic(A, B), simplification]
    rule A -Int (B -Int C) => (A -Int B) +Int C [symbolic(A, B), simplification]

    rule A +Int (B -Int C) => (A -Int C) +Int B [symbolic(A, C), concrete(B), simplification]
    rule A -Int (B -Int C) => (A +Int C) -Int B [symbolic(A, C), concrete(B), simplification]

    rule (A +Int B) +Int C => (A +Int C) +Int B [concrete(B), symbolic(C), simplification]
    rule (A +Int B) -Int C => (A -Int C) +Int B [concrete(B), symbolic(C), simplification]
    rule (A -Int B) +Int C => (A +Int C) -Int B [concrete(B), symbolic(C), simplification]
    rule (A -Int B) -Int C => (A -Int C) -Int B [concrete(B), symbolic(C), simplification]

    rule (A +Int B) +Int C => A +Int (B +Int C) [concrete(B, C), symbolic(A), simplification]
    rule (A +Int B) -Int C => A +Int (B -Int C) [concrete(B, C), symbolic(A), simplification]
    rule (A -Int B) +Int C => A +Int (C -Int B) [concrete(B, C), symbolic(A), simplification]
    rule (A -Int B) -Int C => A -Int (B +Int C) [concrete(B, C), symbolic(A), simplification]

  // ###########################################################################
  // inequality
  // ###########################################################################

    rule A +Int B  <Int C        => A         <Int C -Int B [concrete(B), simplification]
    rule A         <Int B +Int C => A -Int C  <Int B        [concrete(A, C), simplification]
    rule A        <=Int B +Int C => A -Int C <=Int B        [concrete(A, C), simplification]
    rule A -Int B  <Int C        => A -Int C  <Int B        [concrete(A, C), simplification]
    rule A        <=Int B -Int C => C        <=Int B -Int A [concrete(A, B), simplification]

endmodule

module INT-SIMPLIFICATION-COMMON
    imports INT
    imports BOOL

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

    rule (A *Int C) +Int (B *Int C) => (A +Int B) *Int C [simplification]

    rule (E *Int A) +Int B +Int C +Int D +Int (F *Int A) => ((E +Int F) *Int A) +Int B +Int C +Int D [simplification]

  // ###########################################################################
  // div
  // ###########################################################################

    rule A /Int 1 => A  [simplification]

    // safeMath mul check c / a == b where c == a * b
    rule (A *Int B) /Int A => B requires A =/=Int 0 [simplification]

    rule ((A *Int B) /Int C) /Int B => A /Int C requires B =/=Int 0 [simplification]

    rule (A /Int 32) *Int 32 => A requires A modInt 32 ==Int 0 [simplification]

    rule (A *Int B) /Int C <=Int D => true requires 0 <=Int A andBool 0 <=Int B andBool 0 <Int C andBool A <=Int D andBool B <=Int C [simplification]

  // ###########################################################################
  // mod
  // ###########################################################################

    rule A modInt B => A requires 0 <=Int A andBool A <Int B [simplification]

  // ###########################################################################
  // max, min
  // ###########################################################################

    rule [minint-left]: minInt(A, B) => A requires A <=Int B [simplification]

    rule [minint-lt]:  minInt(A, B) <Int C  => true requires A  <Int C  orBool B  <Int C [simplification]
    rule [minint-gt]:  A  <Int minInt(B, C) => true requires A  <Int B andBool A  <Int C [simplification]
    rule [minint-geq]: A <=Int minInt(B, C) => true requires A <=Int B andBool A <=Int C [simplification]

    rule [maxint-geq-left]: A <=Int maxInt(B, C) => true requires A <=Int B orBool A <=Int C [simplification]

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

endmodule
