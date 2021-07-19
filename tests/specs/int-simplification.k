//
// Int Simplification
// TODO: explanation
//

module INT-SIMPLIFICATION
    imports INT-SIMPLIFICATION-HASKELL
    imports INT-SIMPLIFICATION-JAVA

  // ################################
  // from tests/specs/infinite-gas.k
  // ################################

    rule X -Int X => 0 [simplification]

    rule   (X -Int Y)                 +Int Y =>  X                [simplification]
    rule  ((X -Int Y) -Int Z)         +Int Y =>  X -Int Z         [simplification]
    rule (((X -Int Y) -Int Z) -Int W) +Int Y => (X -Int Z) -Int W [simplification]

    rule X -Int Y +Int Z <=Int A => false requires A <Int X -Int Y andBool 0 <=Int Z [simplification]

    rule minInt(X, Y)  <Int Z            => X  <Int Z orBool  Y  <Int Z [simplification]
    rule X             <Int minInt(Y, Z) => X  <Int Y andBool X  <Int Z [simplification]
    rule X            <=Int minInt(Y, Z) => X <=Int Y andBool X <=Int Z [simplification]

    rule 0 <=Int X *Int Y => true requires 0 <=Int X andBool 0 <=Int Y [simplification]
    
  // ##########################
  // from tests/specs/lemmas.k
  // ##########################

    //Inequality sign normalization
    rule          X  >Int Y  => Y  <Int X [simplification]
    rule          X >=Int Y  => Y <=Int X [simplification]
    rule notBool (X  <Int Y) => Y <=Int X [simplification]
    rule notBool (X <=Int Y) => Y  <Int X [simplification]

    rule N /Int 1 => N  [simplification]

endmodule

module INT-SIMPLIFICATION-JAVA [kast]
    imports INT
    imports BOOL
    imports K-REFLECTION

  // ################################
  // from tests/specs/infinite-gas.k
  // ################################

    rule X +Int B  <Int  C        => X         <Int C -Int B requires #isConcrete(B) andBool #isConcrete(C) [simplification]
    rule A         <Int  Y +Int C => A -Int C  <Int Y        requires #isConcrete(A) andBool #isConcrete(C) [simplification]
    rule A         <=Int Y +Int C => A -Int C <=Int Y        requires #isConcrete(A) andBool #isConcrete(C) [simplification]

    rule A +Int Y => Y +Int A requires #isConcrete(A) andBool notBool #isConcrete(Y) [simplification]

    rule X +Int (Y +Int Z) => (X +Int Y) +Int Z requires (notBool #isConcrete(X)) andBool (notBool #isConcrete(Y)) [simplification]
    rule X +Int (Y -Int Z) => (X +Int Y) -Int Z requires (notBool #isConcrete(X)) andBool (notBool #isConcrete(Y)) [simplification]
    rule X -Int (Y +Int Z) => (X -Int Y) -Int Z requires (notBool #isConcrete(X)) andBool (notBool #isConcrete(Y)) [simplification]
    rule X -Int (Y -Int Z) => (X -Int Y) +Int Z requires (notBool #isConcrete(X)) andBool (notBool #isConcrete(Y)) [simplification]

    rule X +Int (B -Int Z) => (X -Int Z) +Int B requires #isConcrete(B) andBool (notBool #isConcrete(X)) andBool (notBool #isConcrete(Z)) [simplification]
    rule X -Int (B -Int Z) => (X +Int Z) -Int B requires #isConcrete(B) andBool (notBool #isConcrete(X)) andBool (notBool #isConcrete(Z)) [simplification]

    rule (X +Int B) +Int Z => (X +Int Z) +Int B requires #isConcrete(B) andBool notBool #isConcrete(Z) [simplification]
    rule (X +Int B) -Int Z => (X -Int Z) +Int B requires #isConcrete(B) andBool notBool #isConcrete(Z) [simplification]
    rule (X -Int B) +Int Z => (X +Int Z) -Int B requires #isConcrete(B) andBool notBool #isConcrete(Z) [simplification]
    rule (X -Int B) -Int Z => (X -Int Z) -Int B requires #isConcrete(B) andBool notBool #isConcrete(Z) [simplification]

    rule (X +Int B) +Int C => X +Int (B +Int C) requires #isConcrete(B) andBool #isConcrete(C) andBool notBool #isConcrete(X) [simplification]
    rule (X +Int B) -Int C => X +Int (B -Int C) requires #isConcrete(B) andBool #isConcrete(C) andBool notBool #isConcrete(X) [simplification]
    rule (X -Int B) +Int C => X +Int (C -Int B) requires #isConcrete(B) andBool #isConcrete(C) andBool notBool #isConcrete(X) [simplification]
    rule (X -Int B) -Int C => X -Int (B +Int C) requires #isConcrete(B) andBool #isConcrete(C) andBool notBool #isConcrete(X) [simplification]
    
    // NOTE: The only test that fails without this lemma (on the java backend)
    // is `tests/specs/functional/lemmas-no-smt-spec.k.prove`
    rule A &Int (B &Int Z) => (A &Int B) &Int Z requires #isConcrete(A) andBool #isConcrete(B) andBool (notBool #isConcrete(Z)) [simplification]

  // ##########################
  // from tests/specs/lemmas.k
  // ##########################

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

    // for #bufStrict simplification in benchmarks
    rule 0  <Int 2 ^Int I => true       requires 0 <=Int I [simplification]
    rule 0 <=Int I *Int 8 => 0 <=Int I                     [simplification]

endmodule

module INT-SIMPLIFICATION-HASKELL [kore]
    imports INT
    imports BOOL

  // ################################
  // from tests/specs/infinite-gas.k
  // ################################

    rule X +Int B  <Int C         => X          <Int C -Int B [concrete(B, C), simplification]
    rule A          <Int Y +Int C => A -Int C  <Int Y         [concrete(A, C), simplification]
    rule A         <=Int Y +Int C => A -Int C <=Int Y         [concrete(A, C), simplification]

    rule A +Int Y => Y +Int A [concrete(A), symbolic(Y), simplification]

    rule X +Int (Y +Int Z) => (X +Int Y) +Int Z [symbolic(X, Y), simplification]
    rule X +Int (Y -Int Z) => (X +Int Y) -Int Z [symbolic(X, Y), simplification]
    rule X -Int (Y +Int Z) => (X -Int Y) -Int Z [symbolic(X, Y), simplification]
    rule X -Int (Y -Int Z) => (X -Int Y) +Int Z [symbolic(X, Y), simplification]

    rule X +Int (B -Int Z) => (X -Int Z) +Int B [symbolic(X, Z), concrete(B), simplification]
    rule X -Int (B -Int Z) => (X +Int Z) -Int B [symbolic(X, Z), concrete(B), simplification]

    rule (X +Int B) +Int Z => (X +Int Z) +Int B [concrete(B), symbolic(Z), simplification]
    rule (X +Int B) -Int Z => (X -Int Z) +Int B [concrete(B), symbolic(Z), simplification]
    rule (X -Int B) +Int Z => (X +Int Z) -Int B [concrete(B), symbolic(Z), simplification]
    rule (X -Int B) -Int Z => (X -Int Z) -Int B [concrete(B), symbolic(Z), simplification]

    rule (X +Int B) +Int C => X +Int (B +Int C) [concrete(B, C), symbolic(X), simplification]
    rule (X +Int B) -Int C => X +Int (B -Int C) [concrete(B, C), symbolic(X), simplification]
    rule (X -Int B) +Int C => X +Int (C -Int B) [concrete(B, C), symbolic(X), simplification]
    rule (X -Int B) -Int C => X -Int (B +Int C) [concrete(B, C), symbolic(X), simplification]

    // TODO: Is this actually needed?
    // It's included in java lemmas, but wasn't originally included in haskell
    // lemmas. I put it here for the sake of symmetry. The only test that fails
    // for the java backend without this lemma (in the java section) is
    // `tests/specs/functional/lemmas-no-smt-spec.k.prove`, and it actually
    // passes with the haskell backend without it (here in the haskell section).
    rule A &Int (B &Int Z) => (A &Int B) &Int Z [concrete(A, B), symbolic(Z), simplification]

  // ##########################
  // from tests/specs/lemmas.k
  // ##########################

    rule N <=Int maxInt(P, Q) => true requires N <=Int P orBool N <=Int Q [simplification]

    rule minInt(P, Q) => P requires P <=Int Q [simplification]

endmodule
