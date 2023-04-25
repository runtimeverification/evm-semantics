requires "evm-types.md"
requires "word.md"

module BITWISE-SIMPLIFICATION [symbolic]
    imports INT-SYMBOLIC
    imports EVM-TYPES
    imports WORD

  // ###########################################################################
  // bit-or
  // ###########################################################################

    rule 0 |Int A => A [simplification]
    rule A |Int 0 => A [simplification]
    rule A |Int A => A [simplification]

  // ###########################################################################
  // bit-and
  // ###########################################################################

    rule 0 &Int _ => 0 [simplification]
    rule _ &Int 0 => 0 [simplification]
    rule A &Int A => A [simplification]

    // PETAR: Why is this one here and not others?
    rule chop ( ( maxUInt48 &Int X:Int ) *Int Y:Int ) => ( maxUInt48 &Int X:Int ) *Int Y
      requires 0 <=Int X andBool 0 <=Int Y andBool Y <=Int pow208 [simplification]

    // PETAR: Why are these here and not others?
    rule maxUInt8   &Int X <Int 256    => true requires 0 <=Int X [simplification, smt-lemma]
    rule maxUInt48  &Int X <Int pow48  => true requires 0 <=Int X [simplification, smt-lemma]
    rule maxUInt160 &Int X <Int pow160 => true requires 0 <=Int X [simplification, smt-lemma]

    rule [bitwise-and-identity]:
      X &Int Y => Y
      requires 0 <=Int X
       andBool X +Int 1 ==Int 2 ^Int log2Int(X +Int 1)
       andBool 0 <=Int Y andBool Y <Int 2 ^Int log2Int(X +Int 1)
       [concrete(X), simplification, comm]

    rule [bitwise-or-geq-zero]:  0 <=Int (X |Int Y) => true requires 0 <=Int X andBool 0 <=Int Y [simplification]
    rule [bitwise-and-geq-zero]: 0 <=Int (X &Int Y) => true requires 0 <=Int X andBool 0 <=Int Y [simplification]

    rule [bitwise-and-lt]:       (X &Int Y) <Int Z      => true requires 0 <=Int X andBool 0 <=Int Y andBool (X <Int Z orBool Y <Int Z)          [simplification]
    rule [bitwise-or-lt-pow256]: (X |Int Y) <Int pow256 => true requires 0 <=Int X andBool 0 <=Int Y andBool X <Int pow256 andBool Y <Int pow256 [simplification]

    // PETAR: We should probably add analogous simplifications for other
    //        relevant powers of two, possibly generally.
    rule notMaxUInt160 &Int X => 0 requires #rangeUInt(160, X) [simplification]
    rule maxUInt160 &Int (X |Int (notMaxUInt160 &Int Y:Int)) => X requires #rangeUInt(160, X) andBool 0 <=Int Y [simplification]

    rule [bitwise-and-asWord-tail]:
      X &Int #asWord ( _ +Bytes B ) => X &Int #asWord ( B )
      requires 0 <=Int X andBool X <Int 2 ^Int (8 *Int lengthBytes(B))
      [simplification]

    rule [bitwise-and-asWord-tail-shift]:
      X &Int ( #asWord ( _ +Bytes B ) >>Int Z ) => X &Int ( #asWord ( B ) >>Int Z )
      requires 0 <=Int X andBool X <Int 2 ^Int ((8 *Int lengthBytes(B)) -Int Z)
      [simplification]

endmodule
