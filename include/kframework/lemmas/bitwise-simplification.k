requires "word.md"

module BITWISE-SIMPLIFICATION [symbolic]
    imports INT-SYMBOLIC
    imports WORD

  // ###########################################################################
  // inc-or
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

    rule chop ( ( maxUInt48 &Int X:Int ) *Int Y:Int ) => ( maxUInt48 &Int X:Int ) *Int Y
      requires 0 <=Int X andBool 0 <=Int Y andBool Y <=Int pow208 [simplification]

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

    rule notMaxUInt160 &Int X => 0 requires #rangeUInt(160, X) [simplification]
    rule maxUInt160 &Int (X |Int (notMaxUInt160 &Int Y:Int)) => X requires #rangeUInt(160, X) andBool 0 <=Int Y [simplification]

    rule [lengthBytes-upInt-32-lower-bound]:
      lengthBytes(X) <=Int notMaxUInt5 &Int ( lengthBytes(X) +Int 31 ) => true
      requires lengthBytes(X) +Int 31 <Int pow256
      [simplification, smt-lemma]

    rule [lengthBytes-upInt-32-upper-bound]:
      lengthBytes(X) +Int 32 >Int notMaxUInt5 &Int ( lengthBytes(X) +Int 31 ) => true
      [simplification, smt-lemma]

endmodule
