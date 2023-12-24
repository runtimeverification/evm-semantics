requires "word.md"

module BITWISE-SIMPLIFICATION [symbolic]
    imports INT-SYMBOLIC
    imports WORD

  // ###########################################################################
  // bit-or
  // ###########################################################################

    rule 0 |Int A => A [simplification]
    rule A |Int 0 => A [simplification]
    rule A |Int A => A [simplification]

    rule A |Int B => B |Int A [simplification(40), concrete(B), symbolic(A)]

    rule  X |Int _  ==Int 0          => false requires 0 <Int X [simplification, concrete(X)]
    rule (A |Int B) ==Int (B |Int A) => true  [simplification, smt-lemma]

  // ###########################################################################
  // bit-and
  // ###########################################################################

    rule A &Int B => B &Int A [symbolic(A), concrete(B), simplification]

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

   // We should probably generalize the simplifications below for relevant powers of two.
    rule notMaxUInt5   &Int X => 0 requires #rangeUInt(  5, X) [simplification]
    rule notMaxUInt8   &Int X => 0 requires #rangeUInt(  8, X) [simplification]
    rule notMaxUInt16  &Int X => 0 requires #rangeUInt( 16, X) [simplification]
    rule notMaxUInt32  &Int X => 0 requires #rangeUInt( 32, X) [simplification]
    rule notMaxUInt64  &Int X => 0 requires #rangeUInt( 64, X) [simplification]
    rule notMaxUInt96  &Int X => 0 requires #rangeUInt( 96, X) [simplification]
    rule notMaxUInt128 &Int X => 0 requires #rangeUInt(128, X) [simplification]
    rule notMaxUInt160 &Int X => 0 requires #rangeUInt(160, X) [simplification]
    rule notMaxUInt192 &Int X => 0 requires #rangeUInt(192, X) [simplification]
    rule notMaxUInt208 &Int X => 0 requires #rangeUInt(208, X) [simplification]
    rule notMaxUInt224 &Int X => 0 requires #rangeUInt(224, X) [simplification]
    rule notMaxUInt240 &Int X => 0 requires #rangeUInt(240, X) [simplification]
    rule notMaxUInt248 &Int X => 0 requires #rangeUInt(248, X) [simplification]

    rule notMaxUInt240 &Int (X <<Int 240) => X <<Int 240 requires #rangeUInt(16, X) [simplification]
    rule notMaxUInt248 &Int (X <<Int 248) => X <<Int 248 requires #rangeUInt( 8, X) [simplification]

    rule maxUInt8   &Int (X |Int (notMaxUInt8   &Int _)) => maxUInt8   &Int X [simplification]
    rule maxUInt16  &Int (X |Int (notMaxUInt16  &Int _)) => maxUInt16  &Int X [simplification]
    rule maxUInt32  &Int (X |Int (notMaxUInt32  &Int _)) => maxUInt32  &Int X [simplification]
    rule maxUInt64  &Int (X |Int (notMaxUInt64  &Int _)) => maxUInt64  &Int X [simplification]
    rule maxUInt96  &Int (X |Int (notMaxUInt96  &Int _)) => maxUInt96  &Int X [simplification]
    rule maxUInt128 &Int (X |Int (notMaxUInt128 &Int _)) => maxUInt128 &Int X [simplification]
    rule maxUInt160 &Int (X |Int (notMaxUInt160 &Int _)) => maxUInt160 &Int X [simplification]
    rule maxUInt192 &Int (X |Int (notMaxUInt192 &Int _)) => maxUInt192 &Int X [simplification]
    rule maxUInt208 &Int (X |Int (notMaxUInt208 &Int _)) => maxUInt208 &Int X [simplification]
    rule maxUInt224 &Int (X |Int (notMaxUInt224 &Int _)) => maxUInt224 &Int X [simplification]
    rule maxUInt240 &Int (X |Int (notMaxUInt240 &Int _)) => maxUInt240 &Int X [simplification]
    rule maxUInt248 &Int (X |Int (notMaxUInt248 &Int _)) => maxUInt248 &Int X [simplification]

    rule [lengthBytes-upInt-32-lower-bound]:
      lengthBytes(X) <=Int notMaxUInt5 &Int ( lengthBytes(X) +Int 31 ) => true
      requires lengthBytes(X) +Int 31 <Int pow256
      [simplification, smt-lemma]

    rule [lengthBytes-upInt-32-upper-bound]:
      lengthBytes(X) +Int 32 >Int notMaxUInt5 &Int ( lengthBytes(X) +Int 31 ) => true
      [simplification, smt-lemma]

  // ###########################################################################
  // bit-xor
  // ###########################################################################

    rule X xorInt Y <Int 0 -Int X => false requires 0 <=Int X andBool 0 <=Int Y [simplification]

  // ###########################################################################
  // shift
  // ###########################################################################

    rule (X <<Int Y) <Int pow256 => true requires 0 <=Int X andBool 0 <=Int Y andBool Y <Int 256 andBool X <Int 2 ^Int (256 -Int Y) [simplification]

    rule 0 <=Int (X <<Int Y) => true requires 0 <=Int X andBool 0 <=Int Y [simplification]

endmodule
