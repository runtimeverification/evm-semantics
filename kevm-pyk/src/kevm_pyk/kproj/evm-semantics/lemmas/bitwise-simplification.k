requires "word.md"

module BITWISE-SIMPLIFICATION [symbolic]
    imports EVM-TYPES
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

    rule [bitwise-or-geq-zero]:  0 <=Int (X |Int Y) => true requires 0 <=Int X andBool 0 <=Int Y [simplification]
    rule [bitwise-and-geq-zero]: 0 <=Int (X &Int Y) => true requires 0 <=Int X andBool 0 <=Int Y [simplification]

    rule [bitwise-or-lt-zero]:  (X |Int Y) <Int Z => false requires 0 <=Int X andBool 0 <=Int Y andBool Z <=Int 0 [concrete(Z), simplification]
    rule [bitwise-and-lt-zero]: (X &Int Y) <Int Z => false requires 0 <=Int X andBool 0 <=Int Y andBool Z <=Int 0 [concrete(Z), simplification]

    rule [bitwise-and-lt]:       (X &Int Y) <Int Z      => true requires 0 <=Int X andBool 0 <=Int Y andBool (X <Int Z orBool Y <Int Z)          [simplification]
    rule [bitwise-or-lt-pow256]: (X |Int Y) <Int pow256 => true requires 0 <=Int X andBool 0 <=Int Y andBool X <Int pow256 andBool Y <Int pow256 [simplification]

    // Generalization of: maxUIntXXX &Int Y => Y requires #rangeUInt(XXX, Y)
    rule [bitwise-and-maxUInt-identity]:
      X &Int Y => Y
      requires 0 <=Int X
       andBool X +Int 1 ==Int 2 ^Int log2Int(X +Int 1)
       andBool 0 <=Int Y andBool Y <Int X +Int 1
       [concrete(X), simplification, comm, preserves-definedness]

    // Generalization of: notMaxUIntXXX &Int Y => 0 requires #rangeUInt(XXX, Y)
    rule [bitwise-and-notMaxUInt-zero]:
      X &Int Y => 0
      requires #rangeUInt(256, X)
       andBool pow256 -Int X ==Int 2 ^Int ( log2Int ( pow256 -Int X ) )
       andBool 0 <=Int Y andBool Y <Int pow256 -Int X
      [simplification, concrete(X), preserves-definedness]

    // Generalization of: maxUIntXXX &Int #asWord ( BA )
    rule X &Int #asWord ( BA ) => #asWord ( #range(BA, 32 -Int (log2Int(X +Int 1) /Int 8), log2Int(X +Int 1) /Int 8) )
    requires #rangeUInt(256, X)
     andBool X +Int 1 ==Int 2 ^Int log2Int(X +Int 1)
     andBool log2Int (X +Int 1) modInt 8 ==Int 0
     andBool lengthBytes(BA) ==Int 32
     [simplification, concrete(X), preserves-definedness]

    // Generalization of: notMaxUIntXXX &Int #asWord ( BA )
    rule X &Int #asWord ( BA ) => #asWord ( #range ( BA, 0, 32 -Int log2Int(pow256 -Int X) /Int 8 ) +Bytes padRightBytes(.Bytes, log2Int(pow256 -Int X) /Int 8, 0 ) )
    requires #rangeUInt(256, X)
     andBool pow256 -Int X ==Int 2 ^Int ( log2Int ( pow256 -Int X ) )
     andBool log2Int ( pow256 -Int X ) modInt 8 ==Int 0
     andBool lengthBytes(BA) ==Int 32
     [simplification, concrete(X), preserves-definedness]

    // Generalization of: notMaxUIntXXX &Int (Y <<Int XXX) => Y <<Int XXX requires #rangeUInt(256 -Int XXX, Y)
    rule X &Int (Y <<Int Z) => Y <<Int Z
      requires #rangeUInt(256, X)
       andBool 2 ^Int ( log2Int ( pow256 -Int X ) ) ==Int pow256 -Int X
       andBool Z ==Int log2Int ( pow256 -Int X )
       andBool 0 <=Int Y andBool Y <Int 2 ^Int ( 256 -Int Z )
      [simplification, concrete(X, Z), comm, preserves-definedness]

    // Generalization of:    maxUIntXXX &Int (Y |Int (notMaxUIntXXX &Int T)) =>    maxUIntXXX &Int Y
    //                and notMaxUIntXXX &Int (Y |Int (   maxUIntXXX &Int T)) => notMaxUIntXXX &Int Y
    rule X &Int (Y |Int (Z &Int T)) => X &Int Y
      requires 0 <=Int X andBool 0 <=Int Y andBool 0 <=Int Z andBool 0 <=Int T
       andBool (      X +Int 1 ==Int 2 ^Int log2Int (      X +Int 1 ) orBool // X is a maxUInt
                 pow256 -Int X ==Int 2 ^Int log2Int ( pow256 -Int X ) )      // X is a notMaxUInt
       andBool X +Int Z ==Int maxUInt256
      [simplification, concrete(X, Z), comm]

    rule [notMaxUInt5-bit-and-nested]:
      notMaxUInt5 &Int ( ( notMaxUInt5 &Int X ) +Int Y ) => chop ( ( notMaxUInt5 &Int X ) +Int ( notMaxUInt5 &Int Y ) )
      requires 0 <=Int X andBool 0 <=Int Y
      [simplification, concrete(Y)]

    rule [lengthBytes-upInt-32-lower-bound]:
      lengthBytes(X) <=Int notMaxUInt5 &Int ( lengthBytes(X) +Int 31 ) => true
      requires lengthBytes(X) +Int 31 <Int pow256
      [simplification, smt-lemma]

    rule [lengthBytes-upInt-32-upper-bound]:
      lengthBytes(X) +Int 32 >Int notMaxUInt5 &Int ( lengthBytes(X) +Int 31 ) => true
      [simplification, smt-lemma]

  // ###########################################################################
  // shift
  // ###########################################################################

    rule (X <<Int Y) <Int pow256 => true
      requires 0 <=Int X andBool 0 <=Int Y andBool Y <Int 256 andBool X <Int 2 ^Int (256 -Int Y)
      [simplification, preserves-definedness]

    rule 0 <=Int (X <<Int Y) => true requires 0 <=Int X andBool 0 <=Int Y [simplification]

endmodule
