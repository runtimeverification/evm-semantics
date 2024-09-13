requires "evm-types.md"

module EVM-INT-SIMPLIFICATION
    imports BOOL
    imports BUF
    imports EVM-TYPES
    imports INT
    imports WORD

  // ###########################################################################
  // up/Int
  // ###########################################################################

    rule [upInt-lt-true]:
      ((X up/Int Y) *Int Y) <Int Z => true
      requires X +Int Y <=Int Z andBool 0 <Int Y
      [simplification]

    rule [upInt-lt-false]:
      ((X up/Int Y) *Int Y) <Int Z => false
      requires Z <=Int X andBool 0 <Int Y
      [simplification]

    rule [upInt-refl-leq]:
      ((X up/Int Y) *Int Y) <=Int X => X modInt Y ==Int 0
      requires 0 <Int Y
      [simplification, preserves-definedness]

    rule [upInt-refl-gt]:
      X <Int ((X up/Int Y) *Int Y) => X modInt Y =/=Int 0
      requires 0 <Int Y
      [simplification, preserves-definedness]

    rule [upInt-refl-geq]:
      X <=Int ((X up/Int Y) *Int Y) => true
      requires 0 <Int Y
      [simplification]

    rule [upInt-ref-eq]:
      X ==Int ((X up/Int Y) *Int Y) => X modInt Y ==Int 0
      requires 0 <Int Y
      [simplification, comm, preserves-definedness]

    rule [upInt-refl-neq]:
      X =/=Int ((X up/Int Y) *Int Y) => X modInt Y =/=Int 0
      requires 0 <Int Y
      [simplification, comm, preserves-definedness]

  // ###########################################################################
  // #asWord
  // ###########################################################################

  // Unification: two `#asWord`s
  rule [asWord-eq-asWord]:
    #asWord ( B1 ) ==Int #asWord ( B2 ) => #buf ( 32 -Int lengthBytes(B1), 0 ) +Bytes B1 ==K #buf ( 32 -Int lengthBytes(B2), 0 ) +Bytes B2
    requires lengthBytes(B1) <=Int 32 andBool lengthBytes(B2) <=Int 32
    [simplification, preserves-definedness]

  // Unification: two `#asWord`s
  rule [asWord-eq-asWord-ml]:
    { #asWord ( B1 ) #Equals #asWord ( B2 ) } => { true #Equals #asWord ( B1 ) ==Int #asWord ( B2 ) }
    [simplification, preserves-definedness]

  // Unification: `#asWord` and concrete number
  rule [asWord-eq-num]:
    #asWord ( B:Bytes ) ==Int X:Int =>
      0 <=Int X andBool X <Int 2 ^Int (8 *Int minInt(32, lengthBytes(B)))
                andBool (
                  ( lengthBytes(B) <=Int 32 andBool #buf ( 32 -Int lengthBytes(B), 0 ) +Bytes B ==K #buf ( 32, X ) )
                    orBool
                  ( lengthBytes(B) >Int 32 andBool #range ( B, lengthBytes(B) -Int 32, 32 ) ==K #buf ( 32, X ) )
                )
    [simplification, concrete(X), comm, preserves-definedness]

  // Unification: `#asWord` and concrete number
  rule [asWord-eq-num-ml-l]: { #asWord ( B:Bytes ) #Equals X:Int } => { true #Equals #asWord ( B:Bytes ) ==K X:Int } [simplification, concrete(X), preserves-definedness]
  rule [asWord-eq-num-ml-r]: { X:Int #Equals #asWord ( B:Bytes ) } => { true #Equals #asWord ( B:Bytes ) ==K X:Int } [simplification, concrete(X), preserves-definedness]

  // Reduction: we can always remove leading zeros
  rule [asWord-trim-leading-zeros]:
    #asWord ( BZ +Bytes B ) => #asWord ( B )
    requires #asInteger ( BZ ) ==Int 0
    [simplification(40), concrete(BZ), preserves-definedness]

  // Reduction: we can always ignore content beyond 32 bytes
  rule [asWord-trim-overflowing]:
    #asWord ( B ) => #asWord ( #range(B, lengthBytes(B) -Int 32, 32) )
    requires 32 <Int lengthBytes(B)
    [simplification(40), preserves-definedness]

  // Reduction: `#range` can be ignored under certain conditions
  rule [asWord-range]:
    #asWord ( #range ( B:Bytes, S, W ) ) => #asWord ( B )
    requires 0 <=Int S andBool 0 <=Int W
     andBool lengthBytes(B) <=Int 32
     andBool lengthBytes(B) ==Int S +Int W
     andBool #asWord ( B ) <Int 2 ^Int ( 8 *Int W )
    [simplification, concrete(S, W), preserves-definedness]

  // Reduction: `#asWord` inverts `#buf` under certain conditions
  rule [asWord-buf-inversion]:
    #asWord ( #buf ( WB:Int, X:Int ) ) => X
    requires 0 <=Int WB andBool 0 <=Int X andBool X <Int minInt ( 2 ^Int (8 *Int WB), pow256 )
    [simplification, concrete(WB), preserves-definedness]

  // Reduction: bitwise right shift in terms of `#range`
  rule [asWord-shr]:
    #asWord( BA ) >>Int N => #asWord ( #range ( BA, 0, lengthBytes( BA ) -Int ( N /Int 8 ) ) )
    requires 0 <=Int N andBool N modInt 8 ==Int 0
    [simplification, concrete(N), preserves-definedness]

  // Reduction: division in terms of `#range`
  rule [asWord-div]:
    #asWord( BA ) /Int N => #asWord ( #range ( BA, 0, lengthBytes( BA ) -Int ( log2Int( N ) /Int 8 ) ) )
    requires 0 <Int N andBool N ==Int 2 ^Int log2Int ( N ) andBool log2Int( N ) modInt 8 ==Int 0
     andBool lengthBytes ( BA ) <=Int 32
    [simplification, preserves-definedness]

  // Comparison: `#asWord` is always in the range `[0, pow256)`
  rule [asWord-lb]: 0 <=Int #asWord( _ )     => true [simplification, smt-lemma]
  rule [asWord-ub]: #asWord( _ ) <Int pow256 => true [simplification, smt-lemma]

  // Comparison: `#asWord(B)` is certainly less than something that does not fit into `lengthBytes(B)` bytes
  rule [asWord-lt]:  #asWord ( B )  <Int X:Int => true  requires   2 ^Int (8 *Int minInt(32, lengthBytes(B)))          <=Int X [simplification, preserves-definedness]
  // Comparison: `#asWord(B)` is certainly less than or equal to something that is not less than the max number fitting into `lengthBytes(B)` bytes
  rule [asWord-le]:  #asWord ( B ) <=Int X:Int => true  requires ( 2 ^Int (8 *Int minInt(32, lengthBytes(B))) -Int 1 ) <=Int X [simplification, preserves-definedness]

  // Comparison: `#asWord` of `+Bytes` when lower bytes match, with `<Int`
  rule [asWord-concat-lt]:
    #asWord ( BA1 +Bytes BA2 ) <Int X:Int => #asWord ( BA1 ) <Int X /Int ( 2 ^Int ( 8 *Int lengthBytes ( BA2 ) ) )
    requires #asWord ( BA2 ) ==Int X modInt ( 2 ^Int ( 8 *Int lengthBytes ( BA2 ) ) )
     andBool lengthBytes ( BA1 +Bytes BA2 ) <=Int 32
    [simplification, concrete(BA2, X), preserves-definedness]

  // Comparison: `#asWord` of `+Bytes` when lower bytes match, with `<=Int`
  rule [asWord-concat-le]:
    #asWord ( BA1 +Bytes BA2 ) <=Int X:Int => #asWord ( BA1 ) <=Int X /Int ( 2 ^Int ( 8 *Int lengthBytes ( BA2 ) ) )
    requires #asWord ( BA2 ) ==Int X modInt ( 2 ^Int ( 8 *Int lengthBytes ( BA2 ) ) )
     andBool lengthBytes ( BA1 +Bytes BA2 ) <=Int 32
    [simplification, concrete(BA2, X), preserves-definedness]

  // ###########################################################################
  // chop
  // ###########################################################################

    rule [chop-resolve]:     chop(I) => I requires #rangeUInt( 256 , I ) [simplification]
    rule [chop-upper-bound]: 0 <=Int chop(_V)             => true        [simplification, smt-lemma]
    rule [chop-lower-bound]:         chop(_V) <Int pow256 => true        [simplification, smt-lemma]

    rule [chop-add-left]:  chop ( chop ( X:Int ) +Int Y:Int ) => chop ( X +Int Y ) [simplification]
    rule [chop-add-right]: chop ( X:Int +Int chop ( Y:Int ) ) => chop ( X +Int Y ) [simplification]
    rule [chop-mul-left]:  chop ( chop ( X:Int ) *Int Y:Int ) => chop ( X *Int Y ) [simplification]
    rule [chop-mul-right]: chop ( X:Int *Int chop ( Y:Int ) ) => chop ( X *Int Y ) [simplification]

    rule [chop-add-r-pos]:
      chop ( X:Int +Int Y:Int ) ==Int 0 => X ==Int chop ( pow256 -Int chop ( Y ) )
      requires #rangeUInt(256, X) andBool 0 <=Int Y
      [simplification, concrete(Y), comm]

    rule [chop-add-r-neg]:
      chop ( X:Int +Int Y:Int ) ==Int 0 => X ==Int (-1) *Int Y
      requires #rangeUInt(256, X) andBool #rangeUInt(256, (-1) *Int Y)
      [simplification, concrete(Y), comm]

    rule [chop-zero-sub]:
      chop ( 0 -Int X:Int ) ==Int Y:Int => X ==Int chop ( pow256 -Int Y )
      requires #rangeUInt(256, X) andBool #rangeUInt(256, Y)
      [simplification, concrete(Y), comm]

    rule [chop-no-overflow-add-le-l]: X:Int <=Int chop ( X +Int Y:Int )        => X +Int Y <Int pow256 requires #rangeUInt(256, X) andBool #rangeUInt(256, Y) [simplification]
    rule [chop-no-overflow-add-le-r]: X:Int <=Int chop ( Y:Int +Int X )        => X +Int Y <Int pow256 requires #rangeUInt(256, X) andBool #rangeUInt(256, Y) [simplification]
    rule [chop-no-overflow-mul-le-l]: X:Int <=Int chop ( X *Int Y:Int ) /Int Y => X *Int Y <Int pow256 requires #rangeUInt(256, X) andBool 0 <Int Y           [simplification, preserves-definedness]
    rule [chop-no-overflow-mul-le-r]: X:Int <=Int chop ( Y:Int *Int X ) /Int Y => X *Int Y <Int pow256 requires #rangeUInt(256, X) andBool 0 <Int Y           [simplification, preserves-definedness]
    rule [chop-no-overflow-mul-eq-l]: X:Int ==Int chop ( X *Int Y:Int ) /Int Y => X *Int Y <Int pow256 requires #rangeUInt(256, X) andBool 0 <Int Y           [simplification, preserves-definedness, comm]
    rule [chop-no-overflow-mul-eq-r]: X:Int ==Int chop ( Y:Int *Int X ) /Int Y => X *Int Y <Int pow256 requires #rangeUInt(256, X) andBool 0 <Int Y           [simplification, preserves-definedness, comm]

    rule [chop-no-overflow-mul-eq-ml-ll]: { X #Equals chop ( X *Int Y ) /Int Y } => { true #Equals X *Int Y <Int pow256 } requires #rangeUInt(256, X) andBool 0 <Int Y [simplification, preserves-definedness]
    rule [chop-no-overflow-mul-eq-ml-rl]: { X #Equals chop ( Y *Int X ) /Int Y } => { true #Equals X *Int Y <Int pow256 } requires #rangeUInt(256, X) andBool 0 <Int Y [simplification, preserves-definedness]
    rule [chop-no-overflow-mul-eq-ml-lr]: { chop ( X *Int Y ) /Int Y #Equals X } => { true #Equals X *Int Y <Int pow256 } requires #rangeUInt(256, X) andBool 0 <Int Y [simplification, preserves-definedness]
    rule [chop-no-overflow-mul-eq-ml-rr]: { chop ( Y *Int X ) /Int Y #Equals X } => { true #Equals X *Int Y <Int pow256 } requires #rangeUInt(256, X) andBool 0 <Int Y [simplification, preserves-definedness]

endmodule
