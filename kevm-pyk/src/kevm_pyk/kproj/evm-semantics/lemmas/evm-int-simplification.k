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

  // Unification: equality with `#asWord` to equality with `+Bytes`
  rule #asWord ( B:Bytes ) ==Int X:Int => #buf ( 32 -Int lengthBytes(B), 0 ) +Bytes B ==K #buf ( 32, X )
    requires lengthBytes( B ) <=Int 32 andBool #rangeUInt(256, X)
    [simplification, comm, preserves-definedness]

  // Unification: equality with `#asWord` to equality with `+Bytes`
  rule { #asWord ( B:Bytes ) #Equals X:Int } => { #buf ( 32 -Int lengthBytes(B), 0 ) +Bytes B #Equals #buf ( 32, X ) } [simplification, preserves-definedness]
  rule { X:Int #Equals #asWord ( B:Bytes ) } => { #buf ( 32 -Int lengthBytes(B), 0 ) +Bytes B #Equals #buf ( 32, X ) } [simplification, preserves-definedness]

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
    [simplification, preserves-definedness]

  // Comparison: `#asWord` is always in the range `[0, pow256)`
  rule [asWord-lb]: 0 <=Int #asWord( _ )     => true [simplification, smt-lemma]
  rule [asWord-ub]: #asWord( _ ) <Int pow256 => true [simplification, smt-lemma]

  // Comparison: `#asWord(B)` is certainly less than something that does not fit into `lengthBytes(B)` bytes
  rule [asWord-lt]:  #asWord ( B )  <Int X:Int => true  requires X >=Int   2 ^Int (8 *Int minInt(32, lengthBytes(B)))          [simplification, preserves-definedness]
  // Comparison: `#asWord(B)` is certainly less than or equal to something that is not less than the max number fitting into `lengthBytes(B)` bytes
  rule [asWord-le]:  #asWord ( B ) <=Int X:Int => true  requires X >=Int ( 2 ^Int (8 *Int minInt(32, lengthBytes(B))) -Int 1 ) [simplification, preserves-definedness]
  // Comparison: `#asWord(B)` is certainly not equal to something that does not fit into `lengthBytes(B)` bytes
  rule [asWord-neq]: #asWord ( B ) ==Int X:Int => false requires X >=Int   2 ^Int (8 *Int minInt(32, lengthBytes(B)))          [simplification, preserves-definedness]

  // Comparison: `#asWord` of `+Bytes` when lower bytes match, with `<Int`
  rule [asWord-concat-lt]:
    #asWord ( BA1 +Bytes BA2 ) <Int X:Int => #asWord ( BA1 ) <Int X /Int ( 2 ^Int ( 8 *Int lengthBytes ( BA2 ) ) )
    requires #asWord ( BA2 ) ==Int X modInt ( 2 ^Int ( 8 *Int lengthBytes ( BA2 ) ) )
    [simplification, concrete(BA2, X), preserves-definedness]

  // Comparison: `#asWord` of `+Bytes` when lower bytes match, with `<=Int`
  rule [asWord-concat-le]:
    #asWord ( BA1 +Bytes BA2 ) <=Int X:Int => #asWord ( BA1 ) <=Int X /Int ( 2 ^Int ( 8 *Int lengthBytes ( BA2 ) ) )
    requires #asWord ( BA2 ) ==Int X modInt ( 2 ^Int ( 8 *Int lengthBytes ( BA2 ) ) )
    [simplification, concrete(BA2, X), preserves-definedness]

  // ###########################################################################
  // chop
  // ###########################################################################

    rule [chop-resolve]:     chop(I) => I requires #rangeUInt( 256 , I ) [simplification]
    rule [chop-upper-bound]: 0 <=Int chop(_V)             => true        [simplification, smt-lemma]
    rule [chop-lower-bound]:         chop(_V) <Int pow256 => true        [simplification, smt-lemma]

    rule [chop-sum-left]:  chop ( chop ( X:Int ) +Int Y:Int ) => chop ( X +Int Y ) [simplification]
    rule [chop-sum-right]: chop ( X:Int +Int chop ( Y:Int ) ) => chop ( X +Int Y ) [simplification]

    rule [chop-no-overflow-add]:
      X:Int <=Int chop ( X +Int Y:Int ) => X +Int Y <Int pow256
      requires #rangeUInt(256, X) andBool #rangeUInt(256, Y)
      [simplification]

endmodule
