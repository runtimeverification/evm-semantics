requires "evm-types.md"

module EVM-INT-SIMPLIFICATION
    imports EVM-INT-SIMPLIFICATION-HASKELL
endmodule

module EVM-INT-SIMPLIFICATION-HASKELL [symbolic]
    imports EVM-INT-SIMPLIFICATION-COMMON
endmodule

module EVM-INT-SIMPLIFICATION-COMMON
    imports INT
    imports BOOL
    imports EVM-TYPES
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

  rule [asWord-lb]: 0 <=Int #asWord(_WS)     => true [simplification, smt-lemma]
  rule [asWord-ub]: #asWord(_WS) <Int pow256 => true [simplification, smt-lemma]

  rule [asWord-lt]:
    #asWord ( BA ) <Int X => true
    requires 2 ^Int ( 8 *Int lengthBytes(BA) ) <=Int X
    [concrete(X), simplification]

  rule [asWord-lt-concat]:
    #asWord ( BA1 +Bytes BA2 ) <Int X => #asWord ( BA1 ) <Int ( X -Int #asWord ( BA2 ) ) /Int ( 2 ^Int ( 8 *Int lengthBytes ( BA2 ) ) )
    requires ( X -Int #asWord ( BA2 ) ) modInt ( 2 ^Int ( 8 *Int lengthBytes ( BA2 ) ) ) ==Int 0
    [concrete(BA2, X), simplification, preserves-definedness]

  rule [asWord-lt-range]:
    #asWord ( #range ( _:Bytes, S, W ) ) <Int X => true
    requires 0 <=Int S andBool 0 <=Int W
     andBool 2 ^Int ( 8 *Int W ) <=Int X
    [simplification, concrete(S, W, X), preserves-definedness]

  rule [lt-asWord-range]:
    X <Int #asWord ( #range ( B:Bytes, S, W ) ) => X <Int #asWord ( B )
    requires 0 <=Int S andBool 0 <=Int W
     andBool lengthBytes(B) ==Int S +Int W
     andBool #asWord ( B ) <Int 2 ^Int ( 8 *Int W )
    [simplification, concrete(X, S, W), preserves-definedness]

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

    rule [chop-no-overflow-add-l]: X:Int <=Int chop ( X +Int Y:Int ) => X +Int Y <Int pow256 requires #rangeUInt(256, X) andBool #rangeUInt(256, Y)                           [simplification]
    rule [chop-no-overflow-add-r]: X:Int <=Int chop ( Y +Int X:Int ) => X +Int Y <Int pow256 requires #rangeUInt(256, X) andBool #rangeUInt(256, Y)                           [simplification]
    rule [chop-no-overflow-mul-l]: X:Int <=Int chop ( X *Int Y:Int ) => X *Int Y <Int pow256 requires #rangeUInt(256, X) andBool #rangeUInt(256, Y)                           [simplification]
    rule [chop-no-overflow-mul-r]: X:Int <=Int chop ( Y *Int X:Int ) => X *Int Y <Int pow256 requires #rangeUInt(256, X) andBool #rangeUInt(256, Y)                           [simplification]

    rule [chop-no-overflow-mul-eq]:
      X ==Int chop ( X *Int Y ) /Int Y => X *Int Y <Int pow256
      requires #rangeUInt(256, X) andBool 0 <Int Y
      [simplification, comm, preserves-definedness]

    rule [chop-no-overflow-mul-eq-ml-l]:
      { X #Equals chop ( X *Int Y ) /Int Y } => { true #Equals X *Int Y <Int pow256 }
      requires #rangeUInt(256, X) andBool 0 <Int Y
      [simplification, preserves-definedness]

    rule [chop-no-overflow-mul-eq-ml-r]:
      { chop ( X *Int Y ) /Int Y #Equals X } => { true #Equals X *Int Y <Int pow256 }
      requires #rangeUInt(256, X) andBool 0 <Int Y
      [simplification, preserves-definedness]

endmodule
