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
  // chop
  // ###########################################################################

  rule [chop-idempotent]:  chop(I) => I requires #rangeUInt( 256 , I ) [simplification]
  rule [chop-upper-bound]: 0 <=Int chop(_V)             => true        [simplification, smt-lemma]
  rule [chop-lower-bound]:         chop(_V) <Int pow256 => true        [simplification, smt-lemma]

  rule [chop-sum-left]:  chop ( chop ( X:Int ) +Int Y:Int ) => chop ( X +Int Y ) [simplification]
  rule [chop-sum-right]: chop ( X:Int +Int chop ( Y:Int ) ) => chop ( X +Int Y ) [simplification]

endmodule
