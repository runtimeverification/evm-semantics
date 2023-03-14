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

    rule N &Int maxUInt256 => N  requires #rangeUInt(256, N) [simplification]
    rule maxUInt256 &Int N => N  requires #rangeUInt(256, N) [simplification]
    rule N &Int maxUInt248 => N  requires #rangeUInt(248, N) [simplification]
    rule maxUInt248 &Int N => N  requires #rangeUInt(248, N) [simplification]
    rule N &Int maxUInt240 => N  requires #rangeUInt(240, N) [simplification]
    rule maxUInt240 &Int N => N  requires #rangeUInt(240, N) [simplification]
    rule N &Int maxUInt232 => N  requires #rangeUInt(232, N) [simplification]
    rule maxUInt232 &Int N => N  requires #rangeUInt(232, N) [simplification]
    rule N &Int maxUInt224 => N  requires #rangeUInt(224, N) [simplification]
    rule maxUInt224 &Int N => N  requires #rangeUInt(224, N) [simplification]
    rule N &Int maxUInt216 => N  requires #rangeUInt(216, N) [simplification]
    rule maxUInt216 &Int N => N  requires #rangeUInt(216, N) [simplification]
    rule N &Int maxUInt208 => N  requires #rangeUInt(208, N) [simplification]
    rule maxUInt208 &Int N => N  requires #rangeUInt(208, N) [simplification]
    rule N &Int maxUInt200 => N  requires #rangeUInt(200, N) [simplification]
    rule maxUInt200 &Int N => N  requires #rangeUInt(200, N) [simplification]
    rule N &Int maxUInt192 => N  requires #rangeUInt(192, N) [simplification]
    rule maxUInt192 &Int N => N  requires #rangeUInt(192, N) [simplification]
    rule N &Int maxUInt184 => N  requires #rangeUInt(184, N) [simplification]
    rule maxUInt184 &Int N => N  requires #rangeUInt(184, N) [simplification]
    rule N &Int maxUInt176 => N  requires #rangeUInt(176, N) [simplification]
    rule maxUInt176 &Int N => N  requires #rangeUInt(176, N) [simplification]
    rule N &Int maxUInt168 => N  requires #rangeUInt(168, N) [simplification]
    rule maxUInt168 &Int N => N  requires #rangeUInt(168, N) [simplification]
    rule N &Int maxUInt160 => N  requires #rangeUInt(160, N) [simplification]
    rule maxUInt160 &Int N => N  requires #rangeUInt(160, N) [simplification]
    rule N &Int maxUInt152 => N  requires #rangeUInt(152, N) [simplification]
    rule maxUInt152 &Int N => N  requires #rangeUInt(152, N) [simplification]
    rule N &Int maxUInt144 => N  requires #rangeUInt(144, N) [simplification]
    rule maxUInt144 &Int N => N  requires #rangeUInt(144, N) [simplification]
    rule N &Int maxUInt136 => N  requires #rangeUInt(136, N) [simplification]
    rule maxUInt136 &Int N => N  requires #rangeUInt(136, N) [simplification]
    rule N &Int maxUInt128 => N  requires #rangeUInt(128, N) [simplification]
    rule maxUInt128 &Int N => N  requires #rangeUInt(128, N) [simplification]
    rule N &Int maxUInt120 => N  requires #rangeUInt(120, N) [simplification]
    rule maxUInt120 &Int N => N  requires #rangeUInt(120, N) [simplification]
    rule N &Int maxUInt112 => N  requires #rangeUInt(112, N) [simplification]
    rule maxUInt112 &Int N => N  requires #rangeUInt(112, N) [simplification]
    rule N &Int maxUInt104 => N  requires #rangeUInt(104, N) [simplification]
    rule maxUInt104 &Int N => N  requires #rangeUInt(104, N) [simplification]
    rule N &Int maxUInt96  => N  requires #rangeUInt(96,  N) [simplification]
    rule maxUInt96 &Int N  => N  requires #rangeUInt(96,  N) [simplification]
    rule N &Int maxUInt88  => N  requires #rangeUInt(88,  N) [simplification]
    rule maxUInt88 &Int N  => N  requires #rangeUInt(88,  N) [simplification]
    rule N &Int maxUInt80  => N  requires #rangeUInt(80,  N) [simplification]
    rule maxUInt80 &Int N  => N  requires #rangeUInt(80,  N) [simplification]
    rule N &Int maxUInt72  => N  requires #rangeUInt(72,  N) [simplification]
    rule maxUInt72 &Int N  => N  requires #rangeUInt(72,  N) [simplification]
    rule N &Int maxUInt64  => N  requires #rangeUInt(64,  N) [simplification]
    rule maxUInt64 &Int N  => N  requires #rangeUInt(64,  N) [simplification]
    rule N &Int maxUInt56  => N  requires #rangeUInt(56,  N) [simplification]
    rule maxUInt56 &Int N  => N  requires #rangeUInt(56,  N) [simplification]
    rule N &Int maxUInt48  => N  requires #rangeUInt(48,  N) [simplification]
    rule maxUInt48 &Int N  => N  requires #rangeUInt(48,  N) [simplification]
    rule N &Int maxUInt40  => N  requires #rangeUInt(40,  N) [simplification]
    rule maxUInt40 &Int N  => N  requires #rangeUInt(40,  N) [simplification]
    rule N &Int maxUInt32  => N  requires #rangeUInt(32,  N) [simplification]
    rule maxUInt32 &Int N  => N  requires #rangeUInt(32,  N) [simplification]
    rule N &Int maxUInt24  => N  requires #rangeUInt(24,  N) [simplification]
    rule maxUInt24 &Int N  => N  requires #rangeUInt(24,  N) [simplification]
    rule N &Int maxUInt16  => N  requires #rangeUInt(16,  N) [simplification]
    rule maxUInt16 &Int N  => N  requires #rangeUInt(16,  N) [simplification]
    rule N &Int maxUInt8   => N  requires #rangeUInt(8,   N) [simplification]
    rule maxUInt8 &Int N   => N  requires #rangeUInt(8,   N) [simplification]

    rule 0 <=Int (X |Int Y) => true requires 0 <=Int X andBool 0 <=Int Y [simplification]
    rule 0 <=Int (X &Int Y) => true requires 0 <=Int X andBool 0 <=Int Y [simplification]

    rule (X &Int Y) <Int Z      => true requires 0 <=Int X andBool 0 <=Int Y andBool (X <Int Z orBool Y <Int Z)          [simplification]
    rule (X |Int Y) <Int pow256 => true requires 0 <=Int X andBool 0 <=Int Y andBool X <Int pow256 andBool Y <Int pow256 [simplification]

    rule maxUInt160 &Int (X |Int (notMaxUInt160 &Int Y:Int)) => X requires #rangeUInt(160, X) andBool 0 <=Int Y [simplification]

endmodule