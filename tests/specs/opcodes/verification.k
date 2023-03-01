requires "edsl.md"
requires "lemmas/int-simplification.k"

module VERIFICATION
    imports EDSL
    imports INT-SIMPLIFICATION

  // ########################
  // Placeholders
  // ########################

    // TODO: should these be here or in tests/specs/opcodes/create-spec.k?
    //       see comment at beginning of that file.
    syntax Int ::= "#memStart" [function]
                 | "#memWidth" [function]

    syntax Memory ::= "#mapWithCode" [function]

  // ########################
  // Buffer Reasoning
  // ########################

    syntax Bytes ::= "#generatedCode" [function]
 // --------------------------------------------

  // ########################
  // Arithmetic
  // ########################

    rule chop(I) => I  requires 0 <=Int I andBool I <Int pow256 [simplification]

    rule 0 <=Int #sizeWordStack ( _  , N ) => true                             requires 0  <=Int N [simplification, smt-lemma]
    rule         #sizeWordStack ( WS , N ) => N +Int #sizeWordStack ( WS , 0 ) requires N =/=Int 0 [simplification]
endmodule
