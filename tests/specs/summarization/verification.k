requires "edsl.md"
requires "lemmas/lemmas.k"

module VERIFICATION
    imports EDSL
    imports LEMMAS

    syntax StepSort ::= Map | Bytes | Int | Bool
 // --------------------------------------------

    syntax KItem ::= runLemma ( StepSort )
                   | doneLemma( StepSort )
 // --------------------------------------
    rule runLemma( T ) => doneLemma( T )

 // Some additional lemmas
 // ----------------------

    rule B:Bytes [ X:Int ] => #asInteger ( #range (B, X, 1) )
      requires X <=Int lengthBytes(B)
      [simplification(40)]

    rule B:Bytes [ START:Int := b"" ] => B
      requires 0 <=Int START andBool START <=Int lengthBytes(B)
      [simplification]

    // Conversion from bytes always yields a non-negative integer
    rule 0 <=Int #asInteger ( _ ) => true [simplification]

endmodule
