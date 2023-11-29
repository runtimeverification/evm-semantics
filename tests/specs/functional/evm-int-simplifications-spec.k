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

endmodule

module EVM-INT-SIMPLIFICATIONS-SPEC
    imports VERIFICATION

 // up/Int
 // ------

    claim [upInt-01]: <k> runLemma ( ((X up/Int Y) *Int Y) <Int X +Int Z )
                           => doneLemma ( true ) ... </k>
                          requires 0 <Int Y andBool Y <=Int Z

    claim [upInt-refl-lt]: <k> runLemma ( ((X up/Int Y) *Int Y) <Int X )
                            => doneLemma ( false ) ... </k>
                           requires 0 <Int Y

endmodule
