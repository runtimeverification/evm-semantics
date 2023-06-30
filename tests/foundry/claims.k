requires "evm.md"
requires "foundry.md"

module RUN-LEMMA
    imports FOUNDRY

    syntax StepSort ::= Int
                      | Bool
 // ------------------------

    syntax KItem ::= runLemma ( StepSort )
                   | doneLemma( StepSort )
 // --------------------------------------

endmodule

module RUN-LEMMA-SPEC
    imports RUN-LEMMA

	claim [should-pass]: <k> runLemma ( 0 <Int 1 ) => doneLemma ( true ) ... </k>

	claim [should-not-pass]: <k> runLemma ( 2 <Int 1 ) => doneLemma ( true ) ... </k>
endmodule
