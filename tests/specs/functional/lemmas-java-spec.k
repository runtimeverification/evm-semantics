requires "../lemmas.k"

module VERIFICATION
    imports LEMMAS

    syntax StepSort ::= Map | ByteArray | Int | Bool
 // ------------------------------------------------

    syntax KItem ::= runLemma ( StepSort )
                   | doneLemma( StepSort )
 // --------------------------------------
    rule runLemma( T ) => doneLemma( T )

endmodule

module LEMMAS-SPEC
    imports VERIFICATION

    claim <k> runLemma ( #bufStrict( #ceil32(LEN) -Int LEN, 0 ) ) => doneLemma( #buf( #ceil32(LEN) -Int LEN, 0 ) ) ... </k>

endmodule
