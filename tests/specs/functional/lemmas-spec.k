requires "../lemmas.k"

module VERIFICATION
    imports LEMMAS

    syntax StepSort ::= Map
 // -----------------------

    syntax KItem ::= runLemma ( StepSort )
                   | doneLemma( StepSort )
 // --------------------------------------
    rule runLemma( T ) => doneLemma( T )

endmodule

module LEMMAS-SPEC
    imports VERIFICATION

 // Buffer write simplifications
 // ----------------------------

    rule <k> runLemma  ( M [ L := .WordStack ] [ N := WS:WordStack ] )
          => doneLemma ( M [ N := WS ]                               ) ... </k>

 // #range selection operation
 // --------------------------

endmodule

