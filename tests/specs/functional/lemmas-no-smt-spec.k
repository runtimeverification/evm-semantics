requires "../lemmas.k"

module VERIFICATION
    imports LEMMAS-HASKELL

    syntax StepSort ::= Int
 // -----------------------

    syntax KItem ::= runLemma ( StepSort )
                   | doneLemma( StepSort )
 // --------------------------------------
    rule runLemma( T ) => doneLemma( T )

endmodule

module LEMMAS-NO-SMT-SPEC
    imports VERIFICATION
 
 // Arithmetic simplification
 // -------------------------

    rule runLemma ( 5 +Int X ) => doneLemma ( X +Int 5 )
    rule runLemma ( X -Int 5 ) => doneLemma ( X +Int (0 -Int 5) )
    rule runLemma ( (X +Int 3) +Int 5 ) => doneLemma ( X +Int 8 )
    rule runLemma ( 3 +Int (X +Int 5) ) => doneLemma ( X +Int 8 )
    rule runLemma ( 5 -Int (X +Int 3) ) => doneLemma ( 2 -Int X )
    rule runLemma ( 5 +Int (3 +Int X) ) => doneLemma ( 8 +Int X )
    rule runLemma ( 5 +Int (3 -Int X) ) => doneLemma ( 8 -Int X )
    rule runLemma ( (5 -Int X) +Int 3 ) => doneLemma ( 8 -Int X )
    rule runLemma ( 5 -Int (3 +Int X) ) => doneLemma ( 2 -Int X )
    rule runLemma ( 5 -Int (3 -Int X) ) => doneLemma ( 2 +Int X )
    rule runLemma ( (X -Int 5) -Int 3 ) => doneLemma ( X -Int 8 )
    rule runLemma ( 5 &Int (3 &Int X) ) => doneLemma ( 1 &Int X )

endmodule
