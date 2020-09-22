requires "../lemmas.k"

module VERIFICATION
    imports LEMMAS

    syntax StepSort ::= Int | Bool
 // ------------------------------

    syntax KItem ::= runLemma ( StepSort )
                   | doneLemma( StepSort )
 // --------------------------------------
    rule <k> runLemma( T ) => doneLemma( T ) ... </k>

endmodule

module LEMMAS-NO-SMT-SPEC
    imports VERIFICATION
 
 // Arithmetic simplification
 // -------------------------

    rule <k> runLemma ( 5 +Int X )          => doneLemma ( X +Int 5          ) ... </k>
    rule <k> runLemma ( X -Int 5 )          => doneLemma ( X +Int (0 -Int 5) ) ... </k>
    rule <k> runLemma ( (X +Int 3) +Int 5 ) => doneLemma ( X +Int 8          ) ... </k>
    rule <k> runLemma ( 3 +Int (X +Int 5) ) => doneLemma ( X +Int 8          ) ... </k>
    rule <k> runLemma ( 5 -Int (X +Int 3) ) => doneLemma ( 2 -Int X          ) ... </k>
    rule <k> runLemma ( 5 +Int (3 +Int X) ) => doneLemma ( 8 +Int X          ) ... </k>
    rule <k> runLemma ( 5 +Int (3 -Int X) ) => doneLemma ( 8 -Int X          ) ... </k>
    rule <k> runLemma ( (5 -Int X) +Int 3 ) => doneLemma ( 8 -Int X          ) ... </k>
    rule <k> runLemma ( 5 -Int (3 +Int X) ) => doneLemma ( 2 -Int X          ) ... </k>
    rule <k> runLemma ( 5 -Int (3 -Int X) ) => doneLemma ( 2 +Int X          ) ... </k>
    rule <k> runLemma ( (X -Int 5) -Int 3 ) => doneLemma ( X -Int 8          ) ... </k>
    rule <k> runLemma ( 5 &Int (3 &Int X) ) => doneLemma ( 1 &Int X          ) ... </k>

 // Boolean simplification
 // ----------------------

    rule <k> runLemma ( (B ==Bool false) ==Bool false ) => doneLemma ( B )          ... </k>
    rule <k> runLemma ( bool2Word( B:Bool ) ==Int 1 )   => doneLemma ( B ==K true ) ... </k>
    rule <k> runLemma ( 1 ==Int bool2Word( B:Bool ) )   => doneLemma ( B ==K true ) ... </k>

endmodule
