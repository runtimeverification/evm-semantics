requires "evm.md"
requires "lemmas/lemmas.k"

module VERIFICATION
    imports LEMMAS
    imports EVM

    syntax StepSort ::= Int | Bool
 // ------------------------------

    syntax KItem ::= runLemma ( StepSort ) [symbol(runLemma)]
                   | doneLemma( StepSort )
 // --------------------------------------
    rule <k> runLemma( T ) => doneLemma( T ) ... </k>

endmodule

module LEMMAS-NO-SMT-SPEC
    imports VERIFICATION

 // Arithmetic simplification
 // -------------------------

    claim [int-simpl-01]: <k> runLemma ( 5 +Int X )          => doneLemma ( X +Int 5          ) ... </k>
    claim [int-simpl-02]: <k> runLemma ( X -Int 5 )          => doneLemma ( X +Int (0 -Int 5) ) ... </k>
    claim [int-simpl-03]: <k> runLemma ( (X +Int 3) +Int 5 ) => doneLemma ( X +Int 8          ) ... </k>
    claim [int-simpl-04]: <k> runLemma ( 3 +Int (X +Int 5) ) => doneLemma ( X +Int 8          ) ... </k>
    claim [int-simpl-05]: <k> runLemma ( 5 -Int (X +Int 3) ) => doneLemma ( 2 -Int X          ) ... </k>
    claim [int-simpl-06]: <k> runLemma ( 5 +Int (3 +Int X) ) => doneLemma ( 8 +Int X          ) ... </k>
    claim [int-simpl-07]: <k> runLemma ( 5 +Int (3 -Int X) ) => doneLemma ( 8 -Int X          ) ... </k>
    claim [int-simpl-08]: <k> runLemma ( (5 -Int X) +Int 3 ) => doneLemma ( 8 -Int X          ) ... </k>
    claim [int-simpl-09]: <k> runLemma ( 5 -Int (3 +Int X) ) => doneLemma ( 2 -Int X          ) ... </k>
    claim [int-simpl-10]: <k> runLemma ( 5 -Int (3 -Int X) ) => doneLemma ( 2 +Int X          ) ... </k>
    claim [int-simpl-11]: <k> runLemma ( (X -Int 5) -Int 3 ) => doneLemma ( X -Int 8          ) ... </k>
    claim [int-simpl-12]: <k> runLemma ( 5 &Int (3 &Int X) ) => doneLemma ( 1 &Int X          ) ... </k>

 // Boolean simplification
 // ----------------------

    claim [bool-simpl-01]: <k> runLemma ( (B ==Bool false) ==Bool false ) => doneLemma ( B ) ... </k>

    // Awaiting Haskell backend updates
    claim [bool-simpl-02]: <k> runLemma ( bool2Word( B:Bool ) ==Int 1 )   => doneLemma ( B ==K true ) ... </k>
    claim [bool-simpl-03]: <k> runLemma ( 1 ==Int bool2Word( B:Bool ) )   => doneLemma ( B ==K true ) ... </k>

endmodule
