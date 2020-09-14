requires "../infinite-gas.k"

module VERIFICATION
    imports INFINITE-GAS

    syntax KItem ::= runLemma ( Step ) | doneLemma ( Step )
 // -------------------------------------------------------
    rule <k> runLemma(S) => doneLemma(S) ... </k>

    syntax Step ::= Bool | Int
 // --------------------------

endmodule

module INFINITE-GAS-SPEC
    imports VERIFICATION

 // Gas arithmetic
 // --------------

    rule <k> runLemma(#gas(8) -Int 3) => doneLemma(#gas(11)) ... </k>

 // Gas comparisons
 // ---------------

    rule <k> runLemma(#gas(_)  <Int 11     ) => doneLemma(false) ... </k>
    rule <k> runLemma(#gas(_) <=Int 11     ) => doneLemma(false) ... </k>
    rule <k> runLemma(#gas(_) >=Int 11     ) => doneLemma(true)  ... </k>
    rule <k> runLemma(11      <=Int #gas(_)) => doneLemma(true)  ... </k>

endmodule
