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

    claim <k> runLemma(#gas(8) -Int 3) => doneLemma(#gas(11)) ... </k>

 // Gas comparisons
 // ---------------

    claim <k> runLemma(#gas(_)  <Int 11     ) => doneLemma(false) ... </k>
    claim <k> runLemma(#gas(_) <=Int 11     ) => doneLemma(false) ... </k>
    claim <k> runLemma(#gas(_) >=Int 11     ) => doneLemma(true)  ... </k>
    claim <k> runLemma(11      <=Int #gas(_)) => doneLemma(true)  ... </k>

    claim <k> runLemma(#gas(_) <Int (Cmem(_, _) +Int Csstore(_, _, _, _))) => doneLemma(false) ... </k>

    // Awaiting Haskell backend updates
    // claim <k> runLemma(#gas(_) <Int (I1 +Int (I2 /Int I3) *Int I4)) => doneLemma(false) ... </k> requires I1 <=Int pow256 andBool I2 <=Int pow256 andBool I3 =/=Int 0 andBool I3 <=Int pow256 andBool I4 <=Int pow256

endmodule
