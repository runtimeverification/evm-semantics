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

    claim <k> runLemma(#gas(8) -Int 3) => doneLemma(#gas(5)) ... </k>

 // Gas comparisons
 // ---------------

    claim <k> runLemma(#gas(_)  <Int 11     ) => doneLemma(false) ... </k>
    claim <k> runLemma(#gas(_) <=Int 11     ) => doneLemma(false) ... </k>
    claim <k> runLemma(#gas(_) >=Int 11     ) => doneLemma(true)  ... </k>
    claim <k> runLemma(11      <=Int #gas(_)) => doneLemma(true)  ... </k>

    claim <k> runLemma(#gas(_) <Int (Cmem(_, _) +Int Csstore(_, _, _, _))) => doneLemma(false) ... </k>

    // Awaiting Haskell backend updates
    // claim <k> runLemma(#gas(_) <Int (I1 +Int (I2 /Int I3) *Int I4)) => doneLemma(false) ... </k> requires I1 <=Int pow256 andBool I2 <=Int pow256 andBool I3 =/=Int 0 andBool I3 <=Int pow256 andBool I4 <=Int pow256

    claim <k> runLemma(4822 <Int minInt(#gas(VGas +Int 4544) +Int (#gas(VGas +Int 4544) /Int 64), #gas(VGas +Int 3844))) => doneLemma(true) ... </k>

    claim <k> runLemma(3 <Int minInt(#gas(VGas), 2)) => doneLemma(false) ... </k>
    claim <k> runLemma(2 <Int minInt(#gas(VGas), 3)) => doneLemma(true ) ... </k>

    claim <k> runLemma(#gas(G) -Int #gas(G')) => doneLemma(#gas(G -Int G')) ... </k>

    claim <k> runLemma(#gas(G) -Int Csstore(_, _, _, _) <Int 2) => doneLemma(false) ... </k>
    claim <k> runLemma(minInt(#gas(G), #gas(G'')) +Int -2522 <Int Csstore(_, _, _, _)) => doneLemma(false) ... </k>

    claim <k> runLemma(#gas(G) <Int #gas(G' +Int 700))  => doneLemma(false) ... </k>
    claim <k> runLemma(#gas(G' +Int 700) <=Int #gas(G)) => doneLemma(true)  ... </k>

    claim <k> runLemma(#gas((((VGas +Int -1259) -Int Csstore(ISTANBUL, 1, 1, Junk_0)) +Int -4339))) => doneLemma(#gas((VGas -Int Csstore(ISTANBUL, 1, 1, Junk_0)) +Int -5598)) ... </k>

endmodule
