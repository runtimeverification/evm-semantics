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

 // Gas simplifications
 // -------------------

    claim <k> runLemma(#if B #then (VGas -Int Csstore(ISTANBUL, V1, V2, V3)) +Int -435 #else (VGas -Int Csstore(ISTANBUL, V1, V2, V3)) +Int -4342 #fi)
           => doneLemma((VGas -Int Csstore(ISTANBUL, V1, V2, V3)) +Int #if B #then -435 #else -4342 #fi)
          ...
          </k>

    claim <k> runLemma((VGas +Int -3844) -Int ((VGas -Int ((VGas +Int -4544) /Int 64)) +Int -3844)) => doneLemma((VGas +Int -4544) /Int 64) ... </k>

 // Infinite Gas simplifications
 // ----------------------------

    claim <k> runLemma(#gas(8) -Int 3) => doneLemma(#gas(5)) ... </k>

    claim <k> runLemma(#gas(G) -Int #gas(G')) => doneLemma(#gas(G -Int G')) ... </k>

    claim <k> runLemma(#gas((((((VGas +Int -1148) -Int G1) +Int -866) -Int G2) +Int -4337))) => doneLemma(#gas(((VGas -Int G1) -Int G2) +Int -6351)) ... </k>

    claim <k> runLemma(#gas((((VGas +Int -1259) -Int Csstore(ISTANBUL, 1, 1, Junk_0)) +Int -4339))) => doneLemma(#gas((VGas -Int Csstore(ISTANBUL, 1, 1, Junk_0)) +Int -5598)) ... </k>

    claim <k> runLemma(#gas(#gas(G1) +Int #allBut64th(G2 +Int -3454))) => doneLemma(#gas(G1 +Int #allBut64th(G2 +Int -3454))) ... </k>

    claim <k> runLemma(#gas(#gas(G1 -Int G2) +Int #allBut64th(G3))) => doneLemma(#gas((G1 -Int G2) +Int #allBut64th(G3))) ... </k> requires 0 <Int G3
    claim <k> runLemma(#gas(#gas(G1 -Int G2) -Int #allBut64th(G3))) => doneLemma(#gas((G1 -Int G2) -Int #allBut64th(G3))) ... </k> requires 0 <Int G3 andBool G3 <Int #gas(G1 -Int G2)

 // Infinite Gas comparisons
 // ------------------------

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

    claim <k> runLemma(#gas(G) -Int Csstore(_, _, _, _) <Int 2) => doneLemma(false) ... </k>
    claim <k> runLemma(minInt(#gas(G), #gas(G'')) +Int -2522 <Int Csstore(_, _, _, _)) => doneLemma(false) ... </k>

    claim <k> runLemma(#gas(G) <Int #gas(G' +Int 700))  => doneLemma(false) ... </k>
    claim <k> runLemma(#gas(G' +Int 700) <=Int #gas(G)) => doneLemma(true)  ... </k>

    claim <k> runLemma(#if _:Int ==Int 0 #then #gas(VGas -Int Csstore(_, _, _,_)) #else #gas(VGas +Int -344) #fi <Int 8)  => doneLemma(false) ... </k>
    claim <k> runLemma(8 <=Int #if _:Int ==Int 0 #then #gas(VGas -Int Csstore(_, _, _,_)) #else #gas(VGas +Int -344) #fi) => doneLemma(true)  ... </k>

    claim <k> runLemma(#if _:Int ==Int 0 #then #gas(VGas -Int Csstore(_, _, _,_)) #else #gas(VGas +Int -344) #fi <Int minInt(#if _ #then #gas(_) #else #gas(_) #fi, #gas(_)))  => doneLemma(false) ... </k>
    claim <k> runLemma(minInt(#if _ #then #gas(_) #else #gas(_) #fi, #gas(_)) <=Int #if _:Int ==Int 0 #then #gas(VGas -Int Csstore(_, _, _,_)) #else #gas(VGas +Int -344) #fi) => doneLemma(true)  ... </k>

endmodule
