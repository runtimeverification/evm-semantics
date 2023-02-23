requires "infinite-gas.md"
requires "lemmas/int-simplification.k"

module VERIFICATION
    imports INFINITE-GAS
    imports INT-SIMPLIFICATION

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

    claim <k> runLemma((VGas -Int #allBut64th(VGas +Int -2732)) +Int #allBut64th(VGas +Int -2732)) => doneLemma(VGas) ... </k>

    claim <k> runLemma(((VGas -Int #allBut64th(VGas +Int -9487)) +Int -9487) +Int #allBut64th(VGas +Int -9487)) => doneLemma(VGas +Int -9487) ... </k>

    claim <k> runLemma(((VGas -Int (#allBut64th(VGas +Int -2655) +Int 700)) +Int #allBut64th(VGas +Int -2655)) +Int -7244) => doneLemma(VGas +Int -7944) ... </k>

    claim <k> runLemma(X +Int (0 -Int ABI_wad)) => doneLemma(X -Int ABI_wad) ... </k>

    claim <k> runLemma(#memoryUsageUpdate(#memoryUsageUpdate(MEMORYUSED_CELL, 0, 32), 32, 32)) => doneLemma(#memoryUsageUpdate(MEMORYUSED_CELL, 32, 32)) ... </k>
      requires #rangeUInt(256, MEMORYUSED_CELL)

 // Infinite Gas simplifications
 // ----------------------------

    claim <k> runLemma(#gas(8) -Int 3) => doneLemma(#gas(5)) ... </k>

    claim <k> runLemma(#gas(G) -Int #gas(G')) => doneLemma(#gas(G -Int G')) ... </k>

    claim <k> runLemma(#gas((((((VGas +Int -1148) -Int G1) +Int -866) -Int G2) +Int -4337))) => doneLemma(#gas(((VGas -Int G1) -Int G2) +Int -6351)) ... </k>

    claim <k> runLemma(#gas((((VGas +Int -1259) -Int Csstore(ISTANBUL, 1, 1, Junk_0)) +Int -4339))) => doneLemma(#gas((VGas -Int Csstore(ISTANBUL, 1, 1, Junk_0)) +Int -5598)) ... </k>

    claim <k> runLemma(#gas(#gas(G1) +Int #allBut64th(G2 +Int -3454))) => doneLemma(#gas(G1 +Int #allBut64th(G2 +Int -3454))) ... </k> requires #rangeUInt(256, G2)

    claim <k> runLemma(#gas(#gas(G1 -Int G2) +Int #allBut64th(G3))) => doneLemma(#gas((G1 -Int G2) +Int #allBut64th(G3))) ... </k> requires 0 <Int G3
    claim <k> runLemma(#gas(#gas(G1 -Int G2) -Int #allBut64th(G3))) => doneLemma(#gas((G1 -Int G2) -Int #allBut64th(G3))) ... </k> requires 0 <Int G3 andBool G3 <Int #gas(G1 -Int G2)

    claim <k> runLemma(#gas(G) +Int (#allBut64th((VGas -Int Csstore(ISTANBUL, V1, V2, V3)) +Int -3232) +Int -3232)) => doneLemma(#gas(G +Int (#allBut64th((VGas -Int Csstore(ISTANBUL, V1, V2, V3)) +Int -3232) +Int -3232))) ... </k>
    claim <k> runLemma(#gas(G) +Int ((#allBut64th(VGas -Int Csstore(ISTANBUL, V1, V2, V3)) -Int Csstore(ISTANBUL, V1', V2', V3')) +Int -3232)) => doneLemma(#gas(G +Int ((#allBut64th(VGas -Int Csstore(ISTANBUL, V1, V2, V3)) -Int Csstore(ISTANBUL, V1', V2', V3')) +Int -3232))) ... </k>

    claim <k> runLemma(#gas(G) -Int Cmem(SCHED, #memoryUsageUpdate(MU, W0, 32))) => doneLemma(#gas(G -Int Cmem(SCHED, #memoryUsageUpdate(MU, W0, 32)))) ... </k>
           requires #rangeUInt(256, MU) andBool #rangeUInt(256, W0)

    claim <k> runLemma(#gas(G) -Int Gverylow < SCHED >) => doneLemma(#gas(G -Int Gverylow < SCHED >)) ... </k>

    claim <k> runLemma(#gas(G) -Int 3 *Int (DATA_LEN up/Int 32)) => doneLemma(#gas(G -Int 3 *Int (DATA_LEN up/Int 32))) ... </k> requires 0 <=Int DATA_LEN andBool DATA_LEN <Int pow16

    claim <k> runLemma (#gas(-271 -Int Cmem(ISTANBUL, #memoryUsageUpdate(5, 160, DATA_LEN))) -Int 3 *Int (DATA_LEN up/Int 32) +Int -3)
           => doneLemma(#gas(-271 -Int Cmem(ISTANBUL, #memoryUsageUpdate(5, 160, DATA_LEN)) -Int 3 *Int (DATA_LEN up/Int 32) +Int -3)) ... </k>
      requires 0 <=Int DATA_LEN andBool DATA_LEN <Int pow16

    claim <k> runLemma(  #gas( -271 -Int CMEM -Int 3 *Int ( DATA_LEN up/Int 32 ) -Int CMEM' +Int CMEM -Int Cmem ( ISTANBUL , #memoryUsageUpdate ( 5 , ( DATA_LEN +Int 31 ) /Int 32 *Int 32 +Int 160 , 32 ) ) +Int CMEM' +Int -122))
           => doneLemma( #gas( -271           -Int 3 *Int ( DATA_LEN up/Int 32 )                      -Int Cmem ( ISTANBUL , #memoryUsageUpdate ( 5 , ( DATA_LEN +Int 31 ) /Int 32 *Int 32 +Int 160 , 32 ) )            +Int -122)) ... </k>

    claim <k> runLemma( #gas(VGAS +Int -6113) +Int Cgascap(ISTANBUL, VGAS +Int -5413, VGAS +Int -5413, 700))
           => doneLemma(#gas((VGAS +Int Cgascap(ISTANBUL, VGAS +Int -5413, VGAS +Int -5413, 700)) +Int -6113)) ... </k>

    claim <k> runLemma( #gas(VGAS +Int -6113) +Int Cgascap(ISTANBUL, #gas(VGAS +Int -5413), #gas(VGAS +Int -5413), 700))
           => doneLemma(#gas((VGAS +Int Cgascap(ISTANBUL, VGAS +Int -5413, VGAS +Int -5413, 700)) +Int -6113)) ... </k>

    claim <k> runLemma( #gas((      #gas((VGAS -Int Cgascap(ISTANBUL, VGAS +Int -5413, VGAS +Int -5413, 700)) +Int -6113)
                               +Int Cgascap(ISTANBUL, #gas(VGAS +Int -5413), #gas(VGAS +Int -5413), 700))
                               +Int -1236
                            )
                      )
           => doneLemma(#gas(VGAS +Int -7349)) ... </k>

    claim <k> runLemma(       Cgascap(ISTANBUL, #gas(VGas +Int -2924), #gas(VGas +Int -2924), Cextra(ISTANBUL, ISEMPTY, VALUE, ISWARM))  )
           => doneLemma( #gas(Cgascap(ISTANBUL,     (VGas +Int -2924),     (VGas +Int -2924), Cextra(ISTANBUL, ISEMPTY, VALUE, ISWARM))) ) ... </k>

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

    claim <k> runLemma(3 <Int minInt(#gas(_VGas), 2)) => doneLemma(false) ... </k>
    claim <k> runLemma(2 <Int minInt(#gas(_VGas), 3)) => doneLemma(true ) ... </k>

    claim <k> runLemma(#gas(_G) -Int Csstore(_, _, _, _) <Int 2) => doneLemma(false) ... </k>
    claim <k> runLemma(minInt(#gas(_G), #gas(_G'')) +Int -2522 <Int Csstore(_, _, _, _)) => doneLemma(false) ... </k>

    claim <k> runLemma(#gas(_G) <Int #gas(_G' +Int 700))  => doneLemma(false) ... </k>
    claim <k> runLemma(#gas(_G' +Int 700) <=Int #gas(_G)) => doneLemma(true)  ... </k>

    claim <k> runLemma(#if _:Int ==Int 0 #then #gas(VGas -Int Csstore(_, _, _,_)) #else #gas(VGas +Int -344) #fi <Int 8)  => doneLemma(false) ... </k>
    claim <k> runLemma(8 <=Int #if _:Int ==Int 0 #then #gas(VGas -Int Csstore(_, _, _,_)) #else #gas(VGas +Int -344) #fi) => doneLemma(true)  ... </k>

    claim <k> runLemma(#if _:Int ==Int 0 #then #gas(VGas -Int Csstore(_, _, _,_)) #else #gas(VGas +Int -344) #fi <Int minInt(#if _ #then #gas(_) #else #gas(_) #fi, #gas(_)))  => doneLemma(false) ... </k>
    claim <k> runLemma(minInt(#if _ #then #gas(_) #else #gas(_) #fi, #gas(_)) <=Int #if _:Int ==Int 0 #then #gas(VGas -Int Csstore(_, _, _,_)) #else #gas(VGas +Int -344) #fi) => doneLemma(true)  ... </k>

    claim [Csstore-1]: <k> runLemma(9223372036854696114 -Int Csstore(LONDON, _, _, _) <Int 8) => doneLemma(false) ... </k>
    claim [Csstore-2]: <k> runLemma(8 <=Int 9223372036854763220 -Int Csstore(LONDON, _, _, _)) => doneLemma(true) ... </k>

    claim <k> runLemma(#allBut64th(#gas(_G)) <Int #gas(_G')) => doneLemma(false) ... </k>

    claim <k> runLemma(Gverylow < _ > <=Int #gas(_)) => doneLemma(true) ... </k>

    claim <k> runLemma(Gexp < SCHED > +Int Gexpbyte < SCHED > *Int ( log2Int ( W1 ) /Int 8 +Int 1 ) <=Int #gas(_)) => doneLemma(true)  ... </k> requires 0 <Int W1 andBool W1 <Int pow256
    claim <k> runLemma(#gas(_) <Int Gexp < SCHED > +Int Gexpbyte < SCHED > *Int ( log2Int ( W1 ) /Int 8 +Int 1 ))  => doneLemma(false) ... </k> requires 0 <Int W1 andBool W1 <Int pow256

    claim <k> runLemma(#gas(_) <Int 3 *Int (DATA_LEN up/Int 32) +Int 3) => doneLemma(false) ... </k> requires 0 <=Int DATA_LEN andBool DATA_LEN <Int pow16
    claim <k> runLemma(#gas(_) <Int         DATA_LEN up/Int 32        ) => doneLemma(false) ... </k> requires 0 <=Int DATA_LEN andBool DATA_LEN <Int pow16
    claim <k> runLemma(#gas(_) <Int         DATA_LEN                  ) => doneLemma(false) ... </k> requires 0 <=Int DATA_LEN andBool DATA_LEN <Int pow16

    claim <k> runLemma(0 <=Int 3 *Int (DATA_LEN up/Int 32))      => doneLemma(true) ... </k> requires 0 <=Int DATA_LEN andBool DATA_LEN <Int pow16
    claim <k> runLemma(3 *Int (DATA_LEN up/Int 32) <Int #gas(_)) => doneLemma(true) ... </k> requires 0 <=Int DATA_LEN andBool DATA_LEN <Int pow16

    claim <k> runLemma(#gas ( _ ) <Int Csload(_ , _) ) => doneLemma(false) ... </k> requires CONTRACT_ID =/=Int 1 andBool #rangeAddress(CONTRACT_ID)
    claim <k> runLemma(Csload(_ , _) <=Int #gas ( _) ) => doneLemma(true)  ... </k> requires CONTRACT_ID =/=Int 1 andBool #rangeAddress(CONTRACT_ID)

    claim <k> runLemma(Cgascap(ISTANBUL, #gas(_), #gas(_), 700) <Int 3) => doneLemma(false) ... </k>
    claim <k> runLemma(0 <=Int Cgascap(ISTANBUL, #gas(VGAS +Int -5413), #gas(VGAS +Int -5413), 700)) => doneLemma(true) ... </k>

endmodule
