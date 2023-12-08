requires "gas.md"
requires "lemmas/lemmas.k"

module VERIFICATION
    imports INFINITE-GAS
    imports LEMMAS
    imports EVM

    syntax KItem ::= runLemma ( Step ) | doneLemma ( Step )
 // -------------------------------------------------------
    rule <k> runLemma(S) => doneLemma(S) ... </k>

    syntax Step ::= Bool | Int | Gas
 // --------------------------------

endmodule

module INFINITE-GAS-SPEC
    imports VERIFICATION

 // Gas simplifications
 // -------------------

    claim [gas.arith.0]: <k> runLemma(#if B #then (VGas -Int Csstore(ISTANBUL, V1, V2, V3)) +Int -435 #else (VGas -Int Csstore(ISTANBUL, V1, V2, V3)) +Int -4342 #fi)
           => doneLemma((VGas -Int Csstore(ISTANBUL, V1, V2, V3)) +Int #if B #then -435 #else -4342 #fi)
          ...
          </k>

    claim [gas.arith.1]: <k> runLemma((VGas +Int -3844) -Int ((VGas -Int ((VGas +Int -4544) /Int 64)) +Int -3844)) => doneLemma((VGas +Int -4544) /Int 64) ... </k>

    claim [gas.arith.2]: <k> runLemma((VGas -Int #allBut64th(VGas +Int -2732)) +Int #allBut64th(VGas +Int -2732)) => doneLemma(VGas) ... </k>

    claim [gas.arith.3]: <k> runLemma(((VGas -Int #allBut64th(VGas +Int -9487)) +Int -9487) +Int #allBut64th(VGas +Int -9487)) => doneLemma(VGas +Int -9487) ... </k>

    claim [gas.arith.4]: <k> runLemma(((VGas -Int (#allBut64th(VGas +Int -2655) +Int 700)) +Int #allBut64th(VGas +Int -2655)) +Int -7244) => doneLemma(VGas +Int -7944) ... </k>

    claim [gas.arith.5]: <k> runLemma(X +Int (0 -Int ABI_wad)) => doneLemma(X -Int ABI_wad) ... </k>

    claim [gas.arith.6]: <k> runLemma(#memoryUsageUpdate(#memoryUsageUpdate(MEMORYUSED_CELL, 0, 32), 32, 32)) => doneLemma(#memoryUsageUpdate(MEMORYUSED_CELL, 32, 32)) ... </k>
        requires #rangeUInt(256, MEMORYUSED_CELL)

 // Infinite Gas simplifications
 // ----------------------------

    claim [gas.inf.1]:  <k> runLemma(#gas(8) -Gas 3) => doneLemma(#gas(5)) ... </k>

    claim [gas.inf.2]:  <k> runLemma(#gas(G) -Gas #gas(G')) => doneLemma(#gas(G -Int G')) ... </k>

    claim [gas.inf.3]:  <k> runLemma(#gas((((((VGas +Int -1148) -Int G1) +Int -866) -Int G2) +Int -4337))) => doneLemma(#gas(((VGas -Int G1) -Int G2) +Int -6351)) ... </k>

    claim [gas.inf.4]:  <k> runLemma(#gas((((VGas +Int -1259) -Int Csstore(ISTANBUL, 1, 1, Junk_0)) +Int -4339))) => doneLemma(#gas((VGas -Int Csstore(ISTANBUL, 1, 1, Junk_0)) +Int -5598)) ... </k>

    claim [gas.inf.5]:  <k> runLemma(#gas(G) +Gas (#allBut64th((VGas -Int Csstore(ISTANBUL, V1, V2, V3)) +Int -3232) +Int -3232)) => doneLemma(#gas(G +Int (#allBut64th((VGas -Int Csstore(ISTANBUL, V1, V2, V3)) +Int -3232) +Int -3232))) ... </k>
    claim [gas.inf.6]:  <k> runLemma(#gas(G) +Gas ((#allBut64th(VGas -Int Csstore(ISTANBUL, V1, V2, V3)) -Int Csstore(ISTANBUL, V1', V2', V3')) +Int -3232)) => doneLemma(#gas(G +Int ((#allBut64th(VGas -Int Csstore(ISTANBUL, V1, V2, V3)) -Int Csstore(ISTANBUL, V1', V2', V3')) +Int -3232))) ... </k>

    claim [gas.inf.7]:  <k> runLemma(#gas(G) -Gas Cmem(SCHED, #memoryUsageUpdate(MU, W0, 32))) => doneLemma(#gas(G -Int Cmem(SCHED, #memoryUsageUpdate(MU, W0, 32)))) ... </k>
           requires #rangeUInt(256, MU) andBool #rangeUInt(256, W0)

    claim [gas.inf.8]:  <k> runLemma(#gas(G) -Gas Gverylow < SCHED >) => doneLemma(#gas(G -Int Gverylow < SCHED >)) ... </k>

    claim [gas.inf.9]:  <k> runLemma(#gas(G) -Gas 3 *Int (DATA_LEN up/Int 32)) => doneLemma(#gas(G -Int 3 *Int (DATA_LEN up/Int 32))) ... </k> requires 0 <=Int DATA_LEN andBool DATA_LEN <Int pow16

    claim [gas.inf.10]: <k> runLemma (#gas(-271 -Int Cmem(ISTANBUL, #memoryUsageUpdate(5, 160, DATA_LEN))) -Gas ((3 *Int (DATA_LEN up/Int 32) +Int 3)))
           => doneLemma(#gas(-271 -Int Cmem(ISTANBUL, #memoryUsageUpdate(5, 160, DATA_LEN)) -Int (3 *Int (DATA_LEN up/Int 32) +Int 3))) ... </k>
      requires 0 <=Int DATA_LEN andBool DATA_LEN <Int pow16

    claim [gas.inf.11]: <k> runLemma(  #gas( -271 -Int CMEM -Int 3 *Int ( DATA_LEN up/Int 32 ) -Int CMEM' +Int CMEM -Int Cmem ( ISTANBUL , #memoryUsageUpdate ( 5 , ( DATA_LEN +Int 31 ) /Int 32 *Int 32 +Int 160 , 32 ) ) +Int CMEM' +Int -122))
           => doneLemma( #gas( -271           -Int 3 *Int ( DATA_LEN up/Int 32 )                      -Int Cmem ( ISTANBUL , #memoryUsageUpdate ( 5 , ( DATA_LEN +Int 31 ) /Int 32 *Int 32 +Int 160 , 32 ) )            +Int -122)) ... </k>

    claim [gas.inf.12]: <k> runLemma( #gas(VGAS +Int -6113) +Gas Cgascap(ISTANBUL, VGAS +Int -5413, VGAS +Int -5413, 700))
           => doneLemma(#gas((VGAS +Int Cgascap(ISTANBUL, VGAS +Int -5413, VGAS +Int -5413, 700)) +Int -6113)) ... </k>

    claim [gas.inf.13]: <k> runLemma( #gas(VGAS +Int -6113) +Gas Cgascap(ISTANBUL, #gas(VGAS +Int -5413), #gas(VGAS +Int -5413), 700))
           => doneLemma(#gas((VGAS +Int Cgascap(ISTANBUL, VGAS +Int -5413, VGAS +Int -5413, 700)) +Int -6113)) ... </k>

    claim [gas.inf.14]: <k> runLemma(       Cgascap(ISTANBUL, #gas(VGas +Int -2924), #gas(VGas +Int -2924), Cextra(ISTANBUL, ISEMPTY, VALUE, ISWARM))  )
           => doneLemma( #gas(Cgascap(ISTANBUL,     (VGas +Int -2924),     (VGas +Int -2924), Cextra(ISTANBUL, ISEMPTY, VALUE, ISWARM))) ) ... </k>

 // Infinite Gas comparisons
 // ------------------------

    claim [gas.comp.1]:  <k> runLemma(#gas(_)  <Gas 11     ) => doneLemma(false) ... </k>
    claim [gas.comp.2]:  <k> runLemma(#gas(_) <=Gas 11     ) => doneLemma(false) ... </k>
    claim [gas.comp.3]:  <k> runLemma(11       <Gas #gas(_)) => doneLemma(true) ... </k>
    claim [gas.comp.4]:  <k> runLemma(11      <=Gas #gas(_)) => doneLemma(true) ... </k>

    claim [gas.comp.5]:  <k> runLemma(#gas(_) <Gas (Cmem(_, _) +Int Csstore(_, _, _, _))) => doneLemma(false) ... </k>

    claim [gas.comp.6]:  <k> runLemma(#gas(_) <Gas (I1 +Int (I2 /Int I3) *Int I4)) => doneLemma(false) ... </k> requires I1 <=Int pow256 andBool I2 <=Int pow256 andBool I3 =/=Int 0 andBool I3 <=Int pow256 andBool I4 <=Int pow256

    claim [gas.comp.7]:  <k> runLemma(4822 <Gas minGas(#gas(VGas +Int 4544) +Gas (#gas(VGas +Int 4544) /Gas 64), #gas(VGas +Int 3844))) => doneLemma(true) ... </k>

    claim [gas.comp.8]:  <k> runLemma(3 <Gas minGas(#gas(_VGas), 2)) => doneLemma(true) ... </k>
    claim [gas.comp.9]:  <k> runLemma(2 <Gas minGas(#gas(_VGas), 3)) => doneLemma(true ) ... </k>

    claim [gas.comp.10]: <k> runLemma(#gas(_G) -Gas Csstore(_, _, _, _) <Gas 2) => doneLemma(false) ... </k>
    claim [gas.comp.11]: <k> runLemma(minGas(#gas(_G), #gas(_G'')) +Gas -2522 <Gas Csstore(_, _, _, _)) => doneLemma(false) ... </k>

    claim [gas.comp.12]: <k> runLemma(#gas(_G) <Gas #gas(_G' +Int 700))  => doneLemma(false) ... </k>
    claim [gas.comp.13]: <k> runLemma(#gas(_G' +Int 700) <=Gas #gas(_G)) => doneLemma(true) ... </k>

    claim [gas.comp.14]: <k> runLemma(#if _:Int ==Int 0 #then #gas(VGas -Int Csstore(_, _, _,_)) #else #gas(VGas +Int -344) #fi <Gas 8)  => doneLemma(false) ... </k>
    claim [gas.comp.15]: <k> runLemma(8 <=Gas #if _:Int ==Int 0 #then #gas(VGas -Int Csstore(_, _, _,_)) #else #gas(VGas +Int -344) #fi) => doneLemma(true) ... </k>

    claim [gas.comp.16]: <k> runLemma(#if _:Int ==Int 0 #then #gas(VGas -Int Csstore(_, _, _,_)) #else #gas(VGas +Int -344) #fi <Gas minGas(#if _ #then #gas(_) #else #gas(_) #fi, #gas(_)))  => doneLemma(false) ... </k>
    claim [gas.comp.17]: <k> runLemma(minGas(#if _ #then #gas(_) #else #gas(_) #fi, #gas(_)) <=Gas #if _:Int ==Int 0 #then #gas(VGas -Int Csstore(_, _, _,_)) #else #gas(VGas +Int -344) #fi) => doneLemma(true) ... </k>

    claim [Csstore-1]:   <k> runLemma(9223372036854696114 -Int Csstore(LONDON, _, _, _) <Int 8) => doneLemma(false) ... </k>
    claim [Csstore-2]:   <k> runLemma(8 <=Int 9223372036854763220 -Int Csstore(LONDON, _, _, _)) => doneLemma(true) ... </k>

    claim [gas.comp.18]: <k> runLemma(#allBut64th(#gas(_G)) <Gas #gas(_G')) => doneLemma(false) ... </k>

    claim [gas.comp.19]: <k> runLemma(Gverylow < _ > <=Gas #gas(_)) => doneLemma(true) ... </k>

    claim [gas.comp.20]: <k> runLemma(Gexp < SCHED > +Int Gexpbyte < SCHED > *Int ( log2Int ( W1 ) /Int 8 +Int 1 ) <=Gas #gas(_)) => doneLemma(true)  ... </k> requires 0 <Int W1 andBool W1 <Int pow256
    claim [gas.comp.21]: <k> runLemma(#gas(_) <Gas Gexp < SCHED > +Int Gexpbyte < SCHED > *Int ( log2Int ( W1 ) /Int 8 +Int 1 ))  => doneLemma(false) ... </k> requires 0 <Int W1 andBool W1 <Int pow256

    claim [gas.comp.22]: <k> runLemma(#gas(_) <Gas 3 *Int (DATA_LEN up/Int 32) +Int 3) => doneLemma(false) ... </k> requires 0 <=Int DATA_LEN andBool DATA_LEN <Int pow16
    claim [gas.comp.23]: <k> runLemma(#gas(_) <Gas         DATA_LEN up/Int 32        ) => doneLemma(false) ... </k> requires 0 <=Int DATA_LEN andBool DATA_LEN <Int pow16
    claim [gas.comp.24]: <k> runLemma(#gas(_) <Gas         DATA_LEN                  ) => doneLemma(false) ... </k> requires 0 <=Int DATA_LEN andBool DATA_LEN <Int pow16

    claim [gas.comp.25]: <k> runLemma(0 <=Int 3 *Int (DATA_LEN up/Int 32))      => doneLemma(true) ... </k> requires 0 <=Int DATA_LEN andBool DATA_LEN <Int pow16
    claim [gas.comp.26]: <k> runLemma(3 *Int (DATA_LEN up/Int 32) <Gas #gas(_)) => doneLemma(true) ... </k> requires 0 <=Int DATA_LEN andBool DATA_LEN <Int pow16

    claim [gas.comp.27]: <k> runLemma(#gas ( _ ) <Gas Csload(_ , _) ) => doneLemma(false) ... </k> requires CONTRACT_ID =/=Int 1 andBool #rangeAddress(CONTRACT_ID)
    claim [gas.comp.28]: <k> runLemma(Csload(_ , _) <=Gas #gas ( _) ) => doneLemma(true)  ... </k> requires CONTRACT_ID =/=Int 1 andBool #rangeAddress(CONTRACT_ID)

    claim [gas.comp.29]: <k> runLemma(Cgascap(ISTANBUL, #gas(_), #gas(_), 700) <Gas 3) => doneLemma(false) ... </k>
    claim [gas.comp.30]: <k> runLemma(0 <=Gas Cgascap(ISTANBUL, #gas(VGAS +Int -5413), #gas(VGAS +Int -5413), 700)) => doneLemma(true) ... </k>

endmodule
