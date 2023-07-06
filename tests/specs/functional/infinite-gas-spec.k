requires "gas.md"
requires "lemmas/lemmas.k"

module VERIFICATION
    imports INFINITE-GAS
    imports LEMMAS

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

    claim [gas.arith.0]: (#if B #then (VGas -Int Csstore(ISTANBUL, V1, V2, V3)) +Int -435 #else (VGas -Int Csstore(ISTANBUL, V1, V2, V3)) +Int -4342 #fi)
           => ((VGas -Int Csstore(ISTANBUL, V1, V2, V3)) +Int #if B #then -435 #else -4342 #fi)

    claim [gas.arith.1]: ((VGas +Int -3844) -Int ((VGas -Int ((VGas +Int -4544) /Int 64)) +Int -3844)) => ((VGas +Int -4544) /Int 64) 

    claim [gas.arith.2]: ((VGas -Int #allBut64th(VGas +Int -2732)) +Int #allBut64th(VGas +Int -2732)) => (VGas) 

    claim [gas.arith.3]: (((VGas -Int #allBut64th(VGas +Int -9487)) +Int -9487) +Int #allBut64th(VGas +Int -9487)) => (VGas +Int -9487) 

    claim [gas.arith.4]: (((VGas -Int (#allBut64th(VGas +Int -2655) +Int 700)) +Int #allBut64th(VGas +Int -2655)) +Int -7244) => (VGas +Int -7944) 

    claim [gas.arith.5]: (X +Int (0 -Int ABI_wad)) => (X -Int ABI_wad) 

    claim [gas.arith.6]: (#memoryUsageUpdate(#memoryUsageUpdate(MEMORYUSED_CELL, 0, 32), 32, 32)) => (#memoryUsageUpdate(MEMORYUSED_CELL, 32, 32)) 
        requires #rangeUInt(256, MEMORYUSED_CELL)

 // Infinite Gas simplifications
 // ----------------------------

    claim [gas.inf.1]:  (#gas(8) -Gas 3) => (#gas(5)) 

    claim [gas.inf.2]:  (#gas(G) -Gas #gas(G')) => (#gas(G -Int G')) 

    claim [gas.inf.3]:  (#gas((((((VGas +Int -1148) -Int G1) +Int -866) -Int G2) +Int -4337))) => (#gas(((VGas -Int G1) -Int G2) +Int -6351)) 

    claim [gas.inf.4]:  (#gas((((VGas +Int -1259) -Int Csstore(ISTANBUL, 1, 1, Junk_0)) +Int -4339))) => (#gas((VGas -Int Csstore(ISTANBUL, 1, 1, Junk_0)) +Int -5598)) 

    claim [gas.inf.5]:  (#gas(G) +Gas (#allBut64th((VGas -Int Csstore(ISTANBUL, V1, V2, V3)) +Int -3232) +Int -3232)) => (#gas(G +Int (#allBut64th((VGas -Int Csstore(ISTANBUL, V1, V2, V3)) +Int -3232) +Int -3232))) 
    claim [gas.inf.6]:  (#gas(G) +Gas ((#allBut64th(VGas -Int Csstore(ISTANBUL, V1, V2, V3)) -Int Csstore(ISTANBUL, V1', V2', V3')) +Int -3232)) => (#gas(G +Int ((#allBut64th(VGas -Int Csstore(ISTANBUL, V1, V2, V3)) -Int Csstore(ISTANBUL, V1', V2', V3')) +Int -3232))) 

    claim [gas.inf.7]:  (#gas(G) -Gas Cmem(SCHED, #memoryUsageUpdate(MU, W0, 32))) => (#gas(G -Int Cmem(SCHED, #memoryUsageUpdate(MU, W0, 32)))) 
           requires #rangeUInt(256, MU) andBool #rangeUInt(256, W0)

    claim [gas.inf.8]:  (#gas(G) -Gas Gverylow < SCHED >) => (#gas(G -Int Gverylow < SCHED >)) 

    claim [gas.inf.9]:  (#gas(G) -Gas 3 *Int (DATA_LEN up/Int 32)) => (#gas(G -Int 3 *Int (DATA_LEN up/Int 32)))  requires 0 <=Int DATA_LEN andBool DATA_LEN <Int pow16

    claim [gas.inf.10]:  (#gas(-271 -Int Cmem(ISTANBUL, #memoryUsageUpdate(5, 160, DATA_LEN))) -Gas ((3 *Int (DATA_LEN up/Int 32) +Int 3)))
           => (#gas(-271 -Int Cmem(ISTANBUL, #memoryUsageUpdate(5, 160, DATA_LEN)) -Int (3 *Int (DATA_LEN up/Int 32) +Int 3))) 
      requires 0 <=Int DATA_LEN andBool DATA_LEN <Int pow16

    claim [gas.inf.11]: (  #gas( -271 -Int CMEM -Int 3 *Int ( DATA_LEN up/Int 32 ) -Int CMEM' +Int CMEM -Int Cmem ( ISTANBUL , #memoryUsageUpdate ( 5 , ( DATA_LEN +Int 31 ) /Int 32 *Int 32 +Int 160 , 32 ) ) +Int CMEM' +Int -122))
           => ( #gas( -271           -Int 3 *Int ( DATA_LEN up/Int 32 )                      -Int Cmem ( ISTANBUL , #memoryUsageUpdate ( 5 , ( DATA_LEN +Int 31 ) /Int 32 *Int 32 +Int 160 , 32 ) )            +Int -122)) 

    claim [gas.inf.12]: ( #gas(VGAS +Int -6113) +Gas Cgascap(ISTANBUL, VGAS +Int -5413, VGAS +Int -5413, 700))
           => (#gas((VGAS +Int Cgascap(ISTANBUL, VGAS +Int -5413, VGAS +Int -5413, 700)) +Int -6113)) 

    claim [gas.inf.13]: ( #gas(VGAS +Int -6113) +Gas Cgascap(ISTANBUL, #gas(VGAS +Int -5413), #gas(VGAS +Int -5413), 700))
           => (#gas((VGAS +Int Cgascap(ISTANBUL, VGAS +Int -5413, VGAS +Int -5413, 700)) +Int -6113)) 

    claim [gas.inf.14]: (       Cgascap(ISTANBUL, #gas(VGas +Int -2924), #gas(VGas +Int -2924), Cextra(ISTANBUL, ISEMPTY, VALUE, ISWARM))  )
           => ( #gas(Cgascap(ISTANBUL,     (VGas +Int -2924),     (VGas +Int -2924), Cextra(ISTANBUL, ISEMPTY, VALUE, ISWARM))) ) 

 // Infinite Gas comparisons
 // ------------------------

    claim [gas.comp.1]:  (#gas(_)  <Gas 11     ) => (false) 
    claim [gas.comp.2]:  (#gas(_) <=Gas 11     ) => (false) 
    claim [gas.comp.3]:  (11       <Gas #gas(_)) => (true)  
    claim [gas.comp.4]:  (11      <=Gas #gas(_)) => (true)  

    claim [gas.comp.5]:  (#gas(_) <Gas (Cmem(_, _) +Int Csstore(_, _, _, _))) => (false) 

    claim [gas.comp.6]:  (#gas(_) <Gas (I1 +Int (I2 /Int I3) *Int I4)) => (false)  requires I1 <=Int pow256 andBool I2 <=Int pow256 andBool I3 =/=Int 0 andBool I3 <=Int pow256 andBool I4 <=Int pow256

    claim [gas.comp.7]:  (4822 <Gas minGas(#gas(VGas +Int 4544) +Gas (#gas(VGas +Int 4544) /Gas 64), #gas(VGas +Int 3844))) => (true) 

    claim [gas.comp.8]:  (3 <Gas minGas(#gas(_VGas), 2)) => (true)  
    claim [gas.comp.9]:  (2 <Gas minGas(#gas(_VGas), 3)) => (true ) 

    claim [gas.comp.10]: (#gas(_G) -Gas Csstore(_, _, _, _) <Gas 2) => (false) 
    claim [gas.comp.11]: (minGas(#gas(_G), #gas(_G'')) +Gas -2522 <Gas Csstore(_, _, _, _)) => (false) 

    claim [gas.comp.12]: (#gas(_G) <Gas #gas(_G' +Int 700))  => (false) 
    claim [gas.comp.13]: (#gas(_G' +Int 700) <=Gas #gas(_G)) => (true)  

    claim [gas.comp.14]: (#if _:Int ==Int 0 #then #gas(VGas -Int Csstore(_, _, _,_)) #else #gas(VGas +Int -344) #fi <Gas 8)  => (false) 
    claim [gas.comp.15]: (8 <=Gas #if _:Int ==Int 0 #then #gas(VGas -Int Csstore(_, _, _,_)) #else #gas(VGas +Int -344) #fi) => (true)  

    claim [gas.comp.16]: (#if _:Int ==Int 0 #then #gas(VGas -Int Csstore(_, _, _,_)) #else #gas(VGas +Int -344) #fi <Gas minGas(#if _ #then #gas(_) #else #gas(_) #fi, #gas(_)))  => (false) 
    claim [gas.comp.17]: (minGas(#if _ #then #gas(_) #else #gas(_) #fi, #gas(_)) <=Gas #if _:Int ==Int 0 #then #gas(VGas -Int Csstore(_, _, _,_)) #else #gas(VGas +Int -344) #fi) => (true)  

    claim [Csstore-1]:   (9223372036854696114 -Int Csstore(LONDON, _, _, _) <Int 8) => (false) 
    claim [Csstore-2]:   (8 <=Int 9223372036854763220 -Int Csstore(LONDON, _, _, _)) => (true) 

    claim [gas.comp.18]: (#allBut64th(#gas(_G)) <Gas #gas(_G')) => (false) 

    claim [gas.comp.19]: (Gverylow < _ > <=Gas #gas(_)) => (true) 

    claim [gas.comp.20]: <k> runLemma(Gexp < SCHED > +Int Gexpbyte < SCHED > *Int ( log2Int ( W1 ) /Int 8 +Int 1 ) <=Gas #gas(_)) => doneLemma(true) ... </k>  requires 0 <Int W1 andBool W1 <Int pow256
    claim [gas.comp.21]: <k> runLemma(#gas(_) <Gas Gexp < SCHED > +Int Gexpbyte < SCHED > *Int ( log2Int ( W1) /Int 8 +Int 1 ))  => doneLemma(false)  ... </k> requires 0 <Int W1 andBool W1 <Int pow256

    claim [gas.comp.22]: (#gas(_) <Gas 3 *Int (DATA_LEN up/Int 32) +Int 3) => (false)  requires 0 <=Int DATA_LEN andBool DATA_LEN <Int pow16
    claim [gas.comp.23]: (#gas(_) <Gas         DATA_LEN up/Int 32        ) => (false)  requires 0 <=Int DATA_LEN andBool DATA_LEN <Int pow16
    claim [gas.comp.24]: (#gas(_) <Gas         DATA_LEN                  ) => (false)  requires 0 <=Int DATA_LEN andBool DATA_LEN <Int pow16

    claim [gas.comp.25]: (0 <=Int 3 *Int (DATA_LEN up/Int 32))      => (true)  requires 0 <=Int DATA_LEN andBool DATA_LEN <Int pow16
    claim [gas.comp.26]: (3 *Int (DATA_LEN up/Int 32) <Gas #gas(_)) => (true)  requires 0 <=Int DATA_LEN andBool DATA_LEN <Int pow16

    claim [gas.comp.27]: (#gas ( _ ) <Gas Csload(_ , _) ) => (false)  requires CONTRACT_ID =/=Int 1 andBool #rangeAddress(CONTRACT_ID)
    claim [gas.comp.28]: (Csload(_ , _) <=Gas #gas ( _) ) => (true)   requires CONTRACT_ID =/=Int 1 andBool #rangeAddress(CONTRACT_ID)

    claim [gas.comp.29]: (Cgascap(ISTANBUL, #gas(_), #gas(_), 700) <Gas 3) => (false) 
    claim [gas.comp.30]: (0 <=Gas Cgascap(ISTANBUL, #gas(VGAS +Int -5413), #gas(VGAS +Int -5413), 700)) => (true) 

endmodule
