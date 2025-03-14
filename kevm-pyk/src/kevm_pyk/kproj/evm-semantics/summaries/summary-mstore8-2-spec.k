requires "../evm.md"
requires "../buf.md"

module SUMMARY-MSTORE8-2-SPEC
imports EVM
imports BUF
    
    
    rule [BASIC-BLOCK-1-TO-8]: <kevm>
           <k>
             ( #next [ MSTORE8 ] ~> .K => .K )
             ~> K_CELL:K
           </k>
           <useGas>
             false
           </useGas>
           <ethereum>
             <evm>
               <callState>
                 <wordStack>
                   ( ( W0:Int : ( W1:Int : WS:WordStack ) ) => WS:WordStack )
                 </wordStack>
                 <localMem>
                   ( LOCALMEM_CELL:Bytes => LOCALMEM_CELL:Bytes [ W0:Int := #buf ( 1 , ( W1:Int modInt 256 ) ) ] )
                 </localMem>
                 <pc>
                   ( PC_CELL:Int => ( PC_CELL:Int +Int 1 ) )
                 </pc>
                 <gas>
                    ( GAS_CELL:Int )
                 </gas>
                 ...
               </callState>
               ...
             </evm>
             ...
           </ethereum>
           ...
         </kevm>
      [priority(20), label(BASIC-BLOCK-1-TO-8)]

endmodule