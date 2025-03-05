requires "../evm.md"

module SUMMARY-MLOAD-1-SPEC
imports EVM
    
    
    rule [BASIC-BLOCK-1-TO-3]: <kevm>
           <k>
             ( #next [ MLOAD ] ~> .K => .K )
             ~> __K_CELL:K
           </k>
           <useGas>
             false
           </useGas>
           <ethereum>
             <evm>
               <callState>
                 <wordStack>
                   ( ( _W0:Int => #asWord ( #range ( _LOCALMEM_CELL:Bytes , _W0:Int , 32 ) ) ) : __WS:WordStack )
                 </wordStack>
                 <localMem>
                   _LOCALMEM_CELL:Bytes
                 </localMem>
                 <pc>
                   ( _PC_CELL:Int => ( _PC_CELL:Int +Int 1 ) )
                 </pc>
                 <gas>
                   ( __GAS_CELL:Int )
                 </gas>
                 ...
               </callState>
               ...
             </evm>
             ...
           </ethereum>
           ...
         </kevm>
      [priority(20), label(BASIC-BLOCK-1-TO-3)]

endmodule