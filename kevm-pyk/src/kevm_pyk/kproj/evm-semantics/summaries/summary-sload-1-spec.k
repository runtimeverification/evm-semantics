requires "../evm.md"

module SUMMARY-SLOAD-1-SPEC
imports EVM
    
    
    rule [BASIC-BLOCK-1-TO-3]: <kevm>
           <k>
             ( #next [ SLOAD ] ~> .K => .K )
             ~> K_CELL:K
           </k>
           <useGas>
             false
           </useGas>
           <ethereum>
             <evm>
               <callState>
                 <id>
                   ID_CELL:Int
                 </id>
                 <wordStack>
                   ( ( W0:Int => #lookup ( STORAGE_CELL:Map , W0:Int ) ) : WS:WordStack )
                 </wordStack>
                 <pc>
                   ( PC_CELL:Int => ( PC_CELL:Int +Int 1 ) )
                 </pc>
                 <gas>
                    GAS_CELL:Int 
                 </gas>
                 ...
               </callState>
               ...
             </evm>
             <network>
               <accounts>
                 <account>
                   <acctID>
                     ID_CELL:Int
                   </acctID>
                   <storage>
                     STORAGE_CELL:Map
                   </storage>
                   ...
                 </account>
                 ...
               </accounts>
               ...
             </network>
           </ethereum>
           ...
         </kevm>
       
      [priority(20), label(BASIC-BLOCK-1-TO-3)]

endmodule