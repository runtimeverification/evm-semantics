requires "../evm.md"

module SUMMARY-SLOAD-1-SPEC
imports EVM
    
    
    rule [BASIC-BLOCK-1-TO-3]: <kevm>
           <k>
             ( #next [ SLOAD ] ~> .K => .K )
             ~> __K_CELL:K
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
                   ( ( _W0:Int => #lookup ( _STORAGE_CELL:Map , _W0:Int ) ) : __WS:WordStack )
                 </wordStack>
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
             <network>
               <accounts>
                 ( <account>
                   <acctID>
                     ID_CELL:Int
                   </acctID>
                   <storage>
                     _STORAGE_CELL:Map
                   </storage>
                   ...
                 </account>
                 DotAccountVar:AccountCellMap )
               </accounts>
               ...
             </network>
           </ethereum>
           ...
         </kevm>
      requires ( notBool <acctID>
        ID_CELL:Int
      </acctID> in_keys ( DotAccountVar:AccountCellMap ) )
      [priority(20), label(BASIC-BLOCK-1-TO-3)]

endmodule