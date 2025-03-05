requires "../evm.md"

module SUMMARY-TSTORE-2-SPEC
imports EVM
    
    
    rule [BASIC-BLOCK-4-TO-5]: <kevm>
           <k>
             ( #next [ TSTORE ] => #halt )
             ~> __K_CELL:K
           </k>
           <useGas>
             false
           </useGas>
           <ethereum>
             <evm>
               <statusCode>
                 ( __STATUSCODE_CELL:StatusCode => EVMC_STATIC_MODE_VIOLATION )
               </statusCode>
               <callState>
                 <id>
                   ID_CELL:Int
                 </id>
                 <wordStack>
                   ( __W0:Int : ( __W1:Int : __WS:WordStack ) )
                 </wordStack>
                 <gas>
                   ( __GAS_CELL:Int )
                 </gas>
                 <static>
                   ( _STATIC_CELL:Bool => true )
                 </static>
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
                   ...
                 </account>
                 DotAccountVar:AccountCellMap )
               </accounts>
               ...
             </network>
           </ethereum>
           ...
         </kevm>
      requires ( _STATIC_CELL:Bool
       andBool ( ( notBool <acctID>
          ID_CELL:Int
        </acctID> in_keys ( DotAccountVar:AccountCellMap ) )
               ))
      [priority(20), label(BASIC-BLOCK-4-TO-5)]
    
    rule [BASIC-BLOCK-3-TO-6]: <kevm>
           <k>
             ( #next [ TSTORE ] ~> .K => .K )
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
                   ( ( _W0:Int : ( _W1:Int : _WS:WordStack ) ) => _WS:WordStack )
                 </wordStack>
                 <pc>
                   ( _PC_CELL:Int => ( _PC_CELL:Int +Int 1 ) )
                 </pc>
                 <gas>
                   ( __GAS_CELL:Int )
                 </gas>
                 <static>
                   ( _STATIC_CELL:Bool => false )
                 </static>
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
                   <transientStorage>
                     ( _TRANSIENT_STORAGE_CELL:Map => _TRANSIENT_STORAGE_CELL:Map [ _W0:Int <- _W1:Int ] )
                   </transientStorage>
                   ...
                 </account>
                 DotAccountVar:AccountCellMap )
               </accounts>
               ...
             </network>
           </ethereum>
           ...
         </kevm>
      requires ( ( notBool _STATIC_CELL:Bool )
       andBool ( ( notBool <acctID>
          ID_CELL:Int
        </acctID> in_keys ( DotAccountVar:AccountCellMap ) )
               ))
      [priority(20), label(BASIC-BLOCK-3-TO-6)]

endmodule