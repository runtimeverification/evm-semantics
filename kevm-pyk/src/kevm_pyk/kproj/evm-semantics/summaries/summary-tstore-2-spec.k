requires "../evm.md"

module SUMMARY-TSTORE-2-SPEC
imports EVM
    
    
    rule [BASIC-BLOCK-4-TO-5]: <kevm>
           <k>
             ( #next [ TSTORE ] => #halt )
             ~> K_CELL:K
           </k>
           <useGas>
             false
           </useGas>
           <ethereum>
             <evm>
               <statusCode>
                 ( STATUSCODE_CELL:StatusCode => EVMC_STATIC_MODE_VIOLATION )
               </statusCode>
               <callState>
                 <id>
                   ID_CELL:Int
                 </id>
                 <wordStack>
                   ( W0:Int : ( W1:Int : WS:WordStack ) )
                 </wordStack>
                 <gas>
                   ( GAS_CELL:Int )
                 </gas>
                 <static>
                   ( STATIC_CELL:Bool => true )
                 </static>
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
                   ...
                 </account>
                 ...
               </accounts>
               ...
             </network>
           </ethereum>
           ...
         </kevm>
      requires ( STATIC_CELL:Bool
       andBool ( ( notBool <acctID>
          ID_CELL:Int
        </acctID> in_keys ( DotAccountVar:AccountCellMap ) )
               ))
      [priority(20), label(BASIC-BLOCK-4-TO-5)]
    
    rule [BASIC-BLOCK-3-TO-6]: <kevm>
           <k>
             ( #next [ TSTORE ] ~> .K => .K )
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
                   ( ( W0:Int : ( W1:Int : WS:WordStack ) ) => WS:WordStack )
                 </wordStack>
                 <pc>
                   ( PC_CELL:Int => ( PC_CELL:Int +Int 1 ) )
                 </pc>
                 <gas>
                   ( GAS_CELL:Int )
                 </gas>
                 <static>
                   ( STATIC_CELL:Bool => false )
                 </static>
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
                   <transientStorage>
                     ( TRANSIENT_STORAGE_CELL:Map => TRANSIENT_STORAGE_CELL:Map [ W0:Int <- W1:Int ] )
                   </transientStorage>
                   ...
                 </account>
                 ...
               </accounts>
               ...
             </network>
           </ethereum>
           ...
         </kevm>
      requires ( ( notBool STATIC_CELL:Bool )
       andBool ( ( notBool <acctID>
          ID_CELL:Int
        </acctID> in_keys ( DotAccountVar:AccountCellMap ) )
               ))
      [priority(20), label(BASIC-BLOCK-3-TO-6)]

endmodule