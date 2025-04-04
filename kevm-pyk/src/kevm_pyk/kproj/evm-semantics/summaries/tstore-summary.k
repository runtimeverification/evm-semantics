requires "../evm.md"

module TSTORE-SUMMARY
    imports public EVM
    
    rule [TSTORE-SUMMARY-0]: <kevm>
           <k>
             ( #next [ TSTORE ] => #halt )
             ~> K_CELL:K
           </k>
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
                   GAS_CELL:Int
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
      requires STATIC_CELL:Bool
      [priority(20), label(TSTORE-SUMMARY-0)]
    
    rule [TSTORE-SUMMARY-1]: <kevm>
           <k>
             ( #next [ TSTORE ] ~> .K => .K )
             ~> K_CELL:K
           </k>
           <schedule>
             SCHEDULE_CELL:Schedule
           </schedule>
           <useGas>
             ( USEGAS_CELL:Bool => true )
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
                   ( GAS_CELL:Int => ( GAS_CELL:Int -Int Gwarmstoragedirtystore < SCHEDULE_CELL:Schedule > ) )
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
      requires ( USEGAS_CELL:Bool
       andBool ( ( notBool STATIC_CELL:Bool )
       andBool ( Gwarmstoragedirtystore < SCHEDULE_CELL:Schedule > <=Int GAS_CELL:Int
               )))
      [priority(20), label(TSTORE-SUMMARY-1)]
    
    rule [TSTORE-SUMMARY-2]: <kevm>
           <k>
             ( #next [ TSTORE ] ~> .K => .K )
             ~> K_CELL:K
           </k>
           <useGas>
             ( USEGAS_CELL:Bool => false )
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
                   GAS_CELL:Int
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
       andBool ( ( notBool USEGAS_CELL:Bool )
               ))
      [priority(20), label(TSTORE-SUMMARY-2)]

endmodule