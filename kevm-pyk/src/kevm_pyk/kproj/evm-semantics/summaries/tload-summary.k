requires "../evm.md"

module TLOAD-SUMMARY
    imports public EVM
    
    rule [TLOAD-SUMMARY-USEGAS]: <kevm>
           <k>
             ( #next [ TLOAD ] ~> .K => .K )
             ~> _K_CELL:K
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
                   ( ( W0:Int => #lookup ( TRANSIENT_STORAGE_CELL:Map , W0:Int ) ) : _WS:WordStack )
                 </wordStack>
                 <pc>
                   ( PC_CELL:Int => ( PC_CELL:Int +Int 1 ) )
                 </pc>
                 <gas>
                   ( GAS_CELL:Int => ( GAS_CELL:Int -Int Gwarmstorageread < SCHEDULE_CELL:Schedule > ) )
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
                   <transientStorage>
                     TRANSIENT_STORAGE_CELL:Map
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
       andBool ( Gwarmstorageread < SCHEDULE_CELL:Schedule > <=Int GAS_CELL:Int
               ))
      [priority(20), label(TLOAD-SUMMARY-USEGAS)]
    
    rule [TLOAD-SUMMARY-NOGAS]: <kevm>
           <k>
             ( #next [ TLOAD ] ~> .K => .K )
             ~> _K_CELL:K
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
                   ( ( W0:Int => #lookup ( TRANSIENT_STORAGE_CELL:Map , W0:Int ) ) : _WS:WordStack )
                 </wordStack>
                 <pc>
                   ( PC_CELL:Int => ( PC_CELL:Int +Int 1 ) )
                 </pc>
                 <gas>
                   _GAS_CELL:Int
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
                   <transientStorage>
                     TRANSIENT_STORAGE_CELL:Map
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
      requires ( notBool USEGAS_CELL:Bool )
      [priority(20), label(TLOAD-SUMMARY-NOGAS)]

endmodule