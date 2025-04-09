requires "../evm.md"

module SLOAD-SUMMARY
    imports public EVM
    
    rule [SLOAD-SUMMARY-NOGAS-BERLIN]: <kevm>
           <k>
             ( #next [ SLOAD ] ~> .K => .K )
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
      requires ( notBool USEGAS_CELL:Bool )
      [priority(20), label(SLOAD-SUMMARY-NOGAS-BERLIN)]
    
    rule [SLOAD-SUMMARY-USEGAS-BERLIN]: <kevm>
           <k>
             ( #next [ SLOAD ] ~> .K => .K )
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
                   ( ( W0:Int => #lookup ( STORAGE_CELL:Map , W0:Int ) ) : WS:WordStack )
                 </wordStack>
                 <pc>
                   ( PC_CELL:Int => ( PC_CELL:Int +Int 1 ) )
                 </pc>
                 <gas>
                   ( GAS_CELL:Int => ( GAS_CELL:Int -Int #if #inStorage ( ACCESSEDSTORAGE_CELL:Map , ID_CELL:Int , W0:Int ) #then Gwarmstorageread < SCHEDULE_CELL:Schedule > #else Gcoldsload < SCHEDULE_CELL:Schedule > #fi ) )
                 </gas>
                 ...
               </callState>
               <substate>
                 <accessedStorage>
                   ( ACCESSEDSTORAGE_CELL:Map => ACCESSEDSTORAGE_CELL:Map [ ID_CELL:Int <- project:Set ( ACCESSEDSTORAGE_CELL:Map [ ID_CELL:Int ] orDefault .Set ~> .K ) |Set SetItem ( W0:Int ) ] )
                 </accessedStorage>
                 ...
               </substate>
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
      requires ( USEGAS_CELL:Bool
       andBool ( Ghasaccesslist << SCHEDULE_CELL:Schedule >>
       andBool ( #if #inStorage ( ACCESSEDSTORAGE_CELL:Map , ID_CELL:Int , W0:Int ) #then Gwarmstorageread < SCHEDULE_CELL:Schedule > #else Gcoldsload < SCHEDULE_CELL:Schedule > #fi <=Int GAS_CELL:Int
               )))
      [priority(20), label(SLOAD-SUMMARY-USEGAS-BERLIN)]
    
    rule [SLOAD-SUMMARY-USEGAS]: <kevm>
           <k>
             ( #next [ SLOAD ] ~> .K => .K )
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
                   ( ( W0:Int => #lookup ( STORAGE_CELL:Map , W0:Int ) ) : WS:WordStack )
                 </wordStack>
                 <pc>
                   ( PC_CELL:Int => ( PC_CELL:Int +Int 1 ) )
                 </pc>
                 <gas>
                   ( GAS_CELL:Int => ( GAS_CELL:Int -Int Gsload < SCHEDULE_CELL:Schedule > ) )
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
      requires ( USEGAS_CELL:Bool
       andBool ( ( notBool Ghasaccesslist << SCHEDULE_CELL:Schedule >> )
       andBool ( Gsload < SCHEDULE_CELL:Schedule > <=Int GAS_CELL:Int
               )))
      [priority(20), label(SLOAD-SUMMARY-USEGAS)]

endmodule