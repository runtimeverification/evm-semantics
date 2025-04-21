requires "../evm.md"

module SSTORE-SUMMARY
    imports public EVM
    
    rule [SSTORE-SUMMARY-NOGAS-BERLIN]: <kevm>
           <k>
             ( #next [ SSTORE ] ~> .K => .K )
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
                   ( ( W0:Int : ( W1:Int : WS:WordStack ) ) => WS:WordStack )
                 </wordStack>
                 <pc>
                   ( PC_CELL:Int => ( PC_CELL:Int +Int 1 ) )
                 </pc>
                 <gas>
                   _GAS_CELL:Int
                 </gas>
                 <static>
                   false
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
                   <storage>
                     ( STORAGE_CELL:Map => STORAGE_CELL:Map [ W0:Int <- W1:Int ] )
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
      [priority(20), label(SSTORE-SUMMARY-NOGAS-BERLIN)]
    
    rule [SSTORE-SUMMARY-USEGAS-BERLIN]: <kevm>
           <k>
             ( #next [ SSTORE ] ~> .K => .K )
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
                   ( ( W0:Int : ( W1:Int : WS:WordStack ) ) => WS:WordStack )
                 </wordStack>
                 <pc>
                   ( PC_CELL:Int => ( PC_CELL:Int +Int 1 ) )
                 </pc>
                 <gas>
                   ( GAS_CELL:Int => ( ( GAS_CELL:Int -Int Csstore ( SCHEDULE_CELL:Schedule , W1:Int , #lookup ( STORAGE_CELL:Map , W0:Int ) , #lookup ( ORIG_STORAGE_CELL:Map , W0:Int ) ) ) -Int #if #inStorage ( ACCESSEDSTORAGE_CELL:Map , ID_CELL:Int , W0:Int ) #then 0 #else Gcoldsload < SCHEDULE_CELL:Schedule > #fi ) )
                 </gas>
                 <static>
                   false
                 </static>
                 ...
               </callState>
               <substate>
                 <refund>
                   ( REFUND_CELL:Int => ( REFUND_CELL:Int +Int Rsstore ( SCHEDULE_CELL:Schedule , W1:Int , #lookup ( STORAGE_CELL:Map , W0:Int ) , #lookup ( ORIG_STORAGE_CELL:Map , W0:Int ) ) ) )
                 </refund>
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
                     ( STORAGE_CELL:Map => STORAGE_CELL:Map [ W0:Int <- W1:Int ] )
                   </storage>
                   <origStorage>
                     ORIG_STORAGE_CELL:Map
                   </origStorage>
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
       andBool ( Csstore ( SCHEDULE_CELL:Schedule , W1:Int , #lookup ( STORAGE_CELL:Map , W0:Int ) , #lookup ( ORIG_STORAGE_CELL:Map , W0:Int ) ) <=Int GAS_CELL:Int
       andBool ( #if #inStorage ( ACCESSEDSTORAGE_CELL:Map , ID_CELL:Int , W0:Int ) #then 0 #else Gcoldsload < SCHEDULE_CELL:Schedule > #fi <=Int ( GAS_CELL:Int -Int Csstore ( SCHEDULE_CELL:Schedule , W1:Int , #lookup ( STORAGE_CELL:Map , W0:Int ) , #lookup ( ORIG_STORAGE_CELL:Map , W0:Int ) ) )
       andBool ( Gcallstipend < SCHEDULE_CELL:Schedule > <Int GAS_CELL:Int
               )))))
      [priority(20), label(SSTORE-SUMMARY-USEGAS-BERLIN)]
    
    rule [SSTORE-SUMMARY-USEGAS]: <kevm>
           <k>
             ( #next [ SSTORE ] ~> .K => .K )
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
                   ( ( W0:Int : ( W1:Int : WS:WordStack ) ) => WS:WordStack )
                 </wordStack>
                 <pc>
                   ( PC_CELL:Int => ( PC_CELL:Int +Int 1 ) )
                 </pc>
                 <gas>
                   ( GAS_CELL:Int => ( GAS_CELL:Int -Int Csstore ( SCHEDULE_CELL:Schedule , W1:Int , #lookup ( STORAGE_CELL:Map , W0:Int ) , #lookup ( ORIG_STORAGE_CELL:Map , W0:Int ) ) ) )
                 </gas>
                 <static>
                   false
                 </static>
                 ...
               </callState>
               <substate>
                 <refund>
                   ( REFUND_CELL:Int => ( REFUND_CELL:Int +Int Rsstore ( SCHEDULE_CELL:Schedule , W1:Int , #lookup ( STORAGE_CELL:Map , W0:Int ) , #lookup ( ORIG_STORAGE_CELL:Map , W0:Int ) ) ) )
                 </refund>
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
                     ( STORAGE_CELL:Map => STORAGE_CELL:Map [ W0:Int <- W1:Int ] )
                   </storage>
                   <origStorage>
                     ORIG_STORAGE_CELL:Map
                   </origStorage>
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
       andBool ( Csstore ( SCHEDULE_CELL:Schedule , W1:Int , #lookup ( STORAGE_CELL:Map , W0:Int ) , #lookup ( ORIG_STORAGE_CELL:Map , W0:Int ) ) <=Int GAS_CELL:Int
       andBool ( Gcallstipend < SCHEDULE_CELL:Schedule > <Int GAS_CELL:Int
               ))))
      [priority(20), label(SSTORE-SUMMARY-USEGAS)]

endmodule