requires "../evm.md"

module LOG-SUMMARY
    imports public EVM
    
    rule [LOG-SUMMARY-USEGAS]: <kevm>
           <k>
             ( #next [ LOG ( N:Int ) ] ~> .K => .K )
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
                   ( ( W0:Int : ( W1:Int : WS:WordStack ) ) => #drop ( N:Int , WS:WordStack ) )
                 </wordStack>
                 <localMem>
                   LOCALMEM_CELL:Bytes
                 </localMem>
                 <pc>
                   ( PC_CELL:Int => ( PC_CELL:Int +Int 1 ) )
                 </pc>
                 <gas>
                   ( GAS_CELL:Int => ( ( GAS_CELL:Int -Int ( Cmem ( SCHEDULE_CELL:Schedule , #memoryUsageUpdate ( MEMORYUSED_CELL:Int , W0:Int , W1:Int ) ) -Int Cmem ( SCHEDULE_CELL:Schedule , MEMORYUSED_CELL:Int ) ) ) -Int ( ( Glog < SCHEDULE_CELL:Schedule > +Int ( Glogdata < SCHEDULE_CELL:Schedule > *Int W1:Int ) ) +Int ( N:Int *Int Glogtopic < SCHEDULE_CELL:Schedule > ) ) ) )
                 </gas>
                 <memoryUsed>
                   ( MEMORYUSED_CELL:Int => #memoryUsageUpdate ( MEMORYUSED_CELL:Int , W0:Int , W1:Int ) )
                 </memoryUsed>
                 <static>
                   false
                 </static>
                 ...
               </callState>
               <substate>
                 <log>
                   ( LOG_CELL:List => LOG_CELL:List ListItem ( { ID_CELL:Int | WordStack2List ( #take ( N:Int , WS:WordStack ) ) | #range ( LOCALMEM_CELL:Bytes , W0:Int , W1:Int ) } ) )
                 </log>
                 ...
               </substate>
               ...
             </evm>
             ...
           </ethereum>
           ...
         </kevm>
      requires ( USEGAS_CELL:Bool
       andBool ( 0 <=Int N:Int
       andBool ( N:Int <=Int #sizeWordStack ( WS:WordStack , 0 )
       andBool ( ( N:Int +Int 2 ) <=Int #sizeWordStack ( WS:WordStack , 2 )
       andBool ( ( Cmem ( SCHEDULE_CELL:Schedule , #memoryUsageUpdate ( MEMORYUSED_CELL:Int , W0:Int , W1:Int ) ) -Int Cmem ( SCHEDULE_CELL:Schedule , MEMORYUSED_CELL:Int ) ) <=Int GAS_CELL:Int
       andBool ( ( ( Glog < SCHEDULE_CELL:Schedule > +Int ( Glogdata < SCHEDULE_CELL:Schedule > *Int W1:Int ) ) +Int ( N:Int *Int Glogtopic < SCHEDULE_CELL:Schedule > ) ) <=Int ( GAS_CELL:Int -Int ( Cmem ( SCHEDULE_CELL:Schedule , #memoryUsageUpdate ( MEMORYUSED_CELL:Int , W0:Int , W1:Int ) ) -Int Cmem ( SCHEDULE_CELL:Schedule , MEMORYUSED_CELL:Int ) ) )
               ))))))
       ensures ( notBool ( N:Int <Int -2 andBool 1026 <Int ( #sizeWordStack ( WS:WordStack , 2 ) -Int N:Int ) ) )
      [priority(20), label(LOG-SUMMARY-USEGAS)]
    
    rule [LOG-SUMMARY-NOGAS]: <kevm>
           <k>
             ( #next [ LOG ( N:Int ) ] ~> .K => .K )
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
                   ( ( W0:Int : ( W1:Int : WS:WordStack ) ) => #drop ( N:Int , WS:WordStack ) )
                 </wordStack>
                 <localMem>
                   LOCALMEM_CELL:Bytes
                 </localMem>
                 <pc>
                   ( PC_CELL:Int => ( PC_CELL:Int +Int 1 ) )
                 </pc>
                 <gas>
                   GAS_CELL:Int
                 </gas>
                 <static>
                   false
                 </static>
                 ...
               </callState>
               <substate>
                 <log>
                   ( LOG_CELL:List => LOG_CELL:List ListItem ( { ID_CELL:Int | WordStack2List ( #take ( N:Int , WS:WordStack ) ) | #range ( LOCALMEM_CELL:Bytes , W0:Int , W1:Int ) } ) )
                 </log>
                 ...
               </substate>
               ...
             </evm>
             ...
           </ethereum>
           ...
         </kevm>
      requires ( ( notBool USEGAS_CELL:Bool )
       andBool ( 0 <=Int N:Int
       andBool ( N:Int <=Int #sizeWordStack ( WS:WordStack , 0 )
       andBool ( ( N:Int +Int 2 ) <=Int #sizeWordStack ( WS:WordStack , 2 )
               ))))
       ensures ( notBool ( N:Int <Int -2 andBool 1026 <Int ( #sizeWordStack ( WS:WordStack , 2 ) -Int N:Int ) ) )
      [priority(20), label(LOG-SUMMARY-NOGAS)]

endmodule