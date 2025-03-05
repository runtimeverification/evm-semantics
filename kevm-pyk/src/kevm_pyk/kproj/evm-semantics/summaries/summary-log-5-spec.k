requires "../evm.md"

module SUMMARY-LOG-5-SPEC
imports EVM
    
    
    rule [BASIC-BLOCK-4-TO-8]: <kevm>
           <k>
             ( #next [ LOG ( 3 ) ] => #halt )
             ~> K_CELL:K
           </k>
           <ethereum>
             <evm>
               <statusCode>
                 ( STATUSCODE_CELL:StatusCode => EVMC_STATIC_MODE_VIOLATION )
               </statusCode>
               <callState>
                 <wordStack>
                   ( W0:Int : ( W1:Int : ( W2:Int : ( W3:Int : ( W4:Int : WS:WordStack ) ) ) ) )
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
             ...
           </ethereum>
           ...
         </kevm>
      requires STATIC_CELL:Bool
      [priority(20), label(BASIC-BLOCK-4-TO-8)]
    
    rule [BASIC-BLOCK-11-TO-10]: <kevm>
           <k>
             ( #next [ LOG ( 3 ) ] ~> .K => .K )
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
                   ( ( W0:Int : ( W1:Int : ( W2:Int : ( W3:Int : ( W4:Int : WS:WordStack ) ) ) ) ) => WS:WordStack )
                 </wordStack>
                 <localMem>
                   LOCALMEM_CELL:Bytes
                 </localMem>
                 <pc>
                   ( PC_CELL:Int => ( PC_CELL:Int +Int 1 ) )
                 </pc>
                 <gas>
                   ( ( GAS_CELL:Int => ( ( GAS_CELL:Int -Int ( Cmem ( SCHEDULE_CELL:Schedule , #memoryUsageUpdate ( MEMORYUSED_CELL:Int , W0:Int , W1:Int ) ) -Int Cmem ( SCHEDULE_CELL:Schedule , MEMORYUSED_CELL:Int ) ) ) -Int ( ( Glog < SCHEDULE_CELL:Schedule > +Int ( Glogdata < SCHEDULE_CELL:Schedule > *Int W1:Int ) ) +Int ( 3 *Int Glogtopic < SCHEDULE_CELL:Schedule > ) ) ) ) )
                 </gas>
                 <memoryUsed>
                   ( MEMORYUSED_CELL:Int => #memoryUsageUpdate ( MEMORYUSED_CELL:Int , W0:Int , W1:Int ) )
                 </memoryUsed>
                 <static>
                   ( STATIC_CELL:Bool => false )
                 </static>
                 ...
               </callState>
               <substate>
                 <log>
                   ( LOG_CELL:List => LOG_CELL:List ListItem ( { ID_CELL:Int | ListItem ( W2:Int ) ListItem ( W3:Int ) ListItem ( W4:Int ) | #range ( LOCALMEM_CELL:Bytes , W0:Int , W1:Int ) } ) )
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
       andBool ( ( notBool STATIC_CELL:Bool )
               ))
      [priority(20), label(BASIC-BLOCK-11-TO-10)]
    
    rule [BASIC-BLOCK-12-TO-9]: <kevm>
           <k>
             ( #next [ LOG ( 3 ) ] ~> .K => .K )
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
                   ( ( W0:Int : ( W1:Int : ( W2:Int : ( W3:Int : ( W4:Int : WS:WordStack ) ) ) ) ) => WS:WordStack )
                 </wordStack>
                 <localMem>
                   LOCALMEM_CELL:Bytes
                 </localMem>
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
               <substate>
                 <log>
                   ( LOG_CELL:List => LOG_CELL:List ListItem ( { ID_CELL:Int | ListItem ( W2:Int ) ListItem ( W3:Int ) ListItem ( W4:Int ) | #range ( LOCALMEM_CELL:Bytes , W0:Int , W1:Int ) } ) )
                 </log>
                 ...
               </substate>
               ...
             </evm>
             ...
           </ethereum>
           ...
         </kevm>
      requires ( ( notBool STATIC_CELL:Bool )
       andBool ( ( notBool USEGAS_CELL:Bool )
               ))
      [priority(20), label(BASIC-BLOCK-12-TO-9)]

endmodule