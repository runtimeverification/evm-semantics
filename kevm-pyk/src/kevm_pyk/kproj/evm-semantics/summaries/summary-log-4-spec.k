requires "../evm.md"

module SUMMARY-LOG-4-SPEC
imports EVM
    
    
    rule [BASIC-BLOCK-4-TO-8]: <kevm>
           <k>
             ( #next [ LOG ( 2 ) ] => #halt )
             ~> __K_CELL:K
           </k>
           <ethereum>
             <evm>
               <statusCode>
                 ( __STATUSCODE_CELL:StatusCode => EVMC_STATIC_MODE_VIOLATION )
               </statusCode>
               <callState>
                 <wordStack>
                   ( __W0:Int : ( __W1:Int : ( __W2:Int : ( __W3:Int : __WS:WordStack ) ) ) )
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
             ...
           </ethereum>
           ...
         </kevm>
      requires _STATIC_CELL:Bool
      [priority(20), label(BASIC-BLOCK-4-TO-8)]
    
    rule [BASIC-BLOCK-11-TO-10]: <kevm>
           <k>
             ( #next [ LOG ( 2 ) ] ~> .K => .K )
             ~> __K_CELL:K
           </k>
           <schedule>
             _SCHEDULE_CELL:Schedule
           </schedule>
           <useGas>
             ( _USEGAS_CELL:Bool => true )
           </useGas>
           <ethereum>
             <evm>
               <callState>
                 <id>
                   _ID_CELL:Int
                 </id>
                 <wordStack>
                   ( ( _W0:Int : ( _W1:Int : ( _W2:Int : ( _W3:Int : _WS:WordStack ) ) ) ) => _WS:WordStack )
                 </wordStack>
                 <localMem>
                   _LOCALMEM_CELL:Bytes
                 </localMem>
                 <pc>
                   ( _PC_CELL:Int => ( _PC_CELL:Int +Int 1 ) )
                 </pc>
                 <gas>
                   ( ( _GAS_CELL:Int => ( ( _GAS_CELL:Int -Int ( Cmem ( _SCHEDULE_CELL:Schedule , #memoryUsageUpdate ( _MEMORYUSED_CELL:Int , _W0:Int , _W1:Int ) ) -Int Cmem ( _SCHEDULE_CELL:Schedule , _MEMORYUSED_CELL:Int ) ) ) -Int ( ( Glog < _SCHEDULE_CELL:Schedule > +Int ( Glogdata < _SCHEDULE_CELL:Schedule > *Int _W1:Int ) ) +Int ( 2 *Int Glogtopic < _SCHEDULE_CELL:Schedule > ) ) ) ) )
                 </gas>
                 <memoryUsed>
                   ( _MEMORYUSED_CELL:Int => #memoryUsageUpdate ( _MEMORYUSED_CELL:Int , _W0:Int , _W1:Int ) )
                 </memoryUsed>
                 <static>
                   ( _STATIC_CELL:Bool => false )
                 </static>
                 ...
               </callState>
               <substate>
                 <log>
                   ( _LOG_CELL:List => _LOG_CELL:List ListItem ( { _ID_CELL:Int | ListItem ( _W2:Int ) ListItem ( _W3:Int ) | #range ( _LOCALMEM_CELL:Bytes , _W0:Int , _W1:Int ) } ) )
                 </log>
                 ...
               </substate>
               ...
             </evm>
             ...
           </ethereum>
           ...
         </kevm>
      requires ( _USEGAS_CELL:Bool
       andBool ( ( notBool _STATIC_CELL:Bool )
               ))
      [priority(20), label(BASIC-BLOCK-11-TO-10)]
    
    rule [BASIC-BLOCK-12-TO-9]: <kevm>
           <k>
             ( #next [ LOG ( 2 ) ] ~> .K => .K )
             ~> __K_CELL:K
           </k>
           <useGas>
             ( _USEGAS_CELL:Bool => false )
           </useGas>
           <ethereum>
             <evm>
               <callState>
                 <id>
                   _ID_CELL:Int
                 </id>
                 <wordStack>
                   ( ( _W0:Int : ( _W1:Int : ( _W2:Int : ( _W3:Int : _WS:WordStack ) ) ) ) => _WS:WordStack )
                 </wordStack>
                 <localMem>
                   _LOCALMEM_CELL:Bytes
                 </localMem>
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
               <substate>
                 <log>
                   ( _LOG_CELL:List => _LOG_CELL:List ListItem ( { _ID_CELL:Int | ListItem ( _W2:Int ) ListItem ( _W3:Int ) | #range ( _LOCALMEM_CELL:Bytes , _W0:Int , _W1:Int ) } ) )
                 </log>
                 ...
               </substate>
               ...
             </evm>
             ...
           </ethereum>
           ...
         </kevm>
      requires ( ( notBool _STATIC_CELL:Bool )
       andBool ( ( notBool _USEGAS_CELL:Bool )
               ))
      [priority(20), label(BASIC-BLOCK-12-TO-9)]

endmodule