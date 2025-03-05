requires "../evm.md"

module SUMMARY-RETURNDATACOPY-3-SPEC
imports EVM
    
    
    rule [BASIC-BLOCK-24-TO-14]: <kevm>
           <k>
             ( #next [ RETURNDATACOPY ] ~> .K => .K )
             ~> __K_CELL:K
           </k>
           <useGas>
             ( _USEGAS_CELL:Bool => false )
           </useGas>
           <ethereum>
             <evm>
               <output>
                 _OUTPUT_CELL:Bytes
               </output>
               <callState>
                 <wordStack>
                   ( ( _W0:Int : ( _W1:Int : ( _W2:Int : _WS:WordStack ) ) ) => _WS:WordStack )
                 </wordStack>
                 <localMem>
                   ( _LOCALMEM_CELL:Bytes => _LOCALMEM_CELL:Bytes [ _W0:Int := #range ( _OUTPUT_CELL:Bytes , _W1:Int , _W2:Int ) ] )
                 </localMem>
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
             ...
           </ethereum>
           ...
         </kevm>
      requires ( ( notBool _USEGAS_CELL:Bool )
       andBool ( ( _W1:Int +Int _W2:Int ) <=Int lengthBytes ( _OUTPUT_CELL:Bytes )
               ))
      [priority(20), label(BASIC-BLOCK-24-TO-14)]
    
    rule [BASIC-BLOCK-25-TO-12]: <kevm>
           <k>
             ( #next [ RETURNDATACOPY ] => #halt )
             ~> __K_CELL:K
           </k>
           <useGas>
             ( _USEGAS_CELL:Bool => false )
           </useGas>
           <ethereum>
             <evm>
               <output>
                 _OUTPUT_CELL:Bytes
               </output>
               <statusCode>
                 ( __STATUSCODE_CELL:StatusCode => EVMC_INVALID_MEMORY_ACCESS )
               </statusCode>
               <callState>
                 <wordStack>
                   ( ( __W0:Int : ( _W1:Int : ( _W2:Int : _WS:WordStack ) ) ) => _WS:WordStack )
                 </wordStack>
                 <gas>
                   ( __GAS_CELL:Int )
                 </gas>
                 ...
               </callState>
               ...
             </evm>
             ...
           </ethereum>
           ...
         </kevm>
      requires ( ( notBool _USEGAS_CELL:Bool )
       andBool ( lengthBytes ( _OUTPUT_CELL:Bytes ) <Int ( _W1:Int +Int _W2:Int )
               ))
      [priority(20), label(BASIC-BLOCK-25-TO-12)]
    
    rule [BASIC-BLOCK-22-TO-15]: <kevm>
           <k>
             ( #next [ RETURNDATACOPY ] ~> .K => .K )
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
               <output>
                 _OUTPUT_CELL:Bytes
               </output>
               <callState>
                 <wordStack>
                   ( ( _W0:Int : ( _W1:Int : ( _W2:Int : _WS:WordStack ) ) ) => _WS:WordStack )
                 </wordStack>
                 <localMem>
                   ( _LOCALMEM_CELL:Bytes => _LOCALMEM_CELL:Bytes [ _W0:Int := #range ( _OUTPUT_CELL:Bytes , _W1:Int , _W2:Int ) ] )
                 </localMem>
                 <pc>
                   ( _PC_CELL:Int => ( _PC_CELL:Int +Int 1 ) )
                 </pc>
                 <gas>
                   ( ( _GAS_CELL:Int => ( ( _GAS_CELL:Int -Int ( Cmem ( _SCHEDULE_CELL:Schedule , #memoryUsageUpdate ( _MEMORYUSED_CELL:Int , _W0:Int , _W2:Int ) ) -Int Cmem ( _SCHEDULE_CELL:Schedule , _MEMORYUSED_CELL:Int ) ) ) -Int ( Gverylow < _SCHEDULE_CELL:Schedule > +Int ( Gcopy < _SCHEDULE_CELL:Schedule > *Int ( _W2:Int up/Int 32 ) ) ) ) ) )
                 </gas>
                 <memoryUsed>
                   ( _MEMORYUSED_CELL:Int => #memoryUsageUpdate ( _MEMORYUSED_CELL:Int , _W0:Int , _W2:Int ) )
                 </memoryUsed>
                 ...
               </callState>
               ...
             </evm>
             ...
           </ethereum>
           ...
         </kevm>
      requires ( _USEGAS_CELL:Bool
       andBool ( ( _W1:Int +Int _W2:Int ) <=Int lengthBytes ( _OUTPUT_CELL:Bytes )
               ))
      [priority(20), label(BASIC-BLOCK-22-TO-15)]
    
    rule [BASIC-BLOCK-23-TO-13]: <kevm>
           <k>
             ( #next [ RETURNDATACOPY ] => #halt )
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
               <output>
                 _OUTPUT_CELL:Bytes
               </output>
               <statusCode>
                 ( __STATUSCODE_CELL:StatusCode => EVMC_INVALID_MEMORY_ACCESS )
               </statusCode>
               <callState>
                 <wordStack>
                   ( ( _W0:Int : ( _W1:Int : ( _W2:Int : _WS:WordStack ) ) ) => _WS:WordStack )
                 </wordStack>
                 <gas>
                   ( ( _GAS_CELL:Int => ( ( _GAS_CELL:Int -Int ( Cmem ( _SCHEDULE_CELL:Schedule , #memoryUsageUpdate ( _MEMORYUSED_CELL:Int , _W0:Int , _W2:Int ) ) -Int Cmem ( _SCHEDULE_CELL:Schedule , _MEMORYUSED_CELL:Int ) ) ) -Int ( Gverylow < _SCHEDULE_CELL:Schedule > +Int ( Gcopy < _SCHEDULE_CELL:Schedule > *Int ( _W2:Int up/Int 32 ) ) ) ) ) )
                 </gas>
                 <memoryUsed>
                   ( _MEMORYUSED_CELL:Int => #memoryUsageUpdate ( _MEMORYUSED_CELL:Int , _W0:Int , _W2:Int ) )
                 </memoryUsed>
                 ...
               </callState>
               ...
             </evm>
             ...
           </ethereum>
           ...
         </kevm>
      requires ( _USEGAS_CELL:Bool
       andBool ( lengthBytes ( _OUTPUT_CELL:Bytes ) <Int ( _W1:Int +Int _W2:Int )
               ))
      [priority(20), label(BASIC-BLOCK-23-TO-13)]

endmodule