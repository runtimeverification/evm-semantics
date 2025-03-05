requires "../evm.md"

module SUMMARY-REVERT-2-SPEC
imports EVM
    
    
    rule [BASIC-BLOCK-8-TO-7]: <kevm>
           <k>
             ( #next [ REVERT ] => #halt )
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
                 ( __OUTPUT_CELL:Bytes => #range ( _LOCALMEM_CELL:Bytes , _W0:Int , _W1:Int ) )
               </output>
               <statusCode>
                 ( __STATUSCODE_CELL:StatusCode => EVMC_REVERT )
               </statusCode>
               <callState>
                 <wordStack>
                   ( ( _W0:Int : ( _W1:Int : _WS:WordStack ) ) => _WS:WordStack )
                 </wordStack>
                 <localMem>
                   _LOCALMEM_CELL:Bytes
                 </localMem>
                 <gas>
                   ( ( _GAS_CELL:Int => ( ( _GAS_CELL:Int -Int ( Cmem ( _SCHEDULE_CELL:Schedule , #memoryUsageUpdate ( _MEMORYUSED_CELL:Int , _W0:Int , _W1:Int ) ) -Int Cmem ( _SCHEDULE_CELL:Schedule , _MEMORYUSED_CELL:Int ) ) ) -Int Gzero < _SCHEDULE_CELL:Schedule > ) ) )
                 </gas>
                 <memoryUsed>
                   ( _MEMORYUSED_CELL:Int => #memoryUsageUpdate ( _MEMORYUSED_CELL:Int , _W0:Int , _W1:Int ) )
                 </memoryUsed>
                 ...
               </callState>
               ...
             </evm>
             ...
           </ethereum>
           ...
         </kevm>
      requires _USEGAS_CELL:Bool
      [priority(20), label(BASIC-BLOCK-8-TO-7)]
    
    rule [BASIC-BLOCK-9-TO-6]: <kevm>
           <k>
             ( #next [ REVERT ] => #halt )
             ~> __K_CELL:K
           </k>
           <useGas>
             ( _USEGAS_CELL:Bool => false )
           </useGas>
           <ethereum>
             <evm>
               <output>
                 ( __OUTPUT_CELL:Bytes => #range ( _LOCALMEM_CELL:Bytes , _W0:Int , _W1:Int ) )
               </output>
               <statusCode>
                 ( __STATUSCODE_CELL:StatusCode => EVMC_REVERT )
               </statusCode>
               <callState>
                 <wordStack>
                   ( ( _W0:Int : ( _W1:Int : _WS:WordStack ) ) => _WS:WordStack )
                 </wordStack>
                 <localMem>
                   _LOCALMEM_CELL:Bytes
                 </localMem>
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
      requires ( notBool _USEGAS_CELL:Bool )
      [priority(20), label(BASIC-BLOCK-9-TO-6)]

endmodule