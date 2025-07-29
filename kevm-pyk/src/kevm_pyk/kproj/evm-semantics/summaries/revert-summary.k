requires "../evm.md"

module REVERT-SUMMARY
    imports public EVM
    
    rule [REVERT-SUMMARY-USEGAS]: <kevm>
           <k>
             ( #next [ REVERT ] => #halt )
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
               <output>
                 ( _OUTPUT_CELL:Bytes => #range ( LOCALMEM_CELL:Bytes , W0:Int , W1:Int ) )
               </output>
               <statusCode>
                 ( _STATUSCODE_CELL:StatusCode => EVMC_REVERT )
               </statusCode>
               <callState>
                 <wordStack>
                   ( ( W0:Int : ( W1:Int : WS:WordStack ) ) => WS:WordStack )
                 </wordStack>
                 <localMem>
                   LOCALMEM_CELL:Bytes
                 </localMem>
                 <gas>
                   ( GAS_CELL:Int => ( ( GAS_CELL:Int -Int ( Cmem ( SCHEDULE_CELL:Schedule , #memoryUsageUpdate ( MEMORYUSED_CELL:Int , W0:Int , W1:Int ) ) -Int Cmem ( SCHEDULE_CELL:Schedule , MEMORYUSED_CELL:Int ) ) ) -Int Gzero < SCHEDULE_CELL:Schedule > ) )
                 </gas>
                 <memoryUsed>
                   ( MEMORYUSED_CELL:Int => #memoryUsageUpdate ( MEMORYUSED_CELL:Int , W0:Int , W1:Int ) )
                 </memoryUsed>
                 ...
               </callState>
               ...
             </evm>
             ...
           </ethereum>
           ...
         </kevm>
      requires ( USEGAS_CELL:Bool
       andBool ( ( Cmem ( SCHEDULE_CELL:Schedule , #memoryUsageUpdate ( MEMORYUSED_CELL:Int , W0:Int , W1:Int ) ) -Int Cmem ( SCHEDULE_CELL:Schedule , MEMORYUSED_CELL:Int ) ) <=Int GAS_CELL:Int
       andBool ( Gzero < SCHEDULE_CELL:Schedule > <=Int ( GAS_CELL:Int -Int ( Cmem ( SCHEDULE_CELL:Schedule , #memoryUsageUpdate ( MEMORYUSED_CELL:Int , W0:Int , W1:Int ) ) -Int Cmem ( SCHEDULE_CELL:Schedule , MEMORYUSED_CELL:Int ) ) )
               )))
      [priority(20), label(REVERT-SUMMARY-USEGAS)]
    
    rule [REVERT-SUMMARY-NOGAS]: <kevm>
           <k>
             ( #next [ REVERT ] => #halt )
             ~> _K_CELL:K
           </k>
           <useGas>
             ( USEGAS_CELL:Bool => false )
           </useGas>
           <ethereum>
             <evm>
               <output>
                 ( _OUTPUT_CELL:Bytes => #range ( LOCALMEM_CELL:Bytes , W0:Int , W1:Int ) )
               </output>
               <statusCode>
                 ( _STATUSCODE_CELL:StatusCode => EVMC_REVERT )
               </statusCode>
               <callState>
                 <wordStack>
                   ( ( W0:Int : ( W1:Int : WS:WordStack ) ) => WS:WordStack )
                 </wordStack>
                 <localMem>
                   LOCALMEM_CELL:Bytes
                 </localMem>
                 <gas>
                   _GAS_CELL:Int
                 </gas>
                 ...
               </callState>
               ...
             </evm>
             ...
           </ethereum>
           ...
         </kevm>
      requires ( notBool USEGAS_CELL:Bool )
      [priority(20), label(REVERT-SUMMARY-NOGAS)]

endmodule