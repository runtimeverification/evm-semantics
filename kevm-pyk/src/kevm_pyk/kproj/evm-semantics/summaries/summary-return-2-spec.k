requires "../evm.md"

module SUMMARY-RETURN-2-SPEC
imports EVM
    
    
    rule [BASIC-BLOCK-8-TO-7]: <kevm>
           <k>
             ( #next [ RETURN ] => #halt )
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
               <output>
                 ( OUTPUT_CELL:Bytes => #range ( LOCALMEM_CELL:Bytes , W0:Int , W1:Int ) )
               </output>
               <statusCode>
                 ( STATUSCODE_CELL:StatusCode => EVMC_SUCCESS )
               </statusCode>
               <callState>
                 <wordStack>
                   ( ( W0:Int : ( W1:Int : WS:WordStack ) ) => WS:WordStack )
                 </wordStack>
                 <localMem>
                   LOCALMEM_CELL:Bytes
                 </localMem>
                 <gas>
                   ( ( GAS_CELL:Int => ( ( GAS_CELL:Int -Int ( Cmem ( SCHEDULE_CELL:Schedule , #memoryUsageUpdate ( MEMORYUSED_CELL:Int , W0:Int , W1:Int ) ) -Int Cmem ( SCHEDULE_CELL:Schedule , MEMORYUSED_CELL:Int ) ) ) -Int Gzero < SCHEDULE_CELL:Schedule > ) ) )
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
      requires USEGAS_CELL:Bool
      [priority(20), label(BASIC-BLOCK-8-TO-7)]
    
    rule [BASIC-BLOCK-9-TO-6]: <kevm>
           <k>
             ( #next [ RETURN ] => #halt )
             ~> K_CELL:K
           </k>
           <useGas>
             ( USEGAS_CELL:Bool => false )
           </useGas>
           <ethereum>
             <evm>
               <output>
                 ( OUTPUT_CELL:Bytes => #range ( LOCALMEM_CELL:Bytes , W0:Int , W1:Int ) )
               </output>
               <statusCode>
                 ( STATUSCODE_CELL:StatusCode => EVMC_SUCCESS )
               </statusCode>
               <callState>
                 <wordStack>
                   ( ( W0:Int : ( W1:Int : WS:WordStack ) ) => WS:WordStack )
                 </wordStack>
                 <localMem>
                   LOCALMEM_CELL:Bytes
                 </localMem>
                 <gas>
                   ( GAS_CELL:Int )
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
      [priority(20), label(BASIC-BLOCK-9-TO-6)]

endmodule