requires "../evm.md"
requires "../buf.md"

module SUMMARY-RETURN-2-SPEC
imports EVM
imports BUF
    
    
    rule [BASIC-BLOCK-24-TO-23]: <kevm>
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
      requires USEGAS_CELL:Bool  andBool ( ( ( ( ( Cmem ( SCHEDULE_CELL:Schedule , #memoryUsageUpdate ( MEMORYUSED_CELL:Int , W0:Int , W1:Int ) ) -Int Cmem ( SCHEDULE_CELL:Schedule , MEMORYUSED_CELL:Int ) ) ) -Int Gzero < SCHEDULE_CELL:Schedule > ) ) ) <=Int GAS_CELL 
      [priority(20), label(BASIC-BLOCK-24-TO-23)]
    
    rule [BASIC-BLOCK-25-TO-14]: <kevm>
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
      [priority(20), label(BASIC-BLOCK-25-TO-14)]

endmodule