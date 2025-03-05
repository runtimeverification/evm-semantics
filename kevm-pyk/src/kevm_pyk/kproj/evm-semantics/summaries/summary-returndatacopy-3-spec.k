requires "../evm.md"

module SUMMARY-RETURNDATACOPY-3-SPEC
imports EVM
    
    
    rule [BASIC-BLOCK-24-TO-14]: <kevm>
           <k>
             ( #next [ RETURNDATACOPY ] ~> .K => .K )
             ~> K_CELL:K
           </k>
           <useGas>
             ( USEGAS_CELL:Bool => false )
           </useGas>
           <ethereum>
             <evm>
               <output>
                 OUTPUT_CELL:Bytes
               </output>
               <callState>
                 <wordStack>
                   ( ( W0:Int : ( W1:Int : ( W2:Int : WS:WordStack ) ) ) => WS:WordStack )
                 </wordStack>
                 <localMem>
                   ( LOCALMEM_CELL:Bytes => LOCALMEM_CELL:Bytes [ W0:Int := #range ( OUTPUT_CELL:Bytes , W1:Int , W2:Int ) ] )
                 </localMem>
                 <pc>
                   ( PC_CELL:Int => ( PC_CELL:Int +Int 1 ) )
                 </pc>
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
      requires ( ( notBool USEGAS_CELL:Bool )
       andBool ( ( W1:Int +Int W2:Int ) <=Int lengthBytes ( OUTPUT_CELL:Bytes )
               ))
      [priority(20), label(BASIC-BLOCK-24-TO-14)]
    
    rule [BASIC-BLOCK-25-TO-12]: <kevm>
           <k>
             ( #next [ RETURNDATACOPY ] => #halt )
             ~> K_CELL:K
           </k>
           <useGas>
             ( USEGAS_CELL:Bool => false )
           </useGas>
           <ethereum>
             <evm>
               <output>
                 OUTPUT_CELL:Bytes
               </output>
               <statusCode>
                 ( STATUSCODE_CELL:StatusCode => EVMC_INVALID_MEMORY_ACCESS )
               </statusCode>
               <callState>
                 <wordStack>
                   ( ( W0:Int : ( W1:Int : ( W2:Int : WS:WordStack ) ) ) => WS:WordStack )
                 </wordStack>
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
      requires ( ( notBool USEGAS_CELL:Bool )
       andBool ( lengthBytes ( OUTPUT_CELL:Bytes ) <Int ( W1:Int +Int W2:Int )
               ))
      [priority(20), label(BASIC-BLOCK-25-TO-12)]
    
    rule [BASIC-BLOCK-22-TO-15]: <kevm>
           <k>
             ( #next [ RETURNDATACOPY ] ~> .K => .K )
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
                 OUTPUT_CELL:Bytes
               </output>
               <callState>
                 <wordStack>
                   ( ( W0:Int : ( W1:Int : ( W2:Int : WS:WordStack ) ) ) => WS:WordStack )
                 </wordStack>
                 <localMem>
                   ( LOCALMEM_CELL:Bytes => LOCALMEM_CELL:Bytes [ W0:Int := #range ( OUTPUT_CELL:Bytes , W1:Int , W2:Int ) ] )
                 </localMem>
                 <pc>
                   ( PC_CELL:Int => ( PC_CELL:Int +Int 1 ) )
                 </pc>
                 <gas>
                   ( ( GAS_CELL:Int => ( ( GAS_CELL:Int -Int ( Cmem ( SCHEDULE_CELL:Schedule , #memoryUsageUpdate ( MEMORYUSED_CELL:Int , W0:Int , W2:Int ) ) -Int Cmem ( SCHEDULE_CELL:Schedule , MEMORYUSED_CELL:Int ) ) ) -Int ( Gverylow < SCHEDULE_CELL:Schedule > +Int ( Gcopy < SCHEDULE_CELL:Schedule > *Int ( W2:Int up/Int 32 ) ) ) ) ) )
                 </gas>
                 <memoryUsed>
                   ( MEMORYUSED_CELL:Int => #memoryUsageUpdate ( MEMORYUSED_CELL:Int , W0:Int , W2:Int ) )
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
       andBool ( ( W1:Int +Int W2:Int ) <=Int lengthBytes ( OUTPUT_CELL:Bytes )
               ))
      [priority(20), label(BASIC-BLOCK-22-TO-15)]
    
    rule [BASIC-BLOCK-23-TO-13]: <kevm>
           <k>
             ( #next [ RETURNDATACOPY ] => #halt )
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
                 OUTPUT_CELL:Bytes
               </output>
               <statusCode>
                 ( STATUSCODE_CELL:StatusCode => EVMC_INVALID_MEMORY_ACCESS )
               </statusCode>
               <callState>
                 <wordStack>
                   ( ( W0:Int : ( W1:Int : ( W2:Int : WS:WordStack ) ) ) => WS:WordStack )
                 </wordStack>
                 <gas>
                   ( ( GAS_CELL:Int => ( ( GAS_CELL:Int -Int ( Cmem ( SCHEDULE_CELL:Schedule , #memoryUsageUpdate ( MEMORYUSED_CELL:Int , W0:Int , W2:Int ) ) -Int Cmem ( SCHEDULE_CELL:Schedule , MEMORYUSED_CELL:Int ) ) ) -Int ( Gverylow < SCHEDULE_CELL:Schedule > +Int ( Gcopy < SCHEDULE_CELL:Schedule > *Int ( W2:Int up/Int 32 ) ) ) ) ) )
                 </gas>
                 <memoryUsed>
                   ( MEMORYUSED_CELL:Int => #memoryUsageUpdate ( MEMORYUSED_CELL:Int , W0:Int , W2:Int ) )
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
       andBool ( lengthBytes ( OUTPUT_CELL:Bytes ) <Int ( W1:Int +Int W2:Int )
               ))
      [priority(20), label(BASIC-BLOCK-23-TO-13)]

endmodule