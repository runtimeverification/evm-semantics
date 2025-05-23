requires "../evm.md"

module SHA3-SUMMARY
    imports public EVM
    
    rule [SHA3-SUMMARY-USEGAS]: <kevm>
           <k>
             ( #next [ SHA3 ] ~> .K => .K )
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
                 <wordStack>
                   ( ( W0:Int => keccak ( #range ( LOCALMEM_CELL:Bytes , W0:Int , W1:Int ) ) ) : ( ( W1:Int : WS:WordStack ) => WS:WordStack ) )
                 </wordStack>
                 <localMem>
                   LOCALMEM_CELL:Bytes
                 </localMem>
                 <pc>
                   ( PC_CELL:Int => ( PC_CELL:Int +Int 1 ) )
                 </pc>
                 <gas>
                   ( GAS_CELL:Int => ( ( GAS_CELL:Int -Int ( Cmem ( SCHEDULE_CELL:Schedule , #memoryUsageUpdate ( MEMORYUSED_CELL:Int , W0:Int , W1:Int ) ) -Int Cmem ( SCHEDULE_CELL:Schedule , MEMORYUSED_CELL:Int ) ) ) -Int ( Gsha3 < SCHEDULE_CELL:Schedule > +Int ( Gsha3word < SCHEDULE_CELL:Schedule > *Int ( W1:Int up/Int 32 ) ) ) ) )
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
       andBool ( ( Gsha3 < SCHEDULE_CELL:Schedule > +Int ( Gsha3word < SCHEDULE_CELL:Schedule > *Int ( W1:Int up/Int 32 ) ) ) <=Int ( GAS_CELL:Int -Int ( Cmem ( SCHEDULE_CELL:Schedule , #memoryUsageUpdate ( MEMORYUSED_CELL:Int , W0:Int , W1:Int ) ) -Int Cmem ( SCHEDULE_CELL:Schedule , MEMORYUSED_CELL:Int ) ) )
               )))
      [priority(20), label(SHA3-SUMMARY-USEGAS)]
    
    rule [SHA3-SUMMARY-NOGAS]: <kevm>
           <k>
             ( #next [ SHA3 ] ~> .K => .K )
             ~> _K_CELL:K
           </k>
           <useGas>
             ( USEGAS_CELL:Bool => false )
           </useGas>
           <ethereum>
             <evm>
               <callState>
                 <wordStack>
                   ( ( W0:Int => keccak ( #range ( LOCALMEM_CELL:Bytes , W0:Int , W1:Int ) ) ) : ( ( W1:Int : WS:WordStack ) => WS:WordStack ) )
                 </wordStack>
                 <localMem>
                   LOCALMEM_CELL:Bytes
                 </localMem>
                 <pc>
                   ( PC_CELL:Int => ( PC_CELL:Int +Int 1 ) )
                 </pc>
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
      [priority(20), label(SHA3-SUMMARY-NOGAS)]

endmodule