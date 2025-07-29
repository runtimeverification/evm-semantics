requires "../evm.md"

module CODECOPY-SUMMARY
    imports public EVM
    
    rule [CODECOPY-SUMMARY-USEGAS]: <kevm>
           <k>
             ( #next [ CODECOPY ] ~> .K => .K )
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
                 <program>
                   PROGRAM_CELL:Bytes
                 </program>
                 <wordStack>
                   ( ( W0:Int : ( W1:Int : ( W2:Int : WS:WordStack ) ) ) => WS:WordStack )
                 </wordStack>
                 <localMem>
                   ( LOCALMEM_CELL:Bytes => LOCALMEM_CELL:Bytes [ W0:Int := #range ( PROGRAM_CELL:Bytes , W1:Int , W2:Int ) ] )
                 </localMem>
                 <pc>
                   ( PC_CELL:Int => ( PC_CELL:Int +Int 1 ) )
                 </pc>
                 <gas>
                   ( GAS_CELL:Int => ( ( GAS_CELL:Int -Int ( Cmem ( SCHEDULE_CELL:Schedule , #memoryUsageUpdate ( MEMORYUSED_CELL:Int , W0:Int , W2:Int ) ) -Int Cmem ( SCHEDULE_CELL:Schedule , MEMORYUSED_CELL:Int ) ) ) -Int ( Gverylow < SCHEDULE_CELL:Schedule > +Int ( Gcopy < SCHEDULE_CELL:Schedule > *Int ( W2:Int up/Int 32 ) ) ) ) )
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
       andBool ( ( Cmem ( SCHEDULE_CELL:Schedule , #memoryUsageUpdate ( MEMORYUSED_CELL:Int , W0:Int , W2:Int ) ) -Int Cmem ( SCHEDULE_CELL:Schedule , MEMORYUSED_CELL:Int ) ) <=Int GAS_CELL:Int
       andBool ( ( Gverylow < SCHEDULE_CELL:Schedule > +Int ( Gcopy < SCHEDULE_CELL:Schedule > *Int ( W2:Int up/Int 32 ) ) ) <=Int ( GAS_CELL:Int -Int ( Cmem ( SCHEDULE_CELL:Schedule , #memoryUsageUpdate ( MEMORYUSED_CELL:Int , W0:Int , W2:Int ) ) -Int Cmem ( SCHEDULE_CELL:Schedule , MEMORYUSED_CELL:Int ) ) )
               )))
      [priority(20), label(CODECOPY-SUMMARY-USEGAS)]
    
    rule [CODECOPY-SUMMARY-NOGAS]: <kevm>
           <k>
             ( #next [ CODECOPY ] ~> .K => .K )
             ~> _K_CELL:K
           </k>
           <useGas>
             ( USEGAS_CELL:Bool => false )
           </useGas>
           <ethereum>
             <evm>
               <callState>
                 <program>
                   PROGRAM_CELL:Bytes
                 </program>
                 <wordStack>
                   ( ( W0:Int : ( W1:Int : ( W2:Int : WS:WordStack ) ) ) => WS:WordStack )
                 </wordStack>
                 <localMem>
                   ( LOCALMEM_CELL:Bytes => LOCALMEM_CELL:Bytes [ W0:Int := #range ( PROGRAM_CELL:Bytes , W1:Int , W2:Int ) ] )
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
      [priority(20), label(CODECOPY-SUMMARY-NOGAS)]

endmodule