requires "../evm.md"

module MSIZE-SUMMARY
    imports public EVM
    
    rule [MSIZE-SUMMARY-0]: <kevm>
           <k>
             ( #next [ MSIZE ] => #halt )
             ~> K_CELL:K
           </k>
           <ethereum>
             <evm>
               <statusCode>
                 ( STATUSCODE_CELL:StatusCode => EVMC_STACK_OVERFLOW )
               </statusCode>
               <callState>
                 <wordStack>
                   WS:WordStack
                 </wordStack>
                 <gas>
                   GAS_CELL:Int
                 </gas>
                 ...
               </callState>
               ...
             </evm>
             ...
           </ethereum>
           ...
         </kevm>
      requires 1023 <Int #sizeWordStack ( WS:WordStack , 0 )
      [priority(20), label(MSIZE-SUMMARY-0)]
    
    rule [MSIZE-SUMMARY-1]: <kevm>
           <k>
             ( #next [ MSIZE ] ~> .K => .K )
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
                 <wordStack>
                   ( WS:WordStack => ( chop ( ( 32 *Int MEMORYUSED_CELL:Int ) ) : WS:WordStack ) )
                 </wordStack>
                 <pc>
                   ( PC_CELL:Int => ( PC_CELL:Int +Int 1 ) )
                 </pc>
                 <gas>
                   ( GAS_CELL:Int => ( GAS_CELL:Int -Int Gbase < SCHEDULE_CELL:Schedule > ) )
                 </gas>
                 <memoryUsed>
                   MEMORYUSED_CELL:Int
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
       andBool ( ( notBool #sizeWordStack ( WS:WordStack , 0 ) <Int 0 )
       andBool ( ( notBool 1023 <Int #sizeWordStack ( WS:WordStack , 0 ) )
       andBool ( Gbase < SCHEDULE_CELL:Schedule > <=Int GAS_CELL:Int
               ))))
       ensures #sizeWordStack ( WS:WordStack , 0 ) <=Int 1023
      [priority(20), label(MSIZE-SUMMARY-1)]
    
    rule [MSIZE-SUMMARY-2]: <kevm>
           <k>
             ( #next [ MSIZE ] ~> .K => .K )
             ~> K_CELL:K
           </k>
           <useGas>
             ( USEGAS_CELL:Bool => false )
           </useGas>
           <ethereum>
             <evm>
               <callState>
                 <wordStack>
                   ( WS:WordStack => ( chop ( ( 32 *Int MEMORYUSED_CELL:Int ) ) : WS:WordStack ) )
                 </wordStack>
                 <pc>
                   ( PC_CELL:Int => ( PC_CELL:Int +Int 1 ) )
                 </pc>
                 <gas>
                   GAS_CELL:Int
                 </gas>
                 <memoryUsed>
                   MEMORYUSED_CELL:Int
                 </memoryUsed>
                 ...
               </callState>
               ...
             </evm>
             ...
           </ethereum>
           ...
         </kevm>
      requires ( ( notBool USEGAS_CELL:Bool )
       andBool ( ( notBool #sizeWordStack ( WS:WordStack , 0 ) <Int 0 )
       andBool ( ( notBool 1023 <Int #sizeWordStack ( WS:WordStack , 0 ) )
               )))
       ensures #sizeWordStack ( WS:WordStack , 0 ) <=Int 1023
      [priority(20), label(MSIZE-SUMMARY-2)]

endmodule