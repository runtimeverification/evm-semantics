requires "../evm.md"

module PUSH-SUMMARY
    imports public EVM
    
    rule [PUSH-SUMMARY-USEGAS]: <kevm>
           <k>
             ( #next [ PUSH ( N:Int ) ] ~> .K => .K )
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
                 <program>
                   PROGRAM_CELL:Bytes
                 </program>
                 <wordStack>
                   ( WS:WordStack => ( #asWord ( #range ( PROGRAM_CELL:Bytes , ( PC_CELL:Int +Int 1 ) , N:Int ) ) : WS:WordStack ) )
                 </wordStack>
                 <pc>
                   ( PC_CELL:Int => ( ( PC_CELL:Int +Int N:Int ) +Int 1 ) )
                 </pc>
                 <gas>
                   ( GAS_CELL:Int => ( GAS_CELL:Int -Int Gverylow < SCHEDULE_CELL:Schedule > ) )
                 </gas>
                 ...
               </callState>
               ...
             </evm>
             ...
           </ethereum>
           ...
         </kevm>
      requires ( USEGAS_CELL:Bool
       andBool ( #sizeWordStack ( WS:WordStack , 0 ) <=Int 1023
       andBool ( Gverylow < SCHEDULE_CELL:Schedule > <=Int GAS_CELL:Int
               )))
      [priority(20), label(PUSH-SUMMARY-USEGAS)]
    
    rule [PUSH-SUMMARY-NOGAS]: <kevm>
           <k>
             ( #next [ PUSH ( N:Int ) ] ~> .K => .K )
             ~> K_CELL:K
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
                   ( WS:WordStack => ( #asWord ( #range ( PROGRAM_CELL:Bytes , ( PC_CELL:Int +Int 1 ) , N:Int ) ) : WS:WordStack ) )
                 </wordStack>
                 <pc>
                   ( PC_CELL:Int => ( ( PC_CELL:Int +Int N:Int ) +Int 1 ) )
                 </pc>
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
      requires ( ( notBool USEGAS_CELL:Bool )
       andBool ( #sizeWordStack ( WS:WordStack , 0 ) <=Int 1023
               ))
      [priority(20), label(PUSH-SUMMARY-NOGAS)]

endmodule