requires "../evm.md"

module DUP-SUMMARY
    imports public EVM
    
    rule [DUP-SUMMARY-USEGAS]: <kevm>
           <k>
             ( #next [ DUP ( N:Int ) ] ~> .K => .K )
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
                   ( WS:WordStack => ( WS:WordStack [ ( N:Int +Int -1 ) ] : WS:WordStack ) )
                 </wordStack>
                 <pc>
                   ( PC_CELL:Int => ( PC_CELL:Int +Int 1 ) )
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
       andBool ( N:Int <=Int #sizeWordStack ( WS:WordStack , 0 )
       andBool ( #sizeWordStack ( WS:WordStack , 0 ) <=Int 1023
       andBool ( Gverylow < SCHEDULE_CELL:Schedule > <=Int GAS_CELL:Int
               ))))
      [priority(20), label(DUP-SUMMARY-USEGAS)]
    
    rule [DUP-SUMMARY-NOGAS]: <kevm>
           <k>
             ( #next [ DUP ( N:Int ) ] ~> .K => .K )
             ~> _K_CELL:K
           </k>
           <useGas>
             ( USEGAS_CELL:Bool => false )
           </useGas>
           <ethereum>
             <evm>
               <callState>
                 <wordStack>
                   ( WS:WordStack => ( WS:WordStack [ ( N:Int +Int -1 ) ] : WS:WordStack ) )
                 </wordStack>
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
      requires ( ( notBool USEGAS_CELL:Bool )
       andBool ( N:Int <=Int #sizeWordStack ( WS:WordStack , 0 )
       andBool ( #sizeWordStack ( WS:WordStack , 0 ) <=Int 1023
               )))
      [priority(20), label(DUP-SUMMARY-NOGAS)]

endmodule