requires "../evm.md"

module DIFFICULTY-SUMMARY
    imports public EVM
    
    rule [DIFFICULTY-SUMMARY-USEGAS]: <kevm>
           <k>
             ( #next [ DIFFICULTY ] ~> .K => .K )
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
                   ( WS:WordStack => ( DIFFICULTY_CELL:Int : WS:WordStack ) )
                 </wordStack>
                 <pc>
                   ( PC_CELL:Int => ( PC_CELL:Int +Int 1 ) )
                 </pc>
                 <gas>
                   ( GAS_CELL:Int => ( GAS_CELL:Int -Int Gbase < SCHEDULE_CELL:Schedule > ) )
                 </gas>
                 ...
               </callState>
               <block>
                 <difficulty>
                   DIFFICULTY_CELL:Int
                 </difficulty>
                 ...
               </block>
               ...
             </evm>
             ...
           </ethereum>
           ...
         </kevm>
      requires ( USEGAS_CELL:Bool
       andBool ( #sizeWordStack ( WS:WordStack , 0 ) <=Int 1023
       andBool ( Gbase < SCHEDULE_CELL:Schedule > <=Int GAS_CELL:Int
               )))
      [priority(20), label(DIFFICULTY-SUMMARY-USEGAS)]
    
    rule [DIFFICULTY-SUMMARY-NOGAS]: <kevm>
           <k>
             ( #next [ DIFFICULTY ] ~> .K => .K )
             ~> _K_CELL:K
           </k>
           <useGas>
             ( USEGAS_CELL:Bool => false )
           </useGas>
           <ethereum>
             <evm>
               <callState>
                 <wordStack>
                   ( WS:WordStack => ( DIFFICULTY_CELL:Int : WS:WordStack ) )
                 </wordStack>
                 <pc>
                   ( PC_CELL:Int => ( PC_CELL:Int +Int 1 ) )
                 </pc>
                 <gas>
                   _GAS_CELL:Int
                 </gas>
                 ...
               </callState>
               <block>
                 <difficulty>
                   DIFFICULTY_CELL:Int
                 </difficulty>
                 ...
               </block>
               ...
             </evm>
             ...
           </ethereum>
           ...
         </kevm>
      requires ( ( notBool USEGAS_CELL:Bool )
       andBool ( #sizeWordStack ( WS:WordStack , 0 ) <=Int 1023
               ))
      [priority(20), label(DIFFICULTY-SUMMARY-NOGAS)]

endmodule