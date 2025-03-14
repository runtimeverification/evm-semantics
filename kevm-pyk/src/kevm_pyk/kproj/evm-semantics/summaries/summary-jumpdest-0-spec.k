requires "../evm.md"
requires "../buf.md"

module SUMMARY-JUMPDEST-0-SPEC
imports EVM
imports BUF
    
    
    rule [BASIC-BLOCK-19-TO-18]: <kevm>
           <k>
             ( #next [ JUMPDEST ] ~> .K => .K )
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
                 <pc>
                   ( PC_CELL:Int => ( PC_CELL:Int +Int 1 ) )
                 </pc>
                 <gas>
                    ( ( GAS_CELL:Int => ( GAS_CELL:Int -Int Gjumpdest < SCHEDULE_CELL:Schedule > ) ) )
                 </gas>
                 ...
               </callState>
               ...
             </evm>
             ...
           </ethereum>
           ...
         </kevm>
      requires USEGAS_CELL:Bool  andBool ( ( ( Gjumpdest < SCHEDULE_CELL:Schedule > ) ) ) <=Int GAS_CELL 
      [priority(20), label(BASIC-BLOCK-19-TO-18)]
    
    rule [BASIC-BLOCK-20-TO-12]: <kevm>
           <k>
             ( #next [ JUMPDEST ] ~> .K => .K )
             ~> K_CELL:K
           </k>
           <useGas>
             ( USEGAS_CELL:Bool => false )
           </useGas>
           <ethereum>
             <evm>
               <callState>
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
      requires ( notBool USEGAS_CELL:Bool )
      [priority(20), label(BASIC-BLOCK-20-TO-12)]

endmodule