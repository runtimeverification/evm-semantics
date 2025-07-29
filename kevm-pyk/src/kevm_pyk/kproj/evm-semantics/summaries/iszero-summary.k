requires "../evm.md"

module ISZERO-SUMMARY
    imports public EVM
    
    rule [ISZERO-SUMMARY-USEGAS]: <kevm>
           <k>
             ( #next [ ISZERO ] ~> .K => .K )
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
                   ( ( W0:Int => bool2Word ( W0:Int ==Int 0 ) ) : _WS:WordStack )
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
       andBool ( Gverylow < SCHEDULE_CELL:Schedule > <=Int GAS_CELL:Int
               ))
      [priority(20), label(ISZERO-SUMMARY-USEGAS)]
    
    rule [ISZERO-SUMMARY-NOGAS]: <kevm>
           <k>
             ( #next [ ISZERO ] ~> .K => .K )
             ~> _K_CELL:K
           </k>
           <useGas>
             ( USEGAS_CELL:Bool => false )
           </useGas>
           <ethereum>
             <evm>
               <callState>
                 <wordStack>
                   ( ( W0:Int => bool2Word ( W0:Int ==Int 0 ) ) : _WS:WordStack )
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
      requires ( notBool USEGAS_CELL:Bool )
      [priority(20), label(ISZERO-SUMMARY-NOGAS)]

endmodule