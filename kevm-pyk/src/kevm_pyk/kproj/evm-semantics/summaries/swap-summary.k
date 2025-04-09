requires "../evm.md"

module SWAP-SUMMARY
    imports public EVM
    
    rule [SWAP-SUMMARY-USEGAS]: <kevm>
           <k>
             ( #next [ SWAP ( N:Int ) ] ~> .K => .K )
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
                   ( ( W0:Int => WS:WordStack [ ( N:Int +Int -1 ) ] ) : ( WS:WordStack => WS:WordStack [ ( N:Int +Int -1 ) := W0:Int ] ) )
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
       andBool ( ( N:Int +Int 1 ) <=Int #sizeWordStack ( WS:WordStack , 1 )
       andBool ( Gverylow < SCHEDULE_CELL:Schedule > <=Int GAS_CELL:Int
               )))
      [priority(20), label(SWAP-SUMMARY-USEGAS)]
    
    rule [SWAP-SUMMARY-NOGAS]: <kevm>
           <k>
             ( #next [ SWAP ( N:Int ) ] ~> .K => .K )
             ~> K_CELL:K
           </k>
           <useGas>
             ( USEGAS_CELL:Bool => false )
           </useGas>
           <ethereum>
             <evm>
               <callState>
                 <wordStack>
                   ( ( W0:Int => WS:WordStack [ ( N:Int +Int -1 ) ] ) : ( WS:WordStack => WS:WordStack [ ( N:Int +Int -1 ) := W0:Int ] ) )
                 </wordStack>
                 <pc>
                   ( PC_CELL:Int => ( PC_CELL:Int +Int 1 ) )
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
       andBool ( ( N:Int +Int 1 ) <=Int #sizeWordStack ( WS:WordStack , 1 )
               ))
      [priority(20), label(SWAP-SUMMARY-NOGAS)]

endmodule