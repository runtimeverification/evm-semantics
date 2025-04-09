requires "../evm.md"

module MULMOD-SUMMARY
    imports public EVM
    
    rule [MULMOD-SUMMARY-USEGAS]: <kevm>
           <k>
             ( #next [ MULMOD ] ~> .K => .K )
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
                   ( ( W0:Int => ( W0:Int *Int W1:Int ) %Word W2:Int ) : ( ( W1:Int : ( W2:Int : WS:WordStack ) ) => WS:WordStack ) )
                 </wordStack>
                 <pc>
                   ( PC_CELL:Int => ( PC_CELL:Int +Int 1 ) )
                 </pc>
                 <gas>
                   ( GAS_CELL:Int => ( GAS_CELL:Int -Int Gmid < SCHEDULE_CELL:Schedule > ) )
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
       andBool ( Gmid < SCHEDULE_CELL:Schedule > <=Int GAS_CELL:Int
               ))
      [priority(20), label(MULMOD-SUMMARY-USEGAS)]
    
    rule [MULMOD-SUMMARY-NOGAS]: <kevm>
           <k>
             ( #next [ MULMOD ] ~> .K => .K )
             ~> K_CELL:K
           </k>
           <useGas>
             ( USEGAS_CELL:Bool => false )
           </useGas>
           <ethereum>
             <evm>
               <callState>
                 <wordStack>
                   ( ( W0:Int => ( W0:Int *Int W1:Int ) %Word W2:Int ) : ( ( W1:Int : ( W2:Int : WS:WordStack ) ) => WS:WordStack ) )
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
      requires ( notBool USEGAS_CELL:Bool )
      [priority(20), label(MULMOD-SUMMARY-NOGAS)]

endmodule