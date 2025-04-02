requires "../evm.md"

module EXP-SUMMARY
    imports public EVM
    
    rule [EXP-SUMMARY-NOGAS]: <kevm>
           <k>
             ( #next [ EXP ] ~> .K => .K )
             ~> K_CELL:K
           </k>
           <useGas>
             ( USEGAS_CELL:Bool => false )
           </useGas>
           <ethereum>
             <evm>
               <callState>
                 <wordStack>
                   ( ( W0:Int => powmod ( W0:Int , W1:Int , pow256 ) ) : ( ( W1:Int : WS:WordStack ) => WS:WordStack ) )
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
      [priority(20), label(EXP-SUMMARY-NOGAS)]
    
    rule [EXP-SUMMARY-USEGAS-LE0]: <kevm>
           <k>
             ( #next [ EXP ] ~> .K => .K )
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
                   ( ( W0:Int => powmod ( W0:Int , W1:Int , pow256 ) ) : ( ( W1:Int : WS:WordStack ) => WS:WordStack ) )
                 </wordStack>
                 <pc>
                   ( PC_CELL:Int => ( PC_CELL:Int +Int 1 ) )
                 </pc>
                 <gas>
                   ( GAS_CELL:Int => ( GAS_CELL:Int -Int Gexp < SCHEDULE_CELL:Schedule > ) )
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
       andBool ( W1:Int <=Int 0
       andBool ( Gexp < SCHEDULE_CELL:Schedule > <=Int GAS_CELL:Int
               )))
      [priority(20), label(EXP-SUMMARY-USEGAS-LE0)]
    
    rule [EXP-SUMMARY-USEGAS]: <kevm>
           <k>
             ( #next [ EXP ] ~> .K => .K )
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
                   ( ( W0:Int => powmod ( W0:Int , W1:Int , pow256 ) ) : ( ( W1:Int : WS:WordStack ) => WS:WordStack ) )
                 </wordStack>
                 <pc>
                   ( PC_CELL:Int => ( PC_CELL:Int +Int 1 ) )
                 </pc>
                 <gas>
                   ( GAS_CELL:Int => ( GAS_CELL:Int -Int ( Gexp < SCHEDULE_CELL:Schedule > +Int ( Gexpbyte < SCHEDULE_CELL:Schedule > *Int ( ( log2Int ( W1:Int ) /Int 8 ) +Int 1 ) ) ) ) )
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
       andBool ( 0 <Int W1:Int
       andBool ( ( Gexp < SCHEDULE_CELL:Schedule > +Int ( Gexpbyte < SCHEDULE_CELL:Schedule > *Int ( ( log2Int ( W1:Int ) /Int 8 ) +Int 1 ) ) ) <=Int GAS_CELL:Int
               )))
      [priority(20), label(EXP-SUMMARY-USEGAS)]

endmodule