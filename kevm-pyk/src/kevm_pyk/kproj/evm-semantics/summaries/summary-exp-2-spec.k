requires "../evm.md"
requires "../buf.md"

module SUMMARY-EXP-2-SPEC
imports EVM
imports BUF
    
    
    rule [BASIC-BLOCK-30-TO-14]: <kevm>
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
      [priority(20), label(BASIC-BLOCK-30-TO-14)]
    
    rule [BASIC-BLOCK-33-TO-27]: <kevm>
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
                    ( ( GAS_CELL:Int => ( GAS_CELL:Int -Int Gexp < SCHEDULE_CELL:Schedule > ) ) )
                 </gas>
                 ...
               </callState>
               ...
             </evm>
             ...
           </ethereum>
           ...
         </kevm>
      requires ( USEGAS_CELL:Bool  andBool ( ( ( Gexp < SCHEDULE_CELL:Schedule > ) ) ) <=Int GAS_CELL  
       andBool ( W1:Int <=Int 0
               ))
      [priority(20), label(BASIC-BLOCK-33-TO-27)]
    
    rule [BASIC-BLOCK-34-TO-28]: <kevm>
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
                    ( ( GAS_CELL:Int => ( GAS_CELL:Int -Int ( Gexp < SCHEDULE_CELL:Schedule > +Int ( Gexpbyte < SCHEDULE_CELL:Schedule > *Int ( ( log2Int ( W1:Int ) /Int 8 ) +Int 1 ) ) ) ) ) )
                 </gas>
                 ...
               </callState>
               ...
             </evm>
             ...
           </ethereum>
           ...
         </kevm>
      requires ( USEGAS_CELL:Bool  andBool ( ( ( ( Gexp < SCHEDULE_CELL:Schedule > +Int ( Gexpbyte < SCHEDULE_CELL:Schedule > *Int ( ( log2Int ( W1:Int ) /Int 8 ) +Int 1 ) ) ) ) ) ) <=Int GAS_CELL  
       andBool ( 0 <Int W1:Int
               ))
      [priority(20), label(BASIC-BLOCK-34-TO-28)]

endmodule