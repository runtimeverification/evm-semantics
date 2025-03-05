requires "../evm.md"

module SUMMARY-EXP-2-SPEC
imports EVM
    
    
    rule [BASIC-BLOCK-13-TO-9]: <kevm>
           <k>
             ( #next [ EXP ] ~> .K => .K )
             ~> __K_CELL:K
           </k>
           <useGas>
             ( _USEGAS_CELL:Bool => false )
           </useGas>
           <ethereum>
             <evm>
               <callState>
                 <wordStack>
                   ( ( _W0:Int => powmod ( _W0:Int , _W1:Int , pow256 ) ) : ( ( _W1:Int : _WS:WordStack ) => _WS:WordStack ) )
                 </wordStack>
                 <pc>
                   ( _PC_CELL:Int => ( _PC_CELL:Int +Int 1 ) )
                 </pc>
                 <gas>
                   ( __GAS_CELL:Int )
                 </gas>
                 ...
               </callState>
               ...
             </evm>
             ...
           </ethereum>
           ...
         </kevm>
      requires ( notBool _USEGAS_CELL:Bool )
      [priority(20), label(BASIC-BLOCK-13-TO-9)]
    
    rule [BASIC-BLOCK-16-TO-11]: <kevm>
           <k>
             ( #next [ EXP ] ~> .K => .K )
             ~> __K_CELL:K
           </k>
           <schedule>
             _SCHEDULE_CELL:Schedule
           </schedule>
           <useGas>
             ( _USEGAS_CELL:Bool => true )
           </useGas>
           <ethereum>
             <evm>
               <callState>
                 <wordStack>
                   ( ( _W0:Int => powmod ( _W0:Int , _W1:Int , pow256 ) ) : ( ( _W1:Int : _WS:WordStack ) => _WS:WordStack ) )
                 </wordStack>
                 <pc>
                   ( _PC_CELL:Int => ( _PC_CELL:Int +Int 1 ) )
                 </pc>
                 <gas>
                   ( ( _GAS_CELL:Int => ( _GAS_CELL:Int -Int Gexp < _SCHEDULE_CELL:Schedule > ) ) )
                 </gas>
                 ...
               </callState>
               ...
             </evm>
             ...
           </ethereum>
           ...
         </kevm>
      requires ( _USEGAS_CELL:Bool
       andBool ( _W1:Int <=Int 0
               ))
      [priority(20), label(BASIC-BLOCK-16-TO-11)]
    
    rule [BASIC-BLOCK-17-TO-10]: <kevm>
           <k>
             ( #next [ EXP ] ~> .K => .K )
             ~> __K_CELL:K
           </k>
           <schedule>
             _SCHEDULE_CELL:Schedule
           </schedule>
           <useGas>
             ( _USEGAS_CELL:Bool => true )
           </useGas>
           <ethereum>
             <evm>
               <callState>
                 <wordStack>
                   ( ( _W0:Int => powmod ( _W0:Int , _W1:Int , pow256 ) ) : ( ( _W1:Int : _WS:WordStack ) => _WS:WordStack ) )
                 </wordStack>
                 <pc>
                   ( _PC_CELL:Int => ( _PC_CELL:Int +Int 1 ) )
                 </pc>
                 <gas>
                   ( ( _GAS_CELL:Int => ( _GAS_CELL:Int -Int ( Gexp < _SCHEDULE_CELL:Schedule > +Int ( Gexpbyte < _SCHEDULE_CELL:Schedule > *Int ( ( log2Int ( _W1:Int ) /Int 8 ) +Int 1 ) ) ) ) ) )
                 </gas>
                 ...
               </callState>
               ...
             </evm>
             ...
           </ethereum>
           ...
         </kevm>
      requires ( _USEGAS_CELL:Bool
       andBool ( 0 <Int _W1:Int
               ))
      [priority(20), label(BASIC-BLOCK-17-TO-10)]

endmodule