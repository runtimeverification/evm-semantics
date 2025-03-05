requires "../evm.md"

module SUMMARY-SWAP-12-SPEC
imports EVM
    
    
    rule [BASIC-BLOCK-3-TO-8]: <kevm>
           <k>
             ( #next [ SWAP ( 12 ) ] => #halt )
             ~> __K_CELL:K
           </k>
           <ethereum>
             <evm>
               <statusCode>
                 ( __STATUSCODE_CELL:StatusCode => EVMC_STACK_UNDERFLOW )
               </statusCode>
               <callState>
                 <wordStack>
                   ( __W0:Int : ( __W1:Int : ( __W2:Int : ( __W3:Int : ( __W4:Int : ( __W5:Int : ( __W6:Int : ( __W7:Int : ( __W8:Int : ( __W9:Int : ( __W10:Int : ( __W11:Int : _WS:WordStack ) ) ) ) ) ) ) ) ) ) ) )
                 </wordStack>
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
      requires #sizeWordStack ( _WS:WordStack , 12 ) <Int 13
      [priority(20), label(BASIC-BLOCK-3-TO-8)]
    
    rule [BASIC-BLOCK-11-TO-9]: <kevm>
           <k>
             ( #next [ SWAP ( 12 ) ] ~> .K => .K )
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
                   ( ( _W0:Int => _WS:WordStack [ 0 ] ) : ( __W1:Int : ( __W2:Int : ( __W3:Int : ( __W4:Int : ( __W5:Int : ( __W6:Int : ( __W7:Int : ( __W8:Int : ( __W9:Int : ( __W10:Int : ( __W11:Int : ( _WS:WordStack => _WS:WordStack [ 0 := _W0:Int ] ) ) ) ) ) ) ) ) ) ) ) ) )
                 </wordStack>
                 <pc>
                   ( _PC_CELL:Int => ( _PC_CELL:Int +Int 1 ) )
                 </pc>
                 <gas>
                   ( ( _GAS_CELL:Int => ( _GAS_CELL:Int -Int Gverylow < _SCHEDULE_CELL:Schedule > ) ) )
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
       andBool ( 13 <=Int #sizeWordStack ( _WS:WordStack , 12 )
               ))
      [priority(20), label(BASIC-BLOCK-11-TO-9)]
    
    rule [BASIC-BLOCK-12-TO-10]: <kevm>
           <k>
             ( #next [ SWAP ( 12 ) ] ~> .K => .K )
             ~> __K_CELL:K
           </k>
           <useGas>
             ( _USEGAS_CELL:Bool => false )
           </useGas>
           <ethereum>
             <evm>
               <callState>
                 <wordStack>
                   ( ( _W0:Int => _WS:WordStack [ 0 ] ) : ( __W1:Int : ( __W2:Int : ( __W3:Int : ( __W4:Int : ( __W5:Int : ( __W6:Int : ( __W7:Int : ( __W8:Int : ( __W9:Int : ( __W10:Int : ( __W11:Int : ( _WS:WordStack => _WS:WordStack [ 0 := _W0:Int ] ) ) ) ) ) ) ) ) ) ) ) ) )
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
      requires ( ( notBool _USEGAS_CELL:Bool )
       andBool ( 13 <=Int #sizeWordStack ( _WS:WordStack , 12 )
               ))
      [priority(20), label(BASIC-BLOCK-12-TO-10)]

endmodule