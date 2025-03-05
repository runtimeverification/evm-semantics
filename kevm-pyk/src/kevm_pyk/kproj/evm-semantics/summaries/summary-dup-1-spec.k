requires "../evm.md"

module SUMMARY-DUP-1-SPEC
imports EVM
    
    
    rule [BASIC-BLOCK-3-TO-8]: <kevm>
           <k>
             ( #next [ DUP ( 1 ) ] => #halt )
             ~> __K_CELL:K
           </k>
           <ethereum>
             <evm>
               <statusCode>
                 ( __STATUSCODE_CELL:StatusCode => EVMC_STACK_OVERFLOW )
               </statusCode>
               <callState>
                 <wordStack>
                   ( __W0:Int : _WS:WordStack )
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
      requires 1023 <Int #sizeWordStack ( _WS:WordStack , 1 )
      [priority(20), label(BASIC-BLOCK-3-TO-8)]
    
    rule [BASIC-BLOCK-11-TO-10]: <kevm>
           <k>
             ( #next [ DUP ( 1 ) ] ~> .K => .K )
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
                   ( _W0:Int : ( _WS:WordStack => ( _W0:Int : _WS:WordStack ) ) )
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
       andBool ( ( notBool #sizeWordStack ( _WS:WordStack , 1 ) <Int 1 )
       andBool ( ( notBool 1023 <Int #sizeWordStack ( _WS:WordStack , 1 ) )
               )))
       ensures #sizeWordStack ( _WS:WordStack , 1 ) <=Int 1023
      [priority(20), label(BASIC-BLOCK-11-TO-10)]
    
    rule [BASIC-BLOCK-12-TO-9]: <kevm>
           <k>
             ( #next [ DUP ( 1 ) ] ~> .K => .K )
             ~> __K_CELL:K
           </k>
           <useGas>
             ( _USEGAS_CELL:Bool => false )
           </useGas>
           <ethereum>
             <evm>
               <callState>
                 <wordStack>
                   ( _W0:Int : ( _WS:WordStack => ( _W0:Int : _WS:WordStack ) ) )
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
       andBool ( ( notBool #sizeWordStack ( _WS:WordStack , 1 ) <Int 1 )
       andBool ( ( notBool 1023 <Int #sizeWordStack ( _WS:WordStack , 1 ) )
               )))
       ensures #sizeWordStack ( _WS:WordStack , 1 ) <=Int 1023
      [priority(20), label(BASIC-BLOCK-12-TO-9)]

endmodule