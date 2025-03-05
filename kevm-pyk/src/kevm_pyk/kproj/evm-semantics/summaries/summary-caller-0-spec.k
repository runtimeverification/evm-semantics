requires "../evm.md"

module SUMMARY-CALLER-0-SPEC
imports EVM
    
    
    rule [BASIC-BLOCK-3-TO-5]: <kevm>
           <k>
             ( #next [ CALLER ] => #halt )
             ~> __K_CELL:K
           </k>
           <useGas>
             false
           </useGas>
           <ethereum>
             <evm>
               <statusCode>
                 ( __STATUSCODE_CELL:StatusCode => EVMC_STACK_OVERFLOW )
               </statusCode>
               <callState>
                 <wordStack>
                   _WS:WordStack
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
      requires 1023 <Int #sizeWordStack ( _WS:WordStack , 0 )
      [priority(20), label(BASIC-BLOCK-3-TO-5)]
    
    rule [BASIC-BLOCK-4-TO-6]: <kevm>
           <k>
             ( #next [ CALLER ] ~> .K => .K )
             ~> __K_CELL:K
           </k>
           <useGas>
             false
           </useGas>
           <ethereum>
             <evm>
               <callState>
                 <caller>
                   _CALLER_CELL:Int
                 </caller>
                 <wordStack>
                   ( _WS:WordStack => ( _CALLER_CELL:Int : _WS:WordStack ) )
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
      requires ( ( notBool #sizeWordStack ( _WS:WordStack , 0 ) <Int 0 )
       andBool ( ( notBool 1023 <Int #sizeWordStack ( _WS:WordStack , 0 ) )
               ))
       ensures #sizeWordStack ( _WS:WordStack , 0 ) <=Int 1023
      [priority(20), label(BASIC-BLOCK-4-TO-6)]

endmodule