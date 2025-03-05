requires "../evm.md"

module SUMMARY-CALLER-0-SPEC
imports EVM
    
    
    rule [BASIC-BLOCK-3-TO-5]: <kevm>
           <k>
             ( #next [ CALLER ] => #halt )
             ~> K_CELL:K
           </k>
           <useGas>
             false
           </useGas>
           <ethereum>
             <evm>
               <statusCode>
                 ( STATUSCODE_CELL:StatusCode => EVMC_STACK_OVERFLOW )
               </statusCode>
               <callState>
                 <wordStack>
                   WS:WordStack
                 </wordStack>
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
      requires 1023 <Int #sizeWordStack ( WS:WordStack , 0 )
      [priority(20), label(BASIC-BLOCK-3-TO-5)]
    
    rule [BASIC-BLOCK-4-TO-6]: <kevm>
           <k>
             ( #next [ CALLER ] ~> .K => .K )
             ~> K_CELL:K
           </k>
           <useGas>
             false
           </useGas>
           <ethereum>
             <evm>
               <callState>
                 <caller>
                   CALLER_CELL:Int
                 </caller>
                 <wordStack>
                   ( WS:WordStack => ( CALLER_CELL:Int : WS:WordStack ) )
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
      requires ( ( notBool #sizeWordStack ( WS:WordStack , 0 ) <Int 0 )
       andBool ( ( notBool 1023 <Int #sizeWordStack ( WS:WordStack , 0 ) )
               ))
       ensures #sizeWordStack ( WS:WordStack , 0 ) <=Int 1023
      [priority(20), label(BASIC-BLOCK-4-TO-6)]

endmodule