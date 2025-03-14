requires "../evm.md"
requires "../buf.md"

module SUMMARY-DUP-9-SPEC
imports EVM
imports BUF
    
    
    rule [BASIC-BLOCK-3-TO-8]: <kevm>
           <k>
             ( #next [ DUP ( 9 ) ] => #halt )
             ~> K_CELL:K
           </k>
           <ethereum>
             <evm>
               <statusCode>
                 ( STATUSCODE_CELL:StatusCode => EVMC_STACK_OVERFLOW )
               </statusCode>
               <callState>
                 <wordStack>
                   ( W0:Int : ( W1:Int : ( W2:Int : ( W3:Int : ( W4:Int : ( W5:Int : ( W6:Int : ( W7:Int : ( W8:Int : WS:WordStack ) ) ) ) ) ) ) ) )
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
      requires 1023 <Int #sizeWordStack ( WS:WordStack , 9 )
      [priority(20), label(BASIC-BLOCK-3-TO-8)]
    
    rule [BASIC-BLOCK-25-TO-24]: <kevm>
           <k>
             ( #next [ DUP ( 9 ) ] ~> .K => .K )
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
                   ( ( W0:Int => W8:Int ) : ( ( W1:Int => W0:Int ) : ( ( W2:Int => W1:Int ) : ( ( W3:Int => W2:Int ) : ( ( W4:Int => W3:Int ) : ( ( W5:Int => W4:Int ) : ( ( W6:Int => W5:Int ) : ( ( W7:Int => W6:Int ) : ( ( W8:Int => W7:Int ) : ( WS:WordStack => ( W8:Int : WS:WordStack ) ) ) ) ) ) ) ) ) ) )
                 </wordStack>
                 <pc>
                   ( PC_CELL:Int => ( PC_CELL:Int +Int 1 ) )
                 </pc>
                 <gas>
                    ( ( GAS_CELL:Int => ( GAS_CELL:Int -Int Gverylow < SCHEDULE_CELL:Schedule > ) ) )
                 </gas>
                 ...
               </callState>
               ...
             </evm>
             ...
           </ethereum>
           ...
         </kevm>
      requires ( USEGAS_CELL:Bool  andBool ( ( ( Gverylow < SCHEDULE_CELL:Schedule > ) ) ) <=Int GAS_CELL  
       andBool ( ( notBool #sizeWordStack ( WS:WordStack , 9 ) <Int 9 )
       andBool ( ( notBool 1023 <Int #sizeWordStack ( WS:WordStack , 9 ) )
               )))
       ensures #sizeWordStack ( WS:WordStack , 9 ) <=Int 1023
      [priority(20), label(BASIC-BLOCK-25-TO-24)]
    
    rule [BASIC-BLOCK-26-TO-18]: <kevm>
           <k>
             ( #next [ DUP ( 9 ) ] ~> .K => .K )
             ~> K_CELL:K
           </k>
           <useGas>
             ( USEGAS_CELL:Bool => false )
           </useGas>
           <ethereum>
             <evm>
               <callState>
                 <wordStack>
                   ( ( W0:Int => W8:Int ) : ( ( W1:Int => W0:Int ) : ( ( W2:Int => W1:Int ) : ( ( W3:Int => W2:Int ) : ( ( W4:Int => W3:Int ) : ( ( W5:Int => W4:Int ) : ( ( W6:Int => W5:Int ) : ( ( W7:Int => W6:Int ) : ( ( W8:Int => W7:Int ) : ( WS:WordStack => ( W8:Int : WS:WordStack ) ) ) ) ) ) ) ) ) ) )
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
      requires ( ( notBool USEGAS_CELL:Bool )
       andBool ( ( notBool #sizeWordStack ( WS:WordStack , 9 ) <Int 9 )
       andBool ( ( notBool 1023 <Int #sizeWordStack ( WS:WordStack , 9 ) )
               )))
       ensures #sizeWordStack ( WS:WordStack , 9 ) <=Int 1023
      [priority(20), label(BASIC-BLOCK-26-TO-18)]

endmodule