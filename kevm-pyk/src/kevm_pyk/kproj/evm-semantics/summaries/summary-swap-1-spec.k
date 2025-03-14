requires "../evm.md"
requires "../buf.md"

module SUMMARY-SWAP-1-SPEC
imports EVM
imports BUF
    
    
    rule [BASIC-BLOCK-3-TO-7]: <kevm>
           <k>
             ( #next [ SWAP ( 1 ) ] => #halt )
             ~> K_CELL:K
           </k>
           <ethereum>
             <evm>
               <statusCode>
                 ( STATUSCODE_CELL:StatusCode => EVMC_STACK_UNDERFLOW )
               </statusCode>
               <callState>
                 <wordStack>
                   ( W0:Int : WS:WordStack )
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
      requires #sizeWordStack ( WS:WordStack , 1 ) <Int 2
      [priority(20), label(BASIC-BLOCK-3-TO-7)]
    
    rule [BASIC-BLOCK-25-TO-24]: <kevm>
           <k>
             ( #next [ SWAP ( 1 ) ] ~> .K => .K )
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
                   ( ( W0:Int => WS:WordStack [ 0 ] ) : ( WS:WordStack => WS:WordStack [ 0 := W0:Int ] ) )
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
       andBool ( 2 <=Int #sizeWordStack ( WS:WordStack , 1 )
               ))
      [priority(20), label(BASIC-BLOCK-25-TO-24)]
    
    rule [BASIC-BLOCK-26-TO-19]: <kevm>
           <k>
             ( #next [ SWAP ( 1 ) ] ~> .K => .K )
             ~> K_CELL:K
           </k>
           <useGas>
             ( USEGAS_CELL:Bool => false )
           </useGas>
           <ethereum>
             <evm>
               <callState>
                 <wordStack>
                   ( ( W0:Int => WS:WordStack [ 0 ] ) : ( WS:WordStack => WS:WordStack [ 0 := W0:Int ] ) )
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
       andBool ( 2 <=Int #sizeWordStack ( WS:WordStack , 1 )
               ))
      [priority(20), label(BASIC-BLOCK-26-TO-19)]

endmodule