requires "../evm.md"
requires "../buf.md"

module SUMMARY-STOP-0-SPEC
imports EVM
imports BUF
    
    
    rule [BASIC-BLOCK-21-TO-20]: <kevm>
           <k>
             ( #next [ STOP ] => #halt )
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
               <output>
                 ( OUTPUT_CELL:Bytes => b"" )
               </output>
               <statusCode>
                 ( STATUSCODE_CELL:StatusCode => EVMC_SUCCESS )
               </statusCode>
               <callState>
                 <gas>
                    ( ( GAS_CELL:Int => ( GAS_CELL:Int -Int Gzero < SCHEDULE_CELL:Schedule > ) ) )
                 </gas>
                 ...
               </callState>
               ...
             </evm>
             ...
           </ethereum>
           ...
         </kevm>
      requires USEGAS_CELL:Bool  andBool ( ( ( Gzero < SCHEDULE_CELL:Schedule > ) ) ) <=Int GAS_CELL 
      [priority(20), label(BASIC-BLOCK-21-TO-20)]
    
    rule [BASIC-BLOCK-22-TO-14]: <kevm>
           <k>
             ( #next [ STOP ] => #halt )
             ~> K_CELL:K
           </k>
           <useGas>
             ( USEGAS_CELL:Bool => false )
           </useGas>
           <ethereum>
             <evm>
               <output>
                 ( OUTPUT_CELL:Bytes => b"" )
               </output>
               <statusCode>
                 ( STATUSCODE_CELL:StatusCode => EVMC_SUCCESS )
               </statusCode>
               <callState>
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
      [priority(20), label(BASIC-BLOCK-22-TO-14)]

endmodule