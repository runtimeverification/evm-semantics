requires "../evm.md"

module SUMMARY-UNDEFINED-0-SPEC
imports EVM
    
    
    rule [BASIC-BLOCK-1-TO-3]: <kevm>
           <k>
             ( #next [ UNDEFINED ( W:Int ) ] => #halt )
             ~> K_CELL:K
           </k>
           <ethereum>
             <evm>
               <statusCode>
                 ( STATUSCODE_CELL:StatusCode => EVMC_UNDEFINED_INSTRUCTION )
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
      [priority(20), label(BASIC-BLOCK-1-TO-3)]

endmodule