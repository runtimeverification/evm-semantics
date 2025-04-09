requires "../evm.md"

module UNDEFINED-SUMMARY
    imports public EVM
    
    rule [UNDEFINED-SUMMARY-USEGAS]: <kevm>
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
                   GAS_CELL:Int
                 </gas>
                 ...
               </callState>
               ...
             </evm>
             ...
           </ethereum>
           ...
         </kevm>
      [priority(20), label(UNDEFINED-SUMMARY-USEGAS)]

endmodule