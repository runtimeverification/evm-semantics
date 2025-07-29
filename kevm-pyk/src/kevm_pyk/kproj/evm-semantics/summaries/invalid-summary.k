requires "../evm.md"

module INVALID-SUMMARY
    imports public EVM
    
    rule [INVALID-SUMMARY-USEGAS]: <kevm>
           <k>
             ( #next [ INVALID ] => #halt )
             ~> _K_CELL:K
           </k>
           <ethereum>
             <evm>
               <statusCode>
                 ( _STATUSCODE_CELL:StatusCode => EVMC_INVALID_INSTRUCTION )
               </statusCode>
               <callState>
                 <gas>
                   _GAS_CELL:Int
                 </gas>
                 ...
               </callState>
               ...
             </evm>
             ...
           </ethereum>
           ...
         </kevm>
      [priority(20), label(INVALID-SUMMARY-USEGAS)]

endmodule