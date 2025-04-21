requires "../evm.md"

module UNDEFINED-SUMMARY
    imports public EVM
    
    rule [UNDEFINED-SUMMARY-USEGAS]: <kevm>
           <k>
             ( #next [ UNDEFINED ( _W:Int ) ] => #halt )
             ~> _K_CELL:K
           </k>
           <ethereum>
             <evm>
               <statusCode>
                 ( _STATUSCODE_CELL:StatusCode => EVMC_UNDEFINED_INSTRUCTION )
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
      [priority(20), label(UNDEFINED-SUMMARY-USEGAS)]

endmodule