requires "../evm.md"

module STOP-SUMMARY
    imports public EVM
    
    rule [STOP-SUMMARY-USEGAS]: <kevm>
           <k>
             ( #next [ STOP ] => #halt )
             ~> _K_CELL:K
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
                 ( _OUTPUT_CELL:Bytes => b"" )
               </output>
               <statusCode>
                 ( _STATUSCODE_CELL:StatusCode => EVMC_SUCCESS )
               </statusCode>
               <callState>
                 <gas>
                   ( GAS_CELL:Int => ( GAS_CELL:Int -Int Gzero < SCHEDULE_CELL:Schedule > ) )
                 </gas>
                 ...
               </callState>
               ...
             </evm>
             ...
           </ethereum>
           ...
         </kevm>
      requires ( USEGAS_CELL:Bool
       andBool ( Gzero < SCHEDULE_CELL:Schedule > <=Int GAS_CELL:Int
               ))
      [priority(20), label(STOP-SUMMARY-USEGAS)]
    
    rule [STOP-SUMMARY-NOGAS]: <kevm>
           <k>
             ( #next [ STOP ] => #halt )
             ~> _K_CELL:K
           </k>
           <useGas>
             ( USEGAS_CELL:Bool => false )
           </useGas>
           <ethereum>
             <evm>
               <output>
                 ( _OUTPUT_CELL:Bytes => b"" )
               </output>
               <statusCode>
                 ( _STATUSCODE_CELL:StatusCode => EVMC_SUCCESS )
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
      requires ( notBool USEGAS_CELL:Bool )
      [priority(20), label(STOP-SUMMARY-NOGAS)]

endmodule