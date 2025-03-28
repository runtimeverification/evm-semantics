requires "../evm.md"

module CALLDATALOAD-SUMMARY
    imports public EVM
    
    rule [CALLDATALOAD-SUMMARY-0]: <kevm>
           <k>
             ( #next [ CALLDATALOAD ] ~> .K => .K )
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
                 <callData>
                   CALLDATA_CELL:Bytes
                 </callData>
                 <wordStack>
                   ( ( W0:Int => #asWord ( #range ( CALLDATA_CELL:Bytes , W0:Int , 32 ) ) ) : WS:WordStack )
                 </wordStack>
                 <pc>
                   ( PC_CELL:Int => ( PC_CELL:Int +Int 1 ) )
                 </pc>
                 <gas>
                   ( GAS_CELL:Int => ( GAS_CELL:Int -Int Gverylow < SCHEDULE_CELL:Schedule > ) )
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
       andBool ( Gverylow < SCHEDULE_CELL:Schedule > <=Int GAS_CELL:Int
               ))
      [priority(20), label(CALLDATALOAD-SUMMARY-0)]
    
    rule [CALLDATALOAD-SUMMARY-1]: <kevm>
           <k>
             ( #next [ CALLDATALOAD ] ~> .K => .K )
             ~> K_CELL:K
           </k>
           <useGas>
             ( USEGAS_CELL:Bool => false )
           </useGas>
           <ethereum>
             <evm>
               <callState>
                 <callData>
                   CALLDATA_CELL:Bytes
                 </callData>
                 <wordStack>
                   ( ( W0:Int => #asWord ( #range ( CALLDATA_CELL:Bytes , W0:Int , 32 ) ) ) : WS:WordStack )
                 </wordStack>
                 <pc>
                   ( PC_CELL:Int => ( PC_CELL:Int +Int 1 ) )
                 </pc>
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
      requires ( notBool USEGAS_CELL:Bool )
      [priority(20), label(CALLDATALOAD-SUMMARY-1)]

endmodule