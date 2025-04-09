requires "../evm.md"

module CALLDATASIZE-SUMMARY
    imports public EVM
    
    rule [CALLDATASIZE-SUMMARY-USEGAS]: <kevm>
           <k>
             ( #next [ CALLDATASIZE ] ~> .K => .K )
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
                   ( WS:WordStack => ( lengthBytes ( CALLDATA_CELL:Bytes ) : WS:WordStack ) )
                 </wordStack>
                 <pc>
                   ( PC_CELL:Int => ( PC_CELL:Int +Int 1 ) )
                 </pc>
                 <gas>
                   ( GAS_CELL:Int => ( GAS_CELL:Int -Int Gbase < SCHEDULE_CELL:Schedule > ) )
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
       andBool ( #sizeWordStack ( WS:WordStack , 0 ) <=Int 1023
       andBool ( Gbase < SCHEDULE_CELL:Schedule > <=Int GAS_CELL:Int
               )))
      [priority(20), label(CALLDATASIZE-SUMMARY-USEGAS)]
    
    rule [CALLDATASIZE-SUMMARY-NOGAS]: <kevm>
           <k>
             ( #next [ CALLDATASIZE ] ~> .K => .K )
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
                   ( WS:WordStack => ( lengthBytes ( CALLDATA_CELL:Bytes ) : WS:WordStack ) )
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
      requires ( ( notBool USEGAS_CELL:Bool )
       andBool ( #sizeWordStack ( WS:WordStack , 0 ) <=Int 1023
               ))
      [priority(20), label(CALLDATASIZE-SUMMARY-NOGAS)]

endmodule