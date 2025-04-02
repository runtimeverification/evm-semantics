requires "../evm.md"

module SELFBALANCE-SUMMARY
    imports public EVM
    
    rule [SELFBALANCE-SUMMARY-0]: <kevm>
           <k>
             ( #next [ SELFBALANCE ] => #halt )
             ~> K_CELL:K
           </k>
           <ethereum>
             <evm>
               <statusCode>
                 ( STATUSCODE_CELL:StatusCode => EVMC_STACK_OVERFLOW )
               </statusCode>
               <callState>
                 <id>
                   ID_CELL:Int
                 </id>
                 <wordStack>
                   WS:WordStack
                 </wordStack>
                 <gas>
                   GAS_CELL:Int
                 </gas>
                 ...
               </callState>
               ...
             </evm>
             <network>
               <accounts>
                 <account>
                   <acctID>
                     ID_CELL:Int
                   </acctID>
                   ...
                 </account>
                 ...
               </accounts>
               ...
             </network>
           </ethereum>
           ...
         </kevm>
      requires 1023 <Int #sizeWordStack ( WS:WordStack , 0 )
      [priority(20), label(SELFBALANCE-SUMMARY-0)]
    
    rule [SELFBALANCE-SUMMARY-1]: <kevm>
           <k>
             ( #next [ SELFBALANCE ] ~> .K => .K )
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
                 <id>
                   ID_CELL:Int
                 </id>
                 <wordStack>
                   ( WS:WordStack => ( BALANCE_CELL:Int : WS:WordStack ) )
                 </wordStack>
                 <pc>
                   ( PC_CELL:Int => ( PC_CELL:Int +Int 1 ) )
                 </pc>
                 <gas>
                   ( GAS_CELL:Int => ( GAS_CELL:Int -Int Glow < SCHEDULE_CELL:Schedule > ) )
                 </gas>
                 ...
               </callState>
               ...
             </evm>
             <network>
               <accounts>
                 <account>
                   <acctID>
                     ID_CELL:Int
                   </acctID>
                   <balance>
                     BALANCE_CELL:Int
                   </balance>
                   ...
                 </account>
                 ...
               </accounts>
               ...
             </network>
           </ethereum>
           ...
         </kevm>
      requires ( USEGAS_CELL:Bool
       andBool ( ( notBool #sizeWordStack ( WS:WordStack , 0 ) <Int 0 )
       andBool ( ( notBool 1023 <Int #sizeWordStack ( WS:WordStack , 0 ) )
       andBool ( Glow < SCHEDULE_CELL:Schedule > <=Int GAS_CELL:Int
               ))))
       ensures #sizeWordStack ( WS:WordStack , 0 ) <=Int 1023
      [priority(20), label(SELFBALANCE-SUMMARY-1)]
    
    rule [SELFBALANCE-SUMMARY-2]: <kevm>
           <k>
             ( #next [ SELFBALANCE ] ~> .K => .K )
             ~> K_CELL:K
           </k>
           <useGas>
             ( USEGAS_CELL:Bool => false )
           </useGas>
           <ethereum>
             <evm>
               <callState>
                 <id>
                   ID_CELL:Int
                 </id>
                 <wordStack>
                   ( WS:WordStack => ( BALANCE_CELL:Int : WS:WordStack ) )
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
             <network>
               <accounts>
                 <account>
                   <acctID>
                     ID_CELL:Int
                   </acctID>
                   <balance>
                     BALANCE_CELL:Int
                   </balance>
                   ...
                 </account>
                 ...
               </accounts>
               ...
             </network>
           </ethereum>
           ...
         </kevm>
      requires ( ( notBool USEGAS_CELL:Bool )
       andBool ( ( notBool #sizeWordStack ( WS:WordStack , 0 ) <Int 0 )
       andBool ( ( notBool 1023 <Int #sizeWordStack ( WS:WordStack , 0 ) )
               )))
       ensures #sizeWordStack ( WS:WordStack , 0 ) <=Int 1023
      [priority(20), label(SELFBALANCE-SUMMARY-2)]

endmodule