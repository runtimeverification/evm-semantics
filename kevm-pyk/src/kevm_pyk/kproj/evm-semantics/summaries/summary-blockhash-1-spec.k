requires "../evm.md"

module SUMMARY-BLOCKHASH-1-SPEC
imports EVM
    
    
    rule [BASIC-BLOCK-8-TO-7]: <kevm>
           <k>
             ( #next [ BLOCKHASH ] ~> .K => .K )
             ~> __K_CELL:K
           </k>
           <schedule>
             _SCHEDULE_CELL:Schedule
           </schedule>
           <useGas>
             ( _USEGAS_CELL:Bool => true )
           </useGas>
           <ethereum>
             <evm>
               <callState>
                 <wordStack>
                   ( ( _W0:Int => #blockhash ( _BLOCKHASHES_CELL:List , _W0:Int , ( _NUMBER_CELL:Int +Int -1 ) , 0 ) ) : __WS:WordStack )
                 </wordStack>
                 <pc>
                   ( _PC_CELL:Int => ( _PC_CELL:Int +Int 1 ) )
                 </pc>
                 <gas>
                   ( ( _GAS_CELL:Int => ( _GAS_CELL:Int -Int Gblockhash < _SCHEDULE_CELL:Schedule > ) ) )
                 </gas>
                 ...
               </callState>
               <blockhashes>
                 _BLOCKHASHES_CELL:List
               </blockhashes>
               <block>
                 <number>
                   _NUMBER_CELL:Int
                 </number>
                 ...
               </block>
               ...
             </evm>
             ...
           </ethereum>
           ...
         </kevm>
      requires _USEGAS_CELL:Bool
      [priority(20), label(BASIC-BLOCK-8-TO-7)]
    
    rule [BASIC-BLOCK-9-TO-6]: <kevm>
           <k>
             ( #next [ BLOCKHASH ] ~> .K => .K )
             ~> __K_CELL:K
           </k>
           <useGas>
             ( _USEGAS_CELL:Bool => false )
           </useGas>
           <ethereum>
             <evm>
               <callState>
                 <wordStack>
                   ( ( _W0:Int => #blockhash ( _BLOCKHASHES_CELL:List , _W0:Int , ( _NUMBER_CELL:Int +Int -1 ) , 0 ) ) : __WS:WordStack )
                 </wordStack>
                 <pc>
                   ( _PC_CELL:Int => ( _PC_CELL:Int +Int 1 ) )
                 </pc>
                 <gas>
                   ( __GAS_CELL:Int )
                 </gas>
                 ...
               </callState>
               <blockhashes>
                 _BLOCKHASHES_CELL:List
               </blockhashes>
               <block>
                 <number>
                   _NUMBER_CELL:Int
                 </number>
                 ...
               </block>
               ...
             </evm>
             ...
           </ethereum>
           ...
         </kevm>
      requires ( notBool _USEGAS_CELL:Bool )
      [priority(20), label(BASIC-BLOCK-9-TO-6)]

endmodule