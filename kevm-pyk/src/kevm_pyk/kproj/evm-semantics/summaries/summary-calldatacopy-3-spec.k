requires "../evm.md"

module SUMMARY-CALLDATACOPY-3-SPEC
imports EVM
    
    
    rule [BASIC-BLOCK-8-TO-7]: <kevm>
           <k>
             ( #next [ CALLDATACOPY ] ~> .K => .K )
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
                 <callData>
                   _CALLDATA_CELL:Bytes
                 </callData>
                 <wordStack>
                   ( ( _W0:Int : ( _W1:Int : ( _W2:Int : _WS:WordStack ) ) ) => _WS:WordStack )
                 </wordStack>
                 <localMem>
                   ( _LOCALMEM_CELL:Bytes => _LOCALMEM_CELL:Bytes [ _W0:Int := #range ( _CALLDATA_CELL:Bytes , _W1:Int , _W2:Int ) ] )
                 </localMem>
                 <pc>
                   ( _PC_CELL:Int => ( _PC_CELL:Int +Int 1 ) )
                 </pc>
                 <gas>
                   ( ( _GAS_CELL:Int => ( ( _GAS_CELL:Int -Int ( Cmem ( _SCHEDULE_CELL:Schedule , #memoryUsageUpdate ( _MEMORYUSED_CELL:Int , _W0:Int , _W2:Int ) ) -Int Cmem ( _SCHEDULE_CELL:Schedule , _MEMORYUSED_CELL:Int ) ) ) -Int ( Gverylow < _SCHEDULE_CELL:Schedule > +Int ( Gcopy < _SCHEDULE_CELL:Schedule > *Int ( _W2:Int up/Int 32 ) ) ) ) ) )
                 </gas>
                 <memoryUsed>
                   ( _MEMORYUSED_CELL:Int => #memoryUsageUpdate ( _MEMORYUSED_CELL:Int , _W0:Int , _W2:Int ) )
                 </memoryUsed>
                 ...
               </callState>
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
             ( #next [ CALLDATACOPY ] ~> .K => .K )
             ~> __K_CELL:K
           </k>
           <useGas>
             ( _USEGAS_CELL:Bool => false )
           </useGas>
           <ethereum>
             <evm>
               <callState>
                 <callData>
                   _CALLDATA_CELL:Bytes
                 </callData>
                 <wordStack>
                   ( ( _W0:Int : ( _W1:Int : ( _W2:Int : _WS:WordStack ) ) ) => _WS:WordStack )
                 </wordStack>
                 <localMem>
                   ( _LOCALMEM_CELL:Bytes => _LOCALMEM_CELL:Bytes [ _W0:Int := #range ( _CALLDATA_CELL:Bytes , _W1:Int , _W2:Int ) ] )
                 </localMem>
                 <pc>
                   ( _PC_CELL:Int => ( _PC_CELL:Int +Int 1 ) )
                 </pc>
                 <gas>
                   ( __GAS_CELL:Int )
                 </gas>
                 ...
               </callState>
               ...
             </evm>
             ...
           </ethereum>
           ...
         </kevm>
      requires ( notBool _USEGAS_CELL:Bool )
      [priority(20), label(BASIC-BLOCK-9-TO-6)]

endmodule