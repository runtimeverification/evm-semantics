requires "../evm.md"

module SUMMARY-BALANCE-NORMAL-1-SPEC
imports EVM
    
    
    rule [BASIC-BLOCK-1-TO-3]: <kevm>
           <k>
             ( #next [ BALANCE ] ~> .K => .K )
             ~> __K_CELL:K
           </k>
           <useGas>
             false
           </useGas>
           <ethereum>
             <evm>
               <callState>
                 <wordStack>
                   ( ( W0:Int => _BALANCE_CELL:Int ) : __WS:WordStack )
                 </wordStack>
                 <pc>
                   ( _PC_CELL:Int => ( _PC_CELL:Int +Int 1 ) )
                 </pc>
                 <gas>
                   ( __GAS_CELL:Int )
                 </gas>
                 ...
               </callState>
               <substate>
                 <accessedAccounts>
                   ( _ACCESSEDACCOUNTS_CELL:Set => _ACCESSEDACCOUNTS_CELL:Set |Set SetItem ( ( W0:Int modInt pow160 ) ) )
                 </accessedAccounts>
                 ...
               </substate>
               ...
             </evm>
             <network>
               <accounts>
                 ( <account>
                   <acctID>
                     ( W0:Int modInt pow160 )
                   </acctID>
                   <balance>
                     _BALANCE_CELL:Int
                   </balance>
                   ...
                 </account>
                 DotAccountVar:AccountCellMap )
               </accounts>
               ...
             </network>
           </ethereum>
           ...
         </kevm>
      requires ( notBool <acctID>
        ( W0:Int modInt pow160 )
      </acctID> in_keys ( DotAccountVar:AccountCellMap ) )
      [priority(20), label(BASIC-BLOCK-1-TO-3)]

endmodule