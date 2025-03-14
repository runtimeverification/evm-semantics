requires "../evm.md"
requires "../buf.md"

module SUMMARY-BALANCE-NORMAL-1-SPEC
imports EVM
imports BUF
    
    
    rule [BASIC-BLOCK-1-TO-10]: <kevm>
           <k>
             ( #next [ BALANCE ] ~> .K => .K )
             ~> K_CELL:K
           </k>
           <useGas>
             false
           </useGas>
           <ethereum>
             <evm>
               <callState>
                 <wordStack>
                   ( ( W0:Int => BALANCE_CELL:Int ) : WS:WordStack )
                 </wordStack>
                 <pc>
                   ( PC_CELL:Int => ( PC_CELL:Int +Int 1 ) )
                 </pc>
                 <gas>
                    ( GAS_CELL:Int )
                 </gas>
                 ...
               </callState>
               <substate>
                 <accessedAccounts>
                   ( ACCESSEDACCOUNTS_CELL:Set => ACCESSEDACCOUNTS_CELL:Set |Set SetItem ( ( W0:Int modInt pow160 ) ) )
                 </accessedAccounts>
                 ...
               </substate>
               ...
             </evm>
             <network>
               <accounts>
                 <account>
                   <acctID> ACCTID_CELL_CELL </acctID>
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
       
      requires ACCTID_CELL_CELL ==Int W0:Int modInt pow160
[priority(20), label(BASIC-BLOCK-1-TO-10)]

endmodule