requires "../evm.md"

module BALANCE-OWISE-SUMMARY
    imports public EVM
    
    rule [BALANCE-OWISE-SUMMARY-NOGAS-BERLIN]: <kevm>
           <k>
             ( #next [ BALANCE ] ~> .K => .K )
             ~> _K_CELL:K
           </k>
           <useGas>
             ( USEGAS_CELL:Bool => false )
           </useGas>
           <ethereum>
             <evm>
               <callState>
                 <wordStack>
                   ( ( W0:Int => BALANCE_CELL:Int ) : _WS:WordStack )
                 </wordStack>
                 <pc>
                   ( PC_CELL:Int => ( PC_CELL:Int +Int 1 ) )
                 </pc>
                 <gas>
                   _GAS_CELL:Int
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
                   <acctID>
                     ACCTID:Int
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
       andBool ( ( W0:Int modInt pow160 ) ==Int ACCTID:Int
               ))
      [priority(20), label(BALANCE-OWISE-SUMMARY-NOGAS-BERLIN)]
    
    rule [BALANCE-OWISE-SUMMARY-USEGAS-BERLIN]: <kevm>
           <k>
             ( #next [ BALANCE ] ~> .K => .K )
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
               <callState>
                 <wordStack>
                   ( ( W0:Int => BALANCE_CELL:Int ) : _WS:WordStack )
                 </wordStack>
                 <pc>
                   ( PC_CELL:Int => ( PC_CELL:Int +Int 1 ) )
                 </pc>
                 <gas>
                   ( GAS_CELL:Int => ( GAS_CELL:Int -Int #if ( W0:Int modInt pow160 ) in ACCESSEDACCOUNTS_CELL:Set #then Gwarmstorageread < SCHEDULE_CELL:Schedule > #else Gcoldaccountaccess < SCHEDULE_CELL:Schedule > #fi ) )
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
                   <acctID>
                     ACCTID:Int
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
       andBool ( Ghasaccesslist << SCHEDULE_CELL:Schedule >>
       andBool ( #if ( W0:Int modInt pow160 ) in ACCESSEDACCOUNTS_CELL:Set #then Gwarmstorageread < SCHEDULE_CELL:Schedule > #else Gcoldaccountaccess < SCHEDULE_CELL:Schedule > #fi <=Int GAS_CELL:Int
       andBool ( 0 <=Int GAS_CELL:Int
       andBool ( ( W0:Int modInt pow160 ) ==Int ACCTID:Int
               )))))
      [priority(20), label(BALANCE-OWISE-SUMMARY-USEGAS-BERLIN)]
    
    rule [BALANCE-OWISE-SUMMARY-USEGAS]: <kevm>
           <k>
             ( #next [ BALANCE ] ~> .K => .K )
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
               <callState>
                 <wordStack>
                   ( ( W0:Int => BALANCE_CELL:Int ) : _WS:WordStack )
                 </wordStack>
                 <pc>
                   ( PC_CELL:Int => ( PC_CELL:Int +Int 1 ) )
                 </pc>
                 <gas>
                   ( GAS_CELL:Int => ( GAS_CELL:Int -Int Gbalance < SCHEDULE_CELL:Schedule > ) )
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
                   <acctID>
                     ACCTID:Int
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
       andBool ( ( notBool Ghasaccesslist << SCHEDULE_CELL:Schedule >> )
       andBool ( Gbalance < SCHEDULE_CELL:Schedule > <=Int GAS_CELL:Int
       andBool ( ( W0:Int modInt pow160 ) ==Int ACCTID:Int
               ))))
      [priority(20), label(BALANCE-OWISE-SUMMARY-USEGAS)]

endmodule