// HKG Token - Full Proof Claims
// =============================

// We now present reachability claims used for verification, one for each function
// in the ERC20 specification. Since the HKG token contract contains only
// sequential code (no loops), we only need one reachability claim per branch per
// function. In the following claims, any symbol starting with a `%` indicates a
// constant which has been replaced by a symbol for clarity. In particular:

// -   `%HKG_Program` is the EVM bytecode for the Hacker Gold token program;
// -   `TRANSFER` represents the symbolic amount to transfer;
// -   `B1` and `B2` are the starting balances of accounts 1 and 2, respectively;
// -   `A1` is the allowance of account 1 (strictly smaller than the balance).

// Transfer Function
// -----------------

// These parts of the state are constant throughout the proof.


module TRANSFER-SPEC
    imports ETHEREUM-SIMULATION

    rule <k> #execute => (RETURN _ _ ~> _) </k>
         <pc> 0 => _ </pc>
         <exit-code> 1 </exit-code>
         <mode>     NORMAL  </mode>
         <schedule> DEFAULT </schedule>

         <output>        .WordStack </output>
         <memoryUsed>    0 => _     </memoryUsed>
         <callDepth>     0          </callDepth>
         <callStack>     .List => _ </callStack>
         <interimStates> .List      </interimStates>
         <substateStack> .List      </substateStack>
         <callLog>       .Set       </callLog>
         <wordStack> .WordStack => _ </wordStack>

         <program>   %HKG_Program </program>
         <id>        %ACCT_ID     </id>
         <caller>    %ORIGIN_ID   </caller>
         <callData>  #abiCallData("transfer",#address(%CALLER_ID),#uint256(TRANSFER)) </callData>
         <callValue> 0            </callValue>

         <gasPrice>     _               </gasPrice>
         <origin>       %ORIGIN_ID      </origin>
         <gasLimit>     _               </gasLimit>
         <coinbase>     %COINBASE_VALUE </coinbase>
         <timestamp>    1               </timestamp>
         <number>       0               </number>
         <previousHash> 0               </previousHash>
         <difficulty>   256             </difficulty>

         <selfDestruct>   .Set                 </selfDestruct>
         <log>            .Set => _            </log>
         <activeAccounts> SetItem ( %ACCT_ID ) </activeAccounts>
         <messages>       .Bag                 </messages>


// These parts of the proof change, but we would like to avoid specifying exactly
// how (abstract over their state change).


         <localMem>    .Map => _ </localMem>
         <previousGas> _    => _ </previousGas>
         <refund>      0    => _ </refund>


// ### Then Branch

// ### Else Branch


         <gas> 100000   => _   </gas>

         <accounts>
           <account>
             <acctID>  %ACCT_ID          </acctID>
             <balance> BAL               </balance>
             <code>    %HKG_ProgramBytes </code>
             <nonce>   0                 </nonce>
             <storage> ...
                       (%ACCT_1_BALANCE |-> B1:Int)
                       (%ACCT_1_ALLOWED |-> A1:Int)
                       (%ACCT_2_BALANCE |-> B2:Int)
                       (%ACCT_2_ALLOWED |-> _)
                       ...
             </storage>
           </account>
         </accounts>

      requires TRANSFER >=Int 0 andBool TRANSFER <Int pow256
       andBool B1 >=Int 0      andBool B1 <Int pow256
       andBool B2 >=Int 0      andBool B2 <Int pow256
       andBool (B1 <Int TRANSFER orBool TRANSFER ==Int 0)
       andBool #sizeWordStack(WS) <Int 1017
endmodule

