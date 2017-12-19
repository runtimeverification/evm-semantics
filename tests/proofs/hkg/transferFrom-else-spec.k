// HKG Token - Full Proof Claims
// =============================

// We now present reachability claims used for verification, one for each function in the ERC20 specification.
// Since the HKG token contract contains only sequential code (no loops), we only need one reachability claim per branch per function.
// In the following claims, any symbol starting with a `%` indicates a constant which has been replaced by a symbol for clarity.
// In particular:

// -   `%HKG_Program` is the EVM bytecode for the Hacker Gold token program;
// -   `TRANSFER` represents the symbolic amount to transfer;
// -   `B1` and `B2` are the starting balances of accounts 1 and 2, respectively;
// -   `A1` is the allowance of account 1 (strictly smaller than the balance).

// TransferFrom Function
// ---------------------

// These parts of the state are constant throughout the proof.


module TRANSFER-FROM-SPEC
    imports ETHEREUM-SIMULATION

    rule <k> #execute ... </k>
         <exit-code> 1 </exit-code>
         <mode>     NORMAL  </mode>
         <schedule> DEFAULT </schedule>

         <output>        .WordStack </output>
         <memoryUsed>    3          </memoryUsed>
         <callDepth>     0          </callDepth>
         <callStack>     .List      </callStack>
         <interimStates> .List      </interimStates>
         <substateStack> .List      </substateStack>
         <callLog>       .Set       </callLog>

         <program>      %HKG_Program      </program>
         <programBytes> %HKG_ProgramBytes </programBytes>
         <id>           %ACCT_ID          </id>
         <caller>       %CALLER_ID        </caller>
         <callData>     .WordStack        </callData>
         <callValue>    0                 </callValue>

         <gasPrice>     _               </gasPrice>
         <origin>       %ORIGIN_ID      </origin>
         <gasLimit>     _               </gasLimit>
         <coinbase>     %COINBASE_VALUE </coinbase>
         <timestamp>    1               </timestamp>
         <number>       0               </number>
         <previousHash> 0               </previousHash>
         <difficulty>   256             </difficulty>

         <selfDestruct>   .Set               </selfDestruct>
         <log>            .List              </log>
         <activeAccounts> %ACCT_ID |-> false </activeAccounts>
         <messages>       .Bag               </messages>


// These parts of the proof change, but we would like to avoid specifying exactly how (abstract over their state change).


         <localMem>    .Map => _ </localMem>
         <previousGas> _    => _ </previousGas>
         <refund>      0    => _ </refund>


// ### Then Branch {#then-branch-1}

// ### Else Branch {#else-branch-1}


         <pc>  818 => 1451 </pc>
         <gas> G   => G1   </gas>

         <wordStack>     TRANSFER : %CALLER_ID : %ORIGIN_ID : WS
                  => 0 : TRANSFER : %CALLER_ID : %ORIGIN_ID : WS
         </wordStack>
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

      requires (TRANSFER <=Int 0 orBool B1 <Int TRANSFER orBool A1 <Int TRANSFER)
       andBool #sizeWordStack(WS) <Int 1016
       andBool G >=Int 485
       ensures G -Int G1 <=Int 485
endmodule

