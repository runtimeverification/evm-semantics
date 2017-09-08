// The Hacker Gold (HKG) Token Smart Contract
// ==========================================

// Allowance Function
// ------------------

// Here we provide a specification file containing a reachability rule for the
// verifying the correctness of the HKG Token's Allowance Function.


module TOKEN-SPEC
imports ETHEREUM-SIMULATION

    rule <k> #execute ... </k>
         <exit-code> 1       </exit-code>
         <mode>      NORMAL  </mode>
         <schedule>  DEFAULT </schedule>

         <output>        .WordStack </output>
         <memoryUsed>    3          </memoryUsed>
         <callDepth>     0          </callDepth>
         <callStack>     .List      </callStack>
         <interimStates> .List      </interimStates>
         <callLog>       .Set       </callLog>

         <program>     %HKG_Program          </program>
         <id>          %ACCT_ID              </id>
         <caller>      %CALLER_ID            </caller>
         <callData>    .WordStack            </callData>
         <callValue>   0                     </callValue>
         <wordStack>   WS   => WS1:WordStack </wordStack>
         <localMem>    .Map => ?B:Map        </localMem>
         <pc>          469  => 573           </pc>
         <gas>         G    => G -Int 415    </gas>
         <previousGas> _    => _             </previousGas>

         <selfDestruct> .Set   </selfDestruct>
         <log>          .Set   </log>
         <refund>       0 => _ </refund>

         <gasPrice>     _               </gasPrice>
         <origin>       %ORIGIN_ID      </origin>
         <gasLimit>     _               </gasLimit>
         <coinbase>     %COINBASE_VALUE </coinbase>
         <timestamp>    1               </timestamp>
         <number>       0               </number>
         <previousHash> 0               </previousHash>
         <difficulty>   256             </difficulty>

         <activeAccounts> SetItem ( %ACCT_ID ) </activeAccounts>
         <accounts>
           <account>
             <acctID>  %ACCT_ID      </acctID>
             <balance> BAL           </balance>
             <code>    %HKG_Program  </code>
             <acctMap> "nonce" |-> 0 </acctMap>
             <storage> %ACCT_1_BALANCE |-> B1:Int
                       %ACCT_1_ALLOWED |-> A1:Int
                       %ACCT_2_BALANCE |-> B2:Int
                       %ACCT_2_ALLOWED |-> A2:Int
                       3 |-> %ORIGIN_ID
                       4 |-> %CALLER_ID
             </storage>
           </account>
         </accounts>

      requires G >=Int 415  andBool #sizeWordStack(WS) <Int 1017
endmodule

