Hacker Gold Token (HKG) Vulnerable Program Specification
========================================================

Here we provide a specification file containing a reachability rule for the verifying the correctness of the buggy HKG Token's transferFrom Function.

```{.k}
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
         <substateStack> .List      </substateStack>
         <callLog>       .Set       </callLog>

         <program>      %HKG_Program_buggy      </program>
         <programBytes> %HKG_ProgramBytes_buggy </programBytes>
         <id>           %ACCT_ID                </id>
         <caller>       %CALLER_ID              </caller>
         <callData>     .WordStack              </callData>
         <callValue>    0                       </callValue>
         <static>       false                   </static>

         <wordStack>                        TRANSFER : %CALLER_ID : %ORIGIN_ID : WS
                  => A1 -Int TRANSFER : 0 : TRANSFER : %CALLER_ID : %ORIGIN_ID : WS
         </wordStack>
         <localMem>     .Map   => _    </localMem>
         <pc>           836    => 1460 </pc>
         <gas>          100000 => _    </gas>
         <previousGas>  _      => _    </previousGas>

         <selfDestruct> .Set    </selfDestruct>
         <log>          .List   </log>
         <refund>       0  => _ </refund>

         <gasPrice>     _               </gasPrice>
         <origin>       %ORIGIN_ID      </origin>
         <gasLimit>     _               </gasLimit>
         <coinbase>     %COINBASE_VALUE </coinbase>
         <timestamp>    1               </timestamp>
         <number>       0               </number>
         <previousHash> 0               </previousHash>
         <difficulty>   256             </difficulty>

         <activeAccounts> SetItem(%ACCT_ID) </activeAccounts>
         <accounts>
           <account>
             <acctID>  %ACCT_ID                </acctID>
             <balance> BAL                     </balance>
             <code>    %HKG_ProgramBytes_buggy </code>
             <nonce>   0                       </nonce>
             <storage> ...
                       %ACCT_1_BALANCE |-> (B1 => B1 -Int TRANSFER)
                       %ACCT_1_ALLOWED |-> (A1 => A1 -Int TRANSFER)
                       %ACCT_2_BALANCE |-> (B2 => B2 +Int TRANSFER)
                       %ACCT_2_ALLOWED |-> _
                       ...
             </storage>
           </account>
         </accounts>

      requires B2 >=Int 0
       andBool TRANSFER >Int 0
       andBool B1 >=Int TRANSFER
       andBool A1 >=Int TRANSFER
       andBool B2 +Int TRANSFER <Int 2^Int 256
       andBool A1 <Int 2^Int 256
       andBool B1 <Int 2^Int 256
       andBool #sizeWordStack(WS) <Int 1016
endmodule
```
