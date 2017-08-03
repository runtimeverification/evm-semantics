Hacker Gold Token (HKG) Transfer-From Correct Program Specification
===================================================================

These parts of the state are constant throughout the proof.

```{.k}
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
         <callLog>       .Set       </callLog>

         <program>   %HKG_Program </program>
         <id>        %ACCT_ID     </id>
         <caller>    %CALLER_ID   </caller>
         <callData>  .WordStack   </callData>
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
         <log>            .Set                 </log>
         <activeAccounts> SetItem ( %ACCT_ID ) </activeAccounts>
         <messages>       .Bag                 </messages>
```

These parts of the proof change, but we would like to avoid specifying exactly how (abstract over their state change).

```{.k}
         <localMem>    .Map => _ </localMem>
         <previousGas> _    => _ </previousGas>
         <refund>      0    => _ </refund>
```

### Then Branch

```{.k}
        <pc>  818 => 1331         </pc>
        <gas> G   => G -Int 16071 </gas>

        <wordStack>                        TRANSFER : %CALLER_ID : %ORIGIN_ID : WS
                 => A1 -Int TRANSFER : 0 : TRANSFER : %CALLER_ID : %ORIGIN_ID : WS
        </wordStack>
	<accounts>
        <account>
          <acctID>   %ACCT_ID     </acctID>
          <balance>  BAL          </balance>
          <code>     %HKG_Program </code>
          <acctMap> "nonce" |-> 0 </acctMap>
          <storage> ...
                    %ACCT_1_BALANCE |-> (B1 => B1 -Int TRANSFER)
                    %ACCT_1_ALLOWED |-> (A1 => A1 -Int TRANSFER)
                    %ACCT_2_BALANCE |-> (B2 => B2 +Int TRANSFER)
                    %ACCT_2_ALLOWED |-> _
                    ...
          </storage>
        </account>
        </accounts>

      requires TRANSFER >Int 0
       andBool B1 >=Int TRANSFER andBool B1 <Int pow256
       andBool A1 >=Int TRANSFER andBool A1 <Int pow256
       andBool B2 >=Int 0        andBool B2 +Int TRANSFER <Int pow256
       andBool #sizeWordStack(WS) <Int 1016
       andBool G >=Int 16071
endmodule
```

### Else Branch

```{.k}
        <pc>  818 => 1451 </pc>
        <gas> G   => G1   </gas>

        <wordStack>     TRANSFER : %CALLER_ID : %ORIGIN_ID : WS
                 => 0 : TRANSFER : %CALLER_ID : %ORIGIN_ID : WS
        </wordStack>
        <accounts>
          <account>
          <acctID>   %ACCT_ID     </acctID>
          <balance>  BAL          </balance>
          <code>     %HKG_Program </code>
          <acctMap> "nonce" |-> 0 </acctMap>
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
```
