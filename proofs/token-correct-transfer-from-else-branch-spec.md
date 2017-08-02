Hacker Gold Token (HKG) Correct Program Specification
=====================================================

Here we provide a specification file containing a reachability rule for verifying the correctness of the else branch in HKG Token's transferFrom Function

```{.k}
module TRANSFER-FROM-SPEC
imports ETHEREUM-SIMULATION

    rule
        <k> #execute ... </k>
        <exit-code> 1       </exit-code>
        <mode>      NORMAL  </mode>
        <schedule>  DEFAULT </schedule>
        <ethereum>
            <evm>
                <output>        .WordStack         </output>
                <memoryUsed>    3                  </memoryUsed>
                <callDepth>     0                  </callDepth>
                <callStack>     .List              </callStack>
                <interimStates> .List              </interimStates>
                <callLog>       .Set               </callLog>
                <txExecState>
					<program>  %HKG_Program                              </program>
                    <id>        %ACCT_ID                                         </id>
                    <caller>    %CALLER_ID                                       </caller>
                    <callData>  .WordStack                                       </callData>
                    <callValue> 0                                                </callValue>
                    <wordStack> 
				TRANSFER     :  %CALLER_ID   : %ORIGIN_ID :  WS
			     => 0 : TRANSFER :  %CALLER_ID   : %ORIGIN_ID :  WS
                                                     				 </wordStack>                                                   
                    <localMem>     .Map  => _                                    </localMem>
                    <pc>           818   => 1451                                 </pc>
		    <gas>          500 => _                                     </gas>
                    <previousGas>  _     => _                                    </previousGas>
                </txExecState>
                <substate>
                    <selfDestruct> .Set             </selfDestruct>
                    <log>          .Set             </log>
                    <refund>       0  => _          </refund>
                </substate>
                <gasPrice>     _                                                </gasPrice>
                <origin>       %ORIGIN_ID					</origin>
                <gasLimit>     _                                                </gasLimit>
                <coinbase>     %COINBASE_VALUE                                   </coinbase>
                <timestamp>    1                                                </timestamp>
                <number>       0                                                </number>
                <previousHash> 0                                                </previousHash>
                <difficulty>   256                                              </difficulty>
            </evm>
            <network>
                <activeAccounts>   SetItem ( %ACCT_ID )   </activeAccounts>
                <accounts>
                    <account>
                        <acctID>   %ACCT_ID  </acctID>
                        <balance>  BAL                                  </balance>
                        <code>     %HKG_Program                         </code>
                        <storage>... 
				  (%ACCT_1_BALANCE |-> B1)
				  (%ACCT_1_ALLOWED |-> A1) 
				  (%ACCT_2_BALANCE |-> B2) 
				  (%ACCT_2_ALLOWED |-> _)
                                      ...		               </storage>
                        <acctMap> "nonce" |-> 0                        </acctMap>
                    </account>
                </accounts>
                <messages> .Bag </messages>
            </network>
        </ethereum>	

	requires ((TRANSFER >Int 0 andBool B1 <Int TRANSFER andBool A1 >=Int TRANSFER)
	  orBool (TRANSFER ==Int 0 andBool B1 >=Int TRANSFER andBool A1 >=Int TRANSFER)
          orBool (TRANSFER >Int  0 andBool B1 >=Int TRANSFER andBool A1 <Int TRANSFER))	 
	 andBool #sizeWordStack(WS) <Int 1016

endmodule
```
