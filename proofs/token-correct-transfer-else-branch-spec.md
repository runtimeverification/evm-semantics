Hacker Gold Token (HKG) Correct Program Specification
=====================================================

Here we provide a specification file containing a reachability rule for verifying the correctness of the else branch in HKG Token's transfer Function

```{.k}
module TRANSFER-SPEC
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
		    <program>      %HKG_Program                                  </program>
                    <id>           %ACCT_ID                                      </id>
                    <caller>       %ORIGIN_ID                                    </caller>
                    <callData>     .WordStack                                    </callData>
                    <callValue>    0                                             </callValue>
                    <wordStack>    TRANSFER : %CALLER_ID : WS
				=> 0 :TRANSFER : %CALLER_ID : WS                 </wordStack>
                    <localMem>     .Map  => ?B:Map                               </localMem>
                    <pc>           1533  => 1892                                 </pc>
                    <gas>          300     => _                         </gas>
                    <previousGas>  _     => _                                    </previousGas>
                </txExecState>
                <substate>
                    <selfDestruct> .Set             </selfDestruct>
                    <log>          .Set             </log>
                     <refund>       0            </refund>
                </substate>
                <gasPrice>     _                                                </gasPrice>
                <origin>       %ORIGIN_ID					</origin>
                <gasLimit>     _                                                </gasLimit>
                <coinbase>     %COINBASE_VALUE                                  </coinbase>
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
                        <storage>
			            ...
				  (%ACCT_2_ALLOWED |-> A2)
			          (%ACCT_1_BALANCE |-> B1) 
				  (%ACCT_1_ALLOWED |-> A1) 
				  (%ACCT_2_BALANCE |-> B2) 
				   ...                                    </storage>
                        <acctMap> "nonce" |-> 0                           </acctMap>
                    </account>
                </accounts>
                <messages> .Bag </messages>
            </network>
        </ethereum>
		requires (TRANSFER <=Int 0 orBool B1 <Int TRANSFER)
		 andBool #sizeWordStack(WS) <Int 1015

endmodule
```
