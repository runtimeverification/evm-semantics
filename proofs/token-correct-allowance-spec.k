// Hacker Gold Token (HKG) Correct Program Specification
// =====================================================

// Here we provide a specification file containing a reachability rule for the
// verifying the correctness of the HKG Token's Allowance Function.


module TOKEN-SPEC
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
					<program>   %function_allowance </program>
                    <id>        %ACCT_ID                                         </id>
                    <caller>    %CALLER_ID                                       </caller>
                    <callData>  .WordStack                                       </callData>
                    <callValue> 0                                                </callValue>
                    <wordStack> _:Int : .WordStack  => ?A:WordStack              </wordStack>
                    <localMem>     .Map  => ?B:Map                               </localMem>
                    <pc>           469   => 573                                  </pc>
                    <gas>          G    => G -Int 415                            </gas>
                    <previousGas>  _     => _                                    </previousGas>
                 </txExecState>
                <substate>
                    <selfDestruct> .Set             </selfDestruct>
                    <log>          .Set             </log>
                    <refund>       0  => _          </refund>
                </substate>
                <gasPrice>     _                                                </gasPrice>
                <origin>       %ORIGIN_ID										</origin>
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
                        <code>    %function_allowance                               </code>
                        <storage>... 
									%ACCT_1_BALANCE |-> B1
									%ACCT_1_ALLOWED |-> A1
									%ACCT_2_BALANCE |-> B2
									%ACCT_2_ALLOWED |-> A2
                                      ...		                       </storage>
                        <acctMap> "nonce" |-> 0 </acctMap>
                    </account>
                </accounts>
                <messages> .Bag </messages>
            </network>
        </ethereum>
        requires B2 ==Int ?B2N 
		 andBool B1 ==Int ?B1N 
		 andBool B1 +Int B2 ==Int TOTAL 
		 andBool TOTAL ==Int ?TOTALN 
		 andBool G >=Int 415
		ensures ?B1N +Int ?B2N ==Int ?TOTALN

endmodule

