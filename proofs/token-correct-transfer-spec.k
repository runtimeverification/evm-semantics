// Hacker Gold Token (HKG) Correct Program Specification
// =====================================================

// Here we provide a specification file containing a reachability rule for the
// verifying the correctness of the HKG Token's transfer Function.


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
					<program>  %function_transfer                            </program>
                    <id>        %ACCT_ID                                         </id>
                    <caller>    %CALLER_ID                                       </caller>
                    <callData>  .WordStack                                       </callData>
                    <callValue> 0                                                </callValue>
                    <wordStack> TRANSFER:Int : ( 428365927726247537526132020791190998556166378203 : ( 443 : ( 2835717307 : .WordStack ) ) )
                                         => ?A:WordStack                         </wordStack>
                    <localMem>     .Map  => ?B:Map                               </localMem>
                    <pc>           1533  => 1772                                 </pc>
                    //<gas>          G:Int => G -Int 10544                         </gas>
					<gas>          20000 => _                         </gas>
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
                        <code>     %function_transfer              </code>
						<storage>... 
									%ACCT_1_BALANCE |-> (B1 => B1 -Int TRANSFER)
									%ACCT_1_ALLOWED |-> (A1) 
									%ACCT_2_BALANCE |-> (B2 => B2 +Int TRANSFER) 
									%ACCT_2_ALLOWED |-> (A2)
                                      ...		                       </storage>
                        <acctMap> "nonce" |-> 0                        </acctMap>
                    </account>
                </accounts>
                <messages> .Bag </messages>
            </network>
        </ethereum>	    
		requires B2 >=Int 0
		 andBool B1 >Int TRANSFER
		 andBool TRANSFER >Int 0
		 andBool B2 +Int TRANSFER <Int 2^Int 256
		 andBool B2 <Int 2^Int 256

endmodule

