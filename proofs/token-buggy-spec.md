Hacker Gold Token (HKG) Vulnerable Program Specification
========================================================

Here we provide a specification file containing a reachability rule for the
verifying the correctness of the HKG Token's transferFrom Function.

```{.k}
module TOKEN-SPEC
    imports ETHEREUM-SIMULATION

    rule
        <k> flush ~> clear ~> ( run { .JSONList } ) ~> ( success .EthereumSimulation ) </k>
        <exit-code> 1       </exit-code>
        <mode>      NORMAL  </mode>
        <schedule>  DEFAULT </schedule>
        <ethereum>
            <evm>
                <op>            #execute => ?OP:K  </op>
                <output>        .WordStack         </output>
                <memoryUsed>    3                  </memoryUsed>
                <callDepth>     0                  </callDepth>
                <callStack>     .List              </callStack>
                <interimStates> .List              </interimStates>
                <callLog>       .Set               </callLog>
                <txExecState>
                <program>   #asMapOpCodes(#dasmOpCodes(#parseByteStack("0x60606040526000357c0100000000000000000000000000000000000000000000000000000000900463ffffffff168063095ea7b31461006757806323b872dd146100be57806370a0823114610134578063a9059cbb1461017e578063dd62ed3e146101d5575bfe5b341561006f57fe5b6100a4600480803573ffffffffffffffffffffffffffffffffffffffff1690602001909190803590602001909190505061023e565b604051808215151515815260200191505060405180910390f35b34156100c657fe5b61011a600480803573ffffffffffffffffffffffffffffffffffffffff1690602001909190803573ffffffffffffffffffffffffffffffffffffffff16906020019091908035906020019091905050610331565b604051808215151515815260200191505060405180910390f35b341561013c57fe5b610168600480803573ffffffffffffffffffffffffffffffffffffffff169060200190919050506105a9565b6040518082815260200191505060405180910390f35b341561018657fe5b6101bb600480803573ffffffffffffffffffffffffffffffffffffffff169060200190919080359060200190919050506105f3565b604051808215151515815260200191505060405180910390f35b34156101dd57fe5b610228600480803573ffffffffffffffffffffffffffffffffffffffff1690602001909190803573ffffffffffffffffffffffffffffffffffffffff16906020019091905050610761565b6040518082815260200191505060405180910390f35b600081600260003373ffffffffffffffffffffffffffffffffffffffff1673ffffffffffffffffffffffffffffffffffffffff16815260200190815260200160002060008573ffffffffffffffffffffffffffffffffffffffff1673ffffffffffffffffffffffffffffffffffffffff168152602001908152602001600020819055508273ffffffffffffffffffffffffffffffffffffffff163373ffffffffffffffffffffffffffffffffffffffff167f8c5be1e5ebec7d5bd14f71427d1e84f3dd0314c0f7b2291e5b200ac8c7c3b925846040518082815260200191505060405180910390a3600190505b92915050565b600081600160008673ffffffffffffffffffffffffffffffffffffffff1673ffffffffffffffffffffffffffffffffffffffff16815260200190815260200160002054101580156103fe575081600260008673ffffffffffffffffffffffffffffffffffffffff1673ffffffffffffffffffffffffffffffffffffffff16815260200190815260200160002060003373ffffffffffffffffffffffffffffffffffffffff1673ffffffffffffffffffffffffffffffffffffffff1681526020019081526020016000205410155b801561040a5750600082115b156105985781600160008673ffffffffffffffffffffffffffffffffffffffff1673ffffffffffffffffffffffffffffffffffffffff1681526020019081526020016000206000828254039250508190555081600160008573ffffffffffffffffffffffffffffffffffffffff1673ffffffffffffffffffffffffffffffffffffffff1681526020019081526020016000208190555081600260008673ffffffffffffffffffffffffffffffffffffffff1673ffffffffffffffffffffffffffffffffffffffff16815260200190815260200160002060003373ffffffffffffffffffffffffffffffffffffffff1673ffffffffffffffffffffffffffffffffffffffff168152602001908152602001600020600082825403925050819055508273ffffffffffffffffffffffffffffffffffffffff168473ffffffffffffffffffffffffffffffffffffffff167fddf252ad1be2c89b69c2b068fc378daa952ba7f163c4a11628f55a4df523b3ef846040518082815260200191505060405180910390a3600190506105a2565b600090506105a2565b5b9392505050565b6000600160008373ffffffffffffffffffffffffffffffffffffffff1673ffffffffffffffffffffffffffffffffffffffff1681526020019081526020016000205490505b919050565b600081600160003373ffffffffffffffffffffffffffffffffffffffff1673ffffffffffffffffffffffffffffffffffffffff16815260200190815260200160002054101580156106445750600082115b156107515781600160003373ffffffffffffffffffffffffffffffffffffffff1673ffffffffffffffffffffffffffffffffffffffff1681526020019081526020016000206000828254039250508190555081600160008573ffffffffffffffffffffffffffffffffffffffff1673ffffffffffffffffffffffffffffffffffffffff168152602001908152602001600020600082825401925050819055508273ffffffffffffffffffffffffffffffffffffffff163373ffffffffffffffffffffffffffffffffffffffff167fddf252ad1be2c89b69c2b068fc378daa952ba7f163c4a11628f55a4df523b3ef846040518082815260200191505060405180910390a36001905061075b565b6000905061075b565b5b92915050565b6000600260008473ffffffffffffffffffffffffffffffffffffffff1673ffffffffffffffffffffffffffffffffffffffff16815260200190815260200160002060008373ffffffffffffffffffffffffffffffffffffffff1673ffffffffffffffffffffffffffffffffffffffff1681526020019081526020016000205490505b929150505600a165627a7a72305820a50c1490f29d0703535d1a273df0b3a1c4fd6d1b6055b5df9a4dd1e3391a6c4a0029"))) </program>
                    <id>        87579061662017136990230301793909925042452127430  </id>
                    <caller>    428365927726247537526132020791190998556166378203 </caller>
                    <callData>  .WordStack                                       </callData>
                    <callValue> 0                                                </callValue>
                    <wordStack> TRANSFER:Int : ( 428365927726247537526132020791190998556166378203 : ( 116727156174188091019688739584752390716576765452 : ( 282 : ( 599290589 : .WordStack ) ) ) ) => ?W:WordStack </wordStack>
                    <localMem>     .Map  => ?B:Map                               </localMem>
                    <pc>           818   => 1322                                 </pc>
                    <gas>          99786 => ?D:Int                               </gas>
                    <previousGas>  99787 => ?E:Int                               </previousGas>

                </txExecState>
                <substate>
                    <selfDestruct> .Set             </selfDestruct>
                    <log>          .Set             </log>
                    <refund>       0                </refund>
                </substate>
                <gasPrice>     100000000000000                                  </gasPrice>
                <origin>       116727156174188091019688739584752390716576765452 </origin>
                <gasLimit>     1000000                                          </gasLimit>
                <coinbase>     244687034288125203496486448490407391986876152250 </coinbase>
                <timestamp>    1                                                </timestamp>
                <number>       0                                                </number>
                <previousHash> 0                                                </previousHash>
                <difficulty>   256                                              </difficulty>
            </evm>
            <network>
                <activeAccounts>   SetItem ( 87579061662017136990230301793909925042452127430 )   </activeAccounts>
                <accounts>
                    <account>
                        <acctID>   87579061662017136990230301793909925042452127430  </acctID>
                        <balance>  1000000000000000000                              </balance>
                        <code>     #asMapOpCodes(#dasmOpCodes(#parseByteStack("0x60606040526000357c0100000000000000000000000000000000000000000000000000000000900463ffffffff168063095ea7b31461006757806323b872dd146100be57806370a0823114610134578063a9059cbb1461017e578063dd62ed3e146101d5575bfe5b341561006f57fe5b6100a4600480803573ffffffffffffffffffffffffffffffffffffffff1690602001909190803590602001909190505061023e565b604051808215151515815260200191505060405180910390f35b34156100c657fe5b61011a600480803573ffffffffffffffffffffffffffffffffffffffff1690602001909190803573ffffffffffffffffffffffffffffffffffffffff16906020019091908035906020019091905050610331565b604051808215151515815260200191505060405180910390f35b341561013c57fe5b610168600480803573ffffffffffffffffffffffffffffffffffffffff169060200190919050506105a9565b6040518082815260200191505060405180910390f35b341561018657fe5b6101bb600480803573ffffffffffffffffffffffffffffffffffffffff169060200190919080359060200190919050506105f3565b604051808215151515815260200191505060405180910390f35b34156101dd57fe5b610228600480803573ffffffffffffffffffffffffffffffffffffffff1690602001909190803573ffffffffffffffffffffffffffffffffffffffff16906020019091905050610761565b6040518082815260200191505060405180910390f35b600081600260003373ffffffffffffffffffffffffffffffffffffffff1673ffffffffffffffffffffffffffffffffffffffff16815260200190815260200160002060008573ffffffffffffffffffffffffffffffffffffffff1673ffffffffffffffffffffffffffffffffffffffff168152602001908152602001600020819055508273ffffffffffffffffffffffffffffffffffffffff163373ffffffffffffffffffffffffffffffffffffffff167f8c5be1e5ebec7d5bd14f71427d1e84f3dd0314c0f7b2291e5b200ac8c7c3b925846040518082815260200191505060405180910390a3600190505b92915050565b600081600160008673ffffffffffffffffffffffffffffffffffffffff1673ffffffffffffffffffffffffffffffffffffffff16815260200190815260200160002054101580156103fe575081600260008673ffffffffffffffffffffffffffffffffffffffff1673ffffffffffffffffffffffffffffffffffffffff16815260200190815260200160002060003373ffffffffffffffffffffffffffffffffffffffff1673ffffffffffffffffffffffffffffffffffffffff1681526020019081526020016000205410155b801561040a5750600082115b156105985781600160008673ffffffffffffffffffffffffffffffffffffffff1673ffffffffffffffffffffffffffffffffffffffff1681526020019081526020016000206000828254039250508190555081600160008573ffffffffffffffffffffffffffffffffffffffff1673ffffffffffffffffffffffffffffffffffffffff1681526020019081526020016000208190555081600260008673ffffffffffffffffffffffffffffffffffffffff1673ffffffffffffffffffffffffffffffffffffffff16815260200190815260200160002060003373ffffffffffffffffffffffffffffffffffffffff1673ffffffffffffffffffffffffffffffffffffffff168152602001908152602001600020600082825403925050819055508273ffffffffffffffffffffffffffffffffffffffff168473ffffffffffffffffffffffffffffffffffffffff167fddf252ad1be2c89b69c2b068fc378daa952ba7f163c4a11628f55a4df523b3ef846040518082815260200191505060405180910390a3600190506105a2565b600090506105a2565b5b9392505050565b6000600160008373ffffffffffffffffffffffffffffffffffffffff1673ffffffffffffffffffffffffffffffffffffffff1681526020019081526020016000205490505b919050565b600081600160003373ffffffffffffffffffffffffffffffffffffffff1673ffffffffffffffffffffffffffffffffffffffff16815260200190815260200160002054101580156106445750600082115b156107515781600160003373ffffffffffffffffffffffffffffffffffffffff1673ffffffffffffffffffffffffffffffffffffffff1681526020019081526020016000206000828254039250508190555081600160008573ffffffffffffffffffffffffffffffffffffffff1673ffffffffffffffffffffffffffffffffffffffff168152602001908152602001600020600082825401925050819055508273ffffffffffffffffffffffffffffffffffffffff163373ffffffffffffffffffffffffffffffffffffffff167fddf252ad1be2c89b69c2b068fc378daa952ba7f163c4a11628f55a4df523b3ef846040518082815260200191505060405180910390a36001905061075b565b6000905061075b565b5b92915050565b6000600260008473ffffffffffffffffffffffffffffffffffffffff1673ffffffffffffffffffffffffffffffffffffffff16815260200190815260200160002060008373ffffffffffffffffffffffffffffffffffffffff1673ffffffffffffffffffffffffffffffffffffffff1681526020019081526020016000205490505b929150505600a165627a7a72305820a50c1490f29d0703535d1a273df0b3a1c4fd6d1b6055b5df9a4dd1e3391a6c4a0029")))                                                </code>
                        <storage>(89883370637028415006891042932604780869171597379948077832163656920795299088269 |-> 3000) (0 |-> 5000) (73276140668783822097736045772311176946506324369098798920944620499663575949472 |-> (2000=> 2000 -Int TRANSFER)) (3 |-> 116727156174188091019688739584752390716576765452) (4 |-> 428365927726247537526132020791190998556166378203) (90140393717854041204577419487481777019768054268415728047989462811209962694062 |-> 2000) (7523342389551220067180060596052511116626922476768911452708464109912271601147 |-> (3000 => 3000 +Int TRANSFER)) </storage>
                        <acctMap> "nonce" |-> 0 </acctMap>
                    </account>
                </accounts>
                <messages> .Bag </messages>
            </network>
        </ethereum>
         requires TRANSFER >Int 0 andBool TRANSFER<Int 2000

endmodule
```
