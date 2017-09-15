The Hacker Gold (HKG) Token Smart Contract
==========================================

[The ERC20 Token Standard](https://github.com/ethereum/EIPs/issues/20)
----------------------------------------------------------------------

The ERC20 standard is a specification that describes several simple methods that a smart contract must implement in order to be treated as a token by a variety of higher level applications (including wallets, exchanges, and other contracts expecting to interact with tokens).
The implementation details of these methods are left to the user, with minimal semantic behavior provided in the specification, leaving room for a wide range of complex tokens (and the associated security vulnerabilities).
The ERC20 standard requires the following Solidity methods and events (and log items) to be implemented:

```js
// Get the total token supply
    function totalSupply() constant returns (uint256 totalSupply)

// Get the account balance of another account with address _owner
    function balanceOf(address _owner) constant returns (uint256 balance)

// Send _value amount of tokens to address _to
    function transfer(address _to, uint256 _value) returns (bool success)

// Send _value amount of tokens from address _from to address _to
    function transferFrom(address _from, address _to, uint256 _value) returns (bool success)

// Allow _spender to withdraw from your account, multiple times, up to the _value amount.
// If this function is called again it overwrites the current allowance with _value.
    function approve(address _spender, uint256 _value) returns (bool success)

// Returns the amount which _spender is still allowed to withdraw from _owner
    function allowance(address _owner, address _spender) constant returns (uint256 remaining)

// Triggered when tokens are transferred.
    event Transfer(address indexed _from, address indexed _to, uint256 _value)

// Triggered whenever approve(address _spender, uint256 _value) is called.
    event Approval(address indexed _owner, address indexed _spender, uint256 _value)
```

The HKG Token is an implementation of the ERC20 specification and was a topic of discussion when a vulnerability based in a typographical error lead to a [reissuance of the entire token](https://www.ethnews.com/ethercamps-hkg-token-has-a-bug-and-needs-to-be-reissued), disrupting a nontrivial economy based on it.
Previously, the token was [manually audited by Zeppelin](https://zeppelin.solutions/security-audits) and deemed secure, further reinforcing the error-prone nature of the human review process and the need for tools that go beyond what is possible with manual review.
Specifically, the typographical error in the [HKG Token Solidity source](https://github.com/ether-camp/virtual-accelerator/issues/8) code came in the form of an `=+` statement being used in place of the desired `+=` when updating a receiver's balance during a transfer.
While typographically similar, these statements are semantically very different, with the former being equivalent to a simple `=` (the second plus saying that the expression following should be treated as positive) and the latter desugaring to add the right hand quantity to the existing value in the variable on the left hand side of the expression.
In testing, this error was missed, as the first balance updated would always work (with balance `=+` value being semantically equivalent to balance `+=` value when balance is 0, in both cases assigning value to balance).
Even with full decision or branch coverage in testing, multiple transfers on the same account can be entirely omitted in a way that is difficult to notice through human review.

In order to thoroughly analyze the HKG contract, we first had to compile the solidity source of the contract to EVM.
A more detailed description of the process, with snippets of solidity code can be found in Sec 6.1.1 of our [technical report](https://www.ideals.illinois.edu/handle/2142/97207).

We now present reachability claims used for verification, one for each function in the ERC20 specification.
Since the HKG token contract contains only sequential code (no loops), we only need one reachability claim per function.
In the following claims, any symbol starting with a `%` indicates a constant which has been replaced by a symbol for clarity.
In particular:

-   `%HKG_Program` is the EVM bytecode for the Hacker Gold token program;
-   `TRANSFER` represents the symbolic amount to transfer;
-   `B1` and `B2` are the starting balances of accounts 1 and 2, respectively;
-   `A1` is the allowance of account 1 (strictly smaller than the balance).

Transfer Function
-----------------

These parts of the state are constant throughout the proof.

```{.k .transfer-then .transfer-else}
module TRANSFER-SPEC
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
         <caller>    %ORIGIN_ID   </caller>
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

```{.k .transfer-then .transfer-else}
         <localMem>    .Map => _ </localMem>
         <previousGas> _    => _ </previousGas>
         <refund>      0    => _ </refund>
```

### Then Branch

```{.k .transfer-then}
         <pc>  1533 => 1772         </pc>
         <gas>  G   => G -Int 10544 </gas>

         <wordStack>                        TRANSFER : %CALLER_ID : WS
                  => B2 +Int TRANSFER : 0 : TRANSFER : %CALLER_ID : WS
         </wordStack>
         <accounts>
           <account>
             <acctID>   %ACCT_ID     </acctID>
             <balance>  BAL          </balance>
             <code>     %HKG_Program </code>
             <acctMap> "nonce" |-> 0 </acctMap>
             <storage> ...
                       (%ACCT_1_BALANCE |-> (B1 => B1 -Int TRANSFER))
                       (%ACCT_1_ALLOWED |-> A1)
                       (%ACCT_2_BALANCE |-> (B2 => B2 +Int TRANSFER))
                       (%ACCT_2_ALLOWED |-> _)
                       ...
             </storage>
           </account>
         </accounts>

      requires TRANSFER >Int 0
       andBool B1 >=Int TRANSFER andBool B1 <Int pow256
       andBool B2 >=Int 0        andBool B2 +Int TRANSFER <Int pow256
       andBool #sizeWordStack(WS) <Int 1017
       andBool G >=Int 10544
endmodule
```

### Else Branch

```{.k .transfer-else}
         <pc>  1533 => 1892 </pc>
         <gas> G   => G1   </gas>

         <wordStack>     TRANSFER : %CALLER_ID : WS
                  => 0 : TRANSFER : %CALLER_ID : WS
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

      requires (TRANSFER <=Int 0 orBool B1 <Int TRANSFER)
       andBool #sizeWordStack(WS) <Int 1015
       andBool G >=Int 221
       ensures G -Int G1 <=Int 221
endmodule
```

TransferFrom Function
---------------------

These parts of the state are constant throughout the proof.

```{.k .transferFrom-then .transferFrom-else}
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

```{.k .transferFrom-then .transferFrom-else}
         <localMem>    .Map => _ </localMem>
         <previousGas> _    => _ </previousGas>
         <refund>      0    => _ </refund>
```

### Then Branch

```{.k .transferFrom-then}
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

```{.k .transferFrom-else}
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

Allowance Function
------------------

Here we provide a specification file containing a reachability rule for the verifying the correctness of the HKG Token's Allowance Function.

```{.k .allowance}
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
```

Approve Function
----------------

Here we provide a specification file containing a reachability rule for the verifying the correctness of the HKG Token's APPROVE Function.

```{.k .approve}
module APPROVE-SPEC
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

         <program>   %HKG_Program </program>
         <id>        %ACCT_ID     </id>
         <caller>    %CALLER_ID   </caller>
         <callData>  .WordStack   </callData>
         <callValue> 0            </callValue>

         <wordStack>   A2 : %ORIGIN_ID : WS => ?A:WordStack </wordStack>
         <localMem>    .Map                 => ?B:Map       </localMem>
         <pc>          574                  => 806          </pc>
         <gas>         G                    => G -Int 5269  </gas>
         <previousGas> _                    => _            </previousGas>

         <selfDestruct> .Set      </selfDestruct>
         <log>          .Set => _ </log>
         <refund>       0    => _ </refund>

         <gasPrice>     _               </gasPrice>
         <origin>       %ORIGIN_ID      </origin>
         <gasLimit>     _               </gasLimit>
         <coinbase>     %COINBASE_VALUE </coinbase>
         <timestamp>    1               </timestamp>
         <number>       0               </number>
         <previousHash> 0               </previousHash>
         <difficulty>   256             </difficulty>

         <activeAccounts>   SetItem ( %ACCT_ID )   </activeAccounts>
         <accounts>
           <account>
           <acctID>   %ACCT_ID     </acctID>
           <balance>  BAL          </balance>
           <code>     %HKG_Program </code>
           <acctMap> "nonce" |-> 0 </acctMap>
           <storage> ...
                     3 |-> %ORIGIN_ID
                     4 |-> %CALLER_ID
                     %ACCT_1_BALANCE |-> B1:Int
                     %ACCT_1_ALLOWED |-> A1:Int
                     %ACCT_2_BALANCE |-> B2:Int
                     %ACCT_2_ALLOWED |-> A2:Int
                     ...
           </storage>
           </account>
         </accounts>

      requires #sizeWordStack(WS) <Int 1014  andBool G >=Int 5269
endmodule
```

BalanceOf Function
------------------

Here we provide a specification file containing a reachability rule for the verifying the correctness of the HKG Token's BalanceOf Function.

```{.k .balanceOf}
module BALANCE-OF-SPEC
    imports ETHEREUM-SIMULATION

    rule <k> #execute ... </k>
         <exit-code> 1       </exit-code>
         <mode>      NORMAL  </mode>
         <schedule>  DEFAULT </schedule>

         <output>        .WordStack </output>
         <memoryUsed>    4          </memoryUsed>
         <callDepth>     0          </callDepth>
         <callStack>     .List      </callStack>
         <interimStates> .List      </interimStates>
         <callLog>       .Set       </callLog>

         <program>      %HKG_Program </program>
         <id>           %ACCT_ID     </id>
         <caller>       %CALLER_ID   </caller>
         <callData>     .WordStack   </callData>
         <callValue>    0            </callValue>

         <wordStack>    WS    => ?A:WordStack </wordStack>
         <localMem>     .Map  => ?B:Map       </localMem>
         <pc>           316   => 381          </pc>
         <gas>          G     => G -Int 274   </gas>
         <previousGas>  _     => _            </previousGas>

         <selfDestruct> .Set    </selfDestruct>
         <log>          .Set    </log>
         <refund>       0  => _ </refund>

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

      requires #sizeWordStack(WS) <Int 1018 andBool G >=Int 274
endmodule
```
