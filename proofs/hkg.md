The Hacker Gold (HKG) Token Smart Contract - Overview
=====================================================

The HKG token is an implementation of the ERC20 specification written in Solidity.
The token became a [topic of discussion](https://www.ethnews.com/ethercamps-hkg-token-has-a-bug-and-needs-to-be-reissued) when a subtle vulnerability lead to a reissue.
The token had been originally audited by [Zeppelin](https://zeppelin.solutions/security-audits), and was deemed secure.

Specifically, the typographical error in the [HKG Token Solidity source](https://github.com/ether-camp/virtual-accelerator/issues/8) code came in the form of an `=+` statement being used in place of the desired `+=` when updating a receiver's balance during a transfer.
While typographically similar, these statements are semantically very different, with the former being equivalent to a simple `=` (the second plus saying that the expression following should be treated as positive) and the latter desugaring to add the right hand quantity to the existing value in the variable on the left hand side of the expression.
In testing, this error was missed, as the first balance updated would always work (with balance `=+` value being semantically equivalent to balance `+=` value when balance is 0, in both cases assigning `value` to `balance`).
Even with full decision or branch coverage in testing, multiple transfers on the same account can be entirely omitted in a way that is difficult to notice through human review.

In order to thoroughly analyze the HKG contract, we first had to compile the Solidity source of the contract to EVM.
A more detailed description of the process, with snippets of Solidity code, can be found in Sec 6.1.1 of our [technical report](https://www.ideals.illinois.edu/handle/2142/97207).

Compiling Solidity Source To EVM
--------------------------------

Since we are performing our verification at the EVM level, the first step in the verification process is to compile the [HKG Token's Source](https://github.com/ether-camp/virtual-accelerator/blob/master/contracts/StandardToken.sol) to EVM.
To simplify the verification process, we fixed the total supply, and added two dummy accounts before compiling the code to EVM.

```solidity
contract StandardToken is TokenInterface {
//...
function StandardToken() {
    totalSupply = 5000;

    balances[dummy1] = 2000;
    balances[dummy2] = 3000;

    allowed[dummy1][dummy2] = balances[dummy1];
    allowed[dummy2][dummy1] = balances[dummy2];
}
```

Here's what the `transferFrom` function looks like, pasted verbatim from HKG Token's source file.

```solidity
  /*
   * transferFrom() - used to move allowed funds from other owner account
   *                  account
   *
   *  @param from  - move funds from account
   *  @param to    - move funds to account
   *  @param value - move the value
   *
   *  @return - return true on success false otherwise
   */
    function transferFrom(address from, address to, uint256 value)
     returns (bool success) {

        if ( balances[from] >= value &&
             allowed[from][msg.sender] >= value &&
             value > 0) {

            // do the transfer
            balances[from] -= value;
            balances[to]   += value;

            // addjust senders allowed spending
            allowed[from][msg.sender] -= value;

            // raise a Transfer
            Transfer(from, to, value);

            // success!
            return true;

        } else {
            return false;
        }
    }
}
```

This function is specified in the ERC20 standard described previously as "Send `_value` amount of tokens from address `_from` to address `_to`", and requires the `_from` address to approve the transfer of at least the amount being sent using ERC20's approve functionality.

Our Proof Claims
----------------

The K prover takes as input *Reachability claims*.
The claims are written in the same format as rules from a language definition.
Since our HKG token contract contains only sequential code (without loops), each specification in our [specification file](hkg.md) contains a single claim for each branch.
The claims have to be supplied to K via a specification file (ends in `-spec.k`).

The following claim captures the behavior of the `transferFrom` function.

```k
    rule <k>       #execute ... </k>
         <id>      %ACCT_ID     </id>
         <program> %HKG_Program </program>

         <pc>  818 => 1331         </pc>
         <gas> G   => G -Int 16071 </gas>

         <wordStack>                        TRANSFER : %CALLER_ID : %ORIGIN_ID : WS
                  => A1 -Int TRANSFER : 0 : TRANSFER : %CALLER_ID : %ORIGIN_ID : WS
         </wordStack>

         <account>
           <acctID>  %ACCT_ID               </acctID>
           <code>    %function_transferFrom </code>
           <storage> %ACCT_1_BALANCE |-> (B1 => B1 -Int TRANSFER)
                     %ACCT_1_ALLOWED |-> (A1 => A1 -Int TRANSFER)
                     %ACCT_2_BALANCE |-> (B2 => B2 +Int TRANSFER)
                     %ACCT_2_ALLOWED |-> _
                     ...
           </storage>
           ...
         </account>
         ...
      requires TRANSFER >Int 0
       andBool B1 >=Int TRANSFER andBool B1               <Int pow256
       andBool B2 >=Int 0        andBool B2 +Int TRANSFER <Int pow256
       andBool A1 >=Int TRANSFER andBool A1               <Int pow256
       andBool #sizeWordStack(WS) <Int 1016
       andBool G >=Int 16071
```

The rule above specifies that in all valid executions starting in the left-hand-side of the rule, either execution will never terminate or it will reach an instance of the right-hand-side.

-   Any symbol starting with a `%` indicates a constant which has been replaced by a symbol for clarity.
    In particular, `%HKG_Program` is the EVM bytecode for the `Hacker Gold` token program.
-   The program counter starts at 818 and ends at 1331, which are the start and end of the `transferFrom` function in the compiled EVM.
-   `TRANSFER` represents the symbolic amonut to transfer, `B1` and `B2` are the starting balances of accounts 1 and 2, repsectively, and `A1` is the allowance of account 1.
-   The terms in the `<storage>` cell capture the behavior of `transferFrom` function, which means that any transfer of amount `TRANSFER` from account 1 to account 2 (with `TRANSFER` sufficiently low and various overflow conditions met) will happen as intended in the execution of the `transferFrom` code provided.
-   The program counter starts at 818 and ends at 1331, which are the start and end of the `transferFrom` function in the compiled EVM.
-   The require clause states the following preconditions:

    a.  the condition that the `then` branch of the function meets;
    b.  the balance of each account should be low enough to avoid overflow during the transaction;
    c.  bounds the size of `WS` to ensure there is no stack overflow in runtime; and
    d.  there is enough gas for the execution of this fuction.

Results
-------

Initially, we took the vulnerability containing code, compiled it to EVM, and plugged in into our [reachability claim](token-buggy-spec.md), which wasn't able to be verified as expected.
Surprisingly, after fixing the bug which caused the reissuance, verifying against the ERC20 specification was still not possible due to the presence of an integer overflow bug not corrected in this reissuance.
Additionally, because the KEVM semantics properly tests every condition which could result in an exception, we found that we must bound the remaining `wordStack` size to 1016 to avoid a stack overflow exception.

We verified all the five functions implemented in HKG token program with preconditions stating that the code will not be called in contexts where the overflow may happen.

Conclusion
----------

With our semantics, we were able to not only catch the bug in Hacker Gold's ERC-20 compliant token using our semantics, but also find two overflow issues may occur in `HKG` token program.
In particular, since a bounded integer and stack size is a well known and documented limitation of the EVM, we did not explicitly reason about it during our initial proof attempts and were reminded to do so by the prover itself, further showing the power of full verification to find subtle cases in interactions between the contract and its underlying execution platform which may be missed by manual inspection and testing.

TODO
----

Right now we are proving complete specifications for each of the functions of the HKG token program, i.e., covering all the cases that the code covers.
To achieve a full verification, we need to analyze the cases when gas is not enough for the transaction and arithmetic overflow occurs at runtime.

HKG Token - Full Proof Claims
=============================

We now present reachability claims used for verification, one for each function in the ERC20 specification.
Since the HKG token contract contains only sequential code (no loops), we only need one reachability claim per branch per function.
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
