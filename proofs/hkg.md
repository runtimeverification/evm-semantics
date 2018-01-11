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
Since our HKG token contract contains only sequential code (without loops), each specification in our [specification file](hkg) contains a single claim for each branch.
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

-   `%HKG_Program` is the EVM bytecode for the ERC20-complaint Program;
-   `VALUE` represents the symbolic amount to transfer;
-   `BAL_FROM` and `BAL_TO` are the starting balances of accounts CALLER_ID and TO_ID, respectively;

Transfer Function
-----------------

```{.k .transfer1}
module TRANSFER1-SPEC
  imports ETHEREUM-SIMULATION

  rule
    <k>         #execute => (RETURN RET_ADDR:Int 32 ~> _) </k>
    <exit-code> 1                                         </exit-code>
    <mode>      NORMAL                                    </mode>
    <schedule>  DEFAULT                                   </schedule>
    <analysis>  /* _ */ .Map                              </analysis>

    <ethereum>
      <evm>
        <output>        /* _ */ .WordStack </output>
        <memoryUsed>    0 => _             </memoryUsed>
        <callDepth>     /* CALL_DEPTH */ 0 </callDepth>
        <callStack>     /* _ */ .List => _ </callStack>
        <interimStates> /* _ */ .List      </interimStates>
        <substateStack> /* _ */ .List      </substateStack>
        <callLog>       /* _ */ .Set       </callLog>

        <txExecState>
          <program>      %HKG_Program      </program>
          <programBytes> %HKG_ProgramBytes </programBytes>

          <id>     ACCT_ID   </id>
          <caller> CALLER_ID </caller>

          <callData>
            int2wordstack(F,     4)
            ++
            int2wordstack(TO_ID, 32)
            ++
            int2wordstack(VALUE, 32)
          </callData>

          <callValue> 0               </callValue>
          <wordStack> .WordStack => _ </wordStack>
          <localMem>
              .Map
              =>
              .Map[ RET_ADDR := int2wordstack(RET_VAL, 32) ]
              _:Map
          </localMem>
          <pc>          0 => _              </pc>
          <gas>         /* G */ 100000 => _ </gas>
          <previousGas> _ => _              </previousGas>
          <static>      false               </static>
        </txExecState>

        <substate>
          <selfDestruct> /* _ */ .Set </selfDestruct>
          <log>
          (
            .List
          =>
            ListItem({ ACCT_ID
                     | /* TODO: hash("Transfer(address,address,num256)") */ 100389287136786176327247604509743168900146139575972864366142685224231313322991
                     : CALLER_ID
                     : TO_ID
                     : .WordStack
                     | int2wordstack(VALUE, 32)
                     })
          )
            /* _ */
          </log>
          <refund> /* _ */ 0 => _ </refund> // TODO: more detail
        </substate>

        <gasPrice>         _         </gasPrice>
        <origin>           ORIGIN_ID </origin>
        <previousHash>     _         </previousHash>
        <ommersHash>       _         </ommersHash>
        <coinbase>         _         </coinbase>
        <stateRoot>        _         </stateRoot>
        <transactionsRoot> _         </transactionsRoot>
        <receiptsRoot>     _         </receiptsRoot>
        <logsBloom>        _         </logsBloom>
        <difficulty>       _         </difficulty>
        <number>           _         </number>
        <gasLimit>         _         </gasLimit>
        <gasUsed>          _         </gasUsed>
        <timestamp>        _         </timestamp>
        <extraData>        _         </extraData>
        <mixHash>          _         </mixHash>
        <blockNonce>       _         </blockNonce>

        <ommerBlockHeaders> _ </ommerBlockHeaders>
        <blockhash>         _ </blockhash>
      </evm>

      <network>
        <activeAccounts> ACCT_ID |-> false /* _ */ </activeAccounts>

        <accounts>
          <account>
            <acctID>  ACCT_ID           </acctID>
            <balance> _                 </balance>
            <code>    %HKG_ProgramBytes </code>
            <storage>
	          keccak(int2wordstack(CALLER_ID, 32) ++ #padToWidth(32, #asByteStack(1))) |-> (BAL_FROM => BAL_FROM -Int VALUE)
	          keccak(int2wordstack(TO_ID, 32)     ++ #padToWidth(32, #asByteStack(1))) |-> (BAL_TO   => BAL_TO +Int VALUE)
              _:Map
            </storage>
            <nonce> _              </nonce>
          </account>
          /* _ */
        </accounts>

        <txOrder>   _            </txOrder>
        <txPending> _            </txPending>
        <messages>  /* _ */ .Bag </messages>
      </network>
    </ethereum>
    requires 0 <=Int ACCT_ID   andBool ACCT_ID   <Int (2 ^Int 160)
     andBool 0 <=Int CALLER_ID andBool CALLER_ID <Int (2 ^Int 160)
     andBool 0 <=Int ORIGIN_ID andBool ORIGIN_ID <Int (2 ^Int 160)
     andBool F ==Int 2835717307 // TODO: auto gen
     andBool 0 <=Int TO_ID     andBool TO_ID     <Int (2 ^Int 160)
     //TODO: Add an extra case for exceptional return on 0.
     andBool 0 <Int VALUE      andBool VALUE     <Int (2 ^Int 256)
     andBool 0 <=Int BAL_FROM  andBool BAL_FROM  <Int (2 ^Int 256)
     andBool 0 <=Int BAL_TO    andBool BAL_TO    <Int (2 ^Int 256)
     andBool CALLER_ID =/=Int TO_ID
     andBool VALUE <=Int BAL_FROM
     andBool BAL_TO +Int VALUE <Int (2 ^Int 256) // viper overflow check: (VALUE ==Int 0 xorBool BAL_TO +Word VALUE >Int BAL_TO)
     andBool RET_VAL ==Int 1
   //andBool G >Int 100000

   // NOTE: negative VALUE is not possible since it is of `num256` type

  // to avoid unnecessary case split
  rule <k> LT W0 W1 => bool2int(W0  <Int W1) ~> #push ... </k> [trusted]
  rule <k> GT W0 W1 => bool2int(W0  >Int W1) ~> #push ... </k> [trusted]
  rule <k> EQ W0 W1 => bool2int(W0 ==Int W1) ~> #push ... </k> [trusted]
  rule <k> ISZERO W => bool2int(W  ==Int 0 ) ~> #push ... </k> [trusted]

endmodule

```

- When "to" address is the same as calling address, total amount should remained unchanged.

```{.k .transfer2}
module TRANSFER2-SPEC
  imports ETHEREUM-SIMULATION

  rule
    <k>         #execute => (RETURN RET_ADDR:Int 32 ~> _) </k>
    <exit-code> 1                                         </exit-code>
    <mode>      NORMAL                                    </mode>
    <schedule>  DEFAULT                                   </schedule>
    <analysis>  /* _ */ .Map                              </analysis>

    <ethereum>
      <evm>
        <output>        /* _ */ .WordStack </output>
        <memoryUsed>    0 => _             </memoryUsed>
        <callDepth>     /* CALL_DEPTH */ 0 </callDepth>
        <callStack>     /* _ */ .List => _ </callStack>
        <interimStates> /* _ */ .List      </interimStates>
        <substateStack> /* _ */ .List      </substateStack>
        <callLog>       /* _ */ .Set       </callLog>

        <txExecState>
          <program>      %HKG_Program      </program>
          <programBytes> %HKG_ProgramBytes </programBytes>

          <id>     ACCT_ID   </id>
          <caller> CALLER_ID </caller>

          <callData>
            int2wordstack(F,     4)
            ++
            int2wordstack(TO_ID, 32)
            ++
            int2wordstack(VALUE, 32)
          </callData>

          <callValue> 0               </callValue>
          <wordStack> .WordStack => _ </wordStack>
          <localMem>
              .Map
              =>
              .Map[ RET_ADDR := int2wordstack(RET_VAL, 32) ]
              _:Map
          </localMem>
          <pc>          0 => _              </pc>
          <gas>         /* G */ 100000 => _ </gas>
          <previousGas> _ => _              </previousGas>
          <static>      false               </static>
        </txExecState>

        <substate>
          <selfDestruct> /* _ */ .Set </selfDestruct>
          <log>
          (
            .List
          =>
            ListItem({ ACCT_ID
                     | /* TODO: hash("Transfer(address,address,num256)") */ 100389287136786176327247604509743168900146139575972864366142685224231313322991
                     : CALLER_ID
                     : TO_ID
                     : .WordStack
                     | int2wordstack(VALUE, 32)
                     })
          )
            /* _ */
          </log>
          <refund> /* _ */ 0 => _ </refund> // TODO: more detail
        </substate>

        <gasPrice>         _         </gasPrice>
        <origin>           ORIGIN_ID </origin>
        <previousHash>     _         </previousHash>
        <ommersHash>       _         </ommersHash>
        <coinbase>         _         </coinbase>
        <stateRoot>        _         </stateRoot>
        <transactionsRoot> _         </transactionsRoot>
        <receiptsRoot>     _         </receiptsRoot>
        <logsBloom>        _         </logsBloom>
        <difficulty>       _         </difficulty>
        <number>           _         </number>
        <gasLimit>         _         </gasLimit>
        <gasUsed>          _         </gasUsed>
        <timestamp>        _         </timestamp>
        <extraData>        _         </extraData>
        <mixHash>          _         </mixHash>
        <blockNonce>       _         </blockNonce>

        <ommerBlockHeaders> _ </ommerBlockHeaders>
        <blockhash>         _ </blockhash>
      </evm>

      <network>
        <activeAccounts> ACCT_ID |-> false /* _ */ </activeAccounts>

        <accounts>
          <account>
            <acctID>  ACCT_ID           </acctID>
            <balance> _                 </balance>
            <code>    %HKG_ProgramBytes </code>
            <storage>
	          keccak(int2wordstack(CALLER_ID, 32) ++ #padToWidth(32, #asByteStack(1))) |-> BAL_FROM
              _:Map
            </storage>
            <nonce> _              </nonce>
          </account>
          /* _ */
        </accounts>

        <txOrder>   _            </txOrder>
        <txPending> _            </txPending>
        <messages>  /* _ */ .Bag </messages>
      </network>
    </ethereum>
    requires 0 <=Int ACCT_ID   andBool ACCT_ID   <Int (2 ^Int 160)
     andBool 0 <=Int CALLER_ID andBool CALLER_ID <Int (2 ^Int 160)
     andBool 0 <=Int ORIGIN_ID andBool ORIGIN_ID <Int (2 ^Int 160)
     andBool F ==Int 2835717307 // TODO: auto gen
     andBool 0 <=Int TO_ID     andBool TO_ID     <Int (2 ^Int 160)
     //TODO: Add an extra case for exceptional return on 0.
     andBool 0 <Int VALUE      andBool VALUE     <Int (2 ^Int 256)
     andBool 0 <=Int BAL_FROM  andBool BAL_FROM  <Int (2 ^Int 256)
     andBool 0 <=Int BAL_TO    andBool BAL_TO    <Int (2 ^Int 256)
     andBool CALLER_ID ==Int TO_ID
     andBool VALUE <=Int BAL_FROM
     andBool RET_VAL ==Int 1
   //andBool G >Int 100000

   // NOTE: negative VALUE is not possible since it is of `num256` type

  // to avoid unnecessary case split
  rule <k> LT W0 W1 => bool2int(W0  <Int W1) ~> #push ... </k> [trusted]
  rule <k> GT W0 W1 => bool2int(W0  >Int W1) ~> #push ... </k> [trusted]
  rule <k> EQ W0 W1 => bool2int(W0 ==Int W1) ~> #push ... </k> [trusted]
  rule <k> ISZERO W => bool2int(W  ==Int 0 ) ~> #push ... </k> [trusted]

endmodule

```

```{.k .transfer3}
module TRANSFER3-SPEC
  imports ETHEREUM-SIMULATION

    rule
        <k>         #execute => (RETURN RET_ADDR:Int 32 ~> _) </k>
        <exit-code> 1                                         </exit-code>
        <mode>      NORMAL                                    </mode>
        <schedule>  DEFAULT                                   </schedule>
        <analysis>  /* _ */ .Map                              </analysis>

        <ethereum>
          <evm>
            <output>        /* _ */ .WordStack </output>
            <memoryUsed>    0 => _             </memoryUsed>
            <callDepth>     /* CALL_DEPTH */ 0 </callDepth>
            <callStack>     /* _ */ .List => _ </callStack>
            <interimStates> /* _ */ .List      </interimStates>
            <substateStack> /* _ */ .List      </substateStack>
            <callLog>       /* _ */ .Set       </callLog>

            <txExecState>
              <program>      %HKG_Program      </program>
              <programBytes> %HKG_ProgramBytes </programBytes>

              <id>     ACCT_ID   </id>
              <caller> CALLER_ID </caller>

              <callData>
                int2wordstack(F, 4)
                ++
                int2wordstack(TO_ID, 32)
                ++
                int2wordstack(VALUE, 32)
              </callData>

              <callValue> 0               </callValue>
              <wordStack> .WordStack => _ </wordStack>
              <localMem>
                .Map
                    =>
                .Map[ RET_ADDR := int2wordstack(RET_VAL, 32) ]
                _:Map
              </localMem>
              <pc>          0 => _              </pc>
              <gas>         /* G */ 100000 => _ </gas>
              <previousGas> _ => _              </previousGas>
              <static>      false               </static>
            </txExecState>

            <substate>
              <selfDestruct> /* _ */ .Set   </selfDestruct>
              <log>          /* _ */ .List  </log>
              <refund>       /* _ */ 0 => _ </refund>
            </substate>

            <gasPrice>          _         </gasPrice>
            <origin>            ORIGIN_ID </origin>

            <previousHash>      _         </previousHash>
            <ommersHash>        _         </ommersHash>
            <coinbase>          _         </coinbase>
            <stateRoot>         _         </stateRoot>
            <transactionsRoot>  _         </transactionsRoot>
            <receiptsRoot>      _         </receiptsRoot>
            <logsBloom>         _         </logsBloom>
            <difficulty>        _         </difficulty>
            <number>            _         </number>
            <gasLimit>          _         </gasLimit>
            <gasUsed>           _         </gasUsed>
            <timestamp>         _         </timestamp>
            <extraData>         _         </extraData>
            <mixHash>           _         </mixHash>
            <blockNonce>        _         </blockNonce>

            <ommerBlockHeaders> _         </ommerBlockHeaders>
            <blockhash>         _         </blockhash>
          </evm>

          <network>
            <activeAccounts> ACCT_ID |-> false /* _ */ </activeAccounts>

            <accounts>
              <account>
                <acctID>  ACCT_ID           </acctID>
                <balance> _                 </balance>
                <code>    %HKG_ProgramBytes </code>
                <storage>
                  keccak(int2wordstack(CALLER_ID, 32) ++ #padToWidth(32, #asByteStack(1))) |-> BAL_FROM
                  keccak(int2wordstack(TO_ID, 32)     ++ #padToWidth(32, #asByteStack(1))) |-> BAL_TO
                  _:Map
                </storage>
                <nonce>  _                  </nonce>
              </account>
              /* _ */
            </accounts>

            <txOrder>   _            </txOrder>
            <txPending> _            </txPending>
            <messages>  /* _ */ .Bag </messages>
          </network>
        </ethereum>
        requires 0 <=Int ACCT_ID   andBool ACCT_ID   <Int (2 ^Int 160)
         andBool 0 <=Int CALLER_ID andBool CALLER_ID <Int (2 ^Int 160)
         andBool 0 <=Int ORIGIN_ID andBool ORIGIN_ID <Int (2 ^Int 160)
         andBool F ==Int 2835717307 // TODO: auto gen
         andBool 0 <=Int TO_ID     andBool TO_ID     <Int (2 ^Int 160)
         // Todo: Extra Exception case for Value == 0
         andBool 0 <Int VALUE      andBool VALUE     <Int (2 ^Int 256)
         andBool 0 <=Int BAL_FROM  andBool BAL_FROM  <Int (2 ^Int 256)
         andBool 0 <=Int BAL_TO    andBool BAL_TO    <Int (2 ^Int 256)
         andBool CALLER_ID =/=Int TO_ID
         andBool VALUE >Int BAL_FROM
         andBool RET_VAL ==Int 0
          //orBool   BAL_TO +Int VALUE >=Int (2 ^Int 256) )
       //andBool G >Int 100000

    // TODO: properly consider exception preserving the input status
    //       using CALL GCAP ACCTTO VALUE ARGSTART ARGWIDTH RETSTART RETWIDTH

    // NOTE: negative VALUE is not possible since it is of `num256` type

      // to avoid unnecessary case split
      rule <k> LT W0 W1 => bool2int(W0  <Int W1) ~> #push ... </k> [trusted]
      rule <k> GT W0 W1 => bool2int(W0  >Int W1) ~> #push ... </k> [trusted]
      rule <k> EQ W0 W1 => bool2int(W0 ==Int W1) ~> #push ... </k> [trusted]
      rule <k> ISZERO W => bool2int(W  ==Int 0 ) ~> #push ... </k> [trusted]

endmodule

```

```{.k .transfer4}

module TRANSFER4-SPEC
    imports ETHEREUM-SIMULATION

    rule
        <k>         #execute => (RETURN RET_ADDR:Int 32 ~> _) </k>
        <exit-code> 1                                         </exit-code>
        <mode>      NORMAL                                    </mode>
        <schedule>  DEFAULT                                   </schedule>
        <analysis>  /* _ */ .Map                              </analysis>

        <ethereum>
          <evm>
            <output>        /* _ */ .WordStack </output>
            <memoryUsed>    0 => _             </memoryUsed>
            <callDepth>     /* CALL_DEPTH */ 0 </callDepth>
            <callStack>     /* _ */ .List => _ </callStack>
            <interimStates> /* _ */ .List      </interimStates>
            <substateStack> /* _ */ .List      </substateStack>
            <callLog>       /* _ */ .Set       </callLog>

            <txExecState>
              <program>      %HKG_Program      </program>
              <programBytes> %HKG_ProgramBytes </programBytes>

              <id>     ACCT_ID   </id>
              <caller> CALLER_ID </caller>

              <callData>
                int2wordstack(F, 4)
                ++
                int2wordstack(TO_ID, 32)
                ++
                int2wordstack(VALUE, 32)
              </callData>

              <callValue> 0               </callValue>
              <wordStack> .WordStack => _ </wordStack>
              <localMem>
                .Map
                    =>
                .Map[ RET_ADDR := int2wordstack(RET_VAL, 32) ]
                _:Map
              </localMem>
              <pc>          0 => _              </pc>
              <gas>         /* G */ 100000 => _ </gas>
              <previousGas> _ => _              </previousGas>
              <static>      false               </static>
            </txExecState>

            <substate>
              <selfDestruct> /* _ */ .Set   </selfDestruct>
              <log>          /* _ */ .List  </log>
              <refund>       /* _ */ 0 => _ </refund>
            </substate>

            <gasPrice>          _         </gasPrice>
            <origin>            ORIGIN_ID </origin>

            <previousHash>      _         </previousHash>
            <ommersHash>        _         </ommersHash>
            <coinbase>          _         </coinbase>
            <stateRoot>         _         </stateRoot>
            <transactionsRoot>  _         </transactionsRoot>
            <receiptsRoot>      _         </receiptsRoot>
            <logsBloom>         _         </logsBloom>
            <difficulty>        _         </difficulty>
            <number>            _         </number>
            <gasLimit>          _         </gasLimit>
            <gasUsed>           _         </gasUsed>
            <timestamp>         _         </timestamp>
            <extraData>         _         </extraData>
            <mixHash>           _         </mixHash>
            <blockNonce>        _         </blockNonce>

            <ommerBlockHeaders> _         </ommerBlockHeaders>
            <blockhash>         _         </blockhash>
          </evm>

          <network>
            <activeAccounts> ACCT_ID |-> false /* _ */ </activeAccounts>

            <accounts>
              <account>
                <acctID>  ACCT_ID           </acctID>
                <balance> _                 </balance>
                <code>    %HKG_ProgramBytes </code>
                <storage>
                  keccak(int2wordstack(CALLER_ID, 32) ++ #padToWidth(32, #asByteStack(1))) |-> BAL_FROM
                  _:Map
                </storage>
                <nonce>  _                  </nonce>
              </account>
              /* _ */
            </accounts>

            <txOrder>   _            </txOrder>
            <txPending> _            </txPending>
            <messages>  /* _ */ .Bag </messages>
          </network>
        </ethereum>
        requires 0 <=Int ACCT_ID   andBool ACCT_ID   <Int (2 ^Int 160)
         andBool 0 <=Int CALLER_ID andBool CALLER_ID <Int (2 ^Int 160)
         andBool 0 <=Int ORIGIN_ID andBool ORIGIN_ID <Int (2 ^Int 160)
         andBool F ==Int 2835717307 // TODO: auto gen
         andBool 0 <=Int TO_ID     andBool TO_ID     <Int (2 ^Int 160)
         // Todo: Extra Exception case for Value == 0
         andBool 0 <Int VALUE      andBool VALUE     <Int (2 ^Int 256)
         andBool 0 <=Int BAL_FROM  andBool BAL_FROM  <Int (2 ^Int 256)
         andBool 0 <=Int BAL_TO    andBool BAL_TO    <Int (2 ^Int 256)
        andBool CALLER_ID ==Int TO_ID
         andBool VALUE >Int BAL_FROM
         andBool RET_VAL ==Int 0
          //orBool   BAL_TO +Int VALUE >=Int (2 ^Int 256) )
       //andBool G >Int 100000

    // TODO: properly consider exception preserving the input status
    //       using CALL GCAP ACCTTO VALUE ARGSTART ARGWIDTH RETSTART RETWIDTH

    // NOTE: negative VALUE is not possible since it is of `num256` type

      // to avoid unnecessary case split
      rule <k> LT W0 W1 => bool2int(W0  <Int W1) ~> #push ... </k> [trusted]
      rule <k> GT W0 W1 => bool2int(W0  >Int W1) ~> #push ... </k> [trusted]
      rule <k> EQ W0 W1 => bool2int(W0 ==Int W1) ~> #push ... </k> [trusted]
      rule <k> ISZERO W => bool2int(W  ==Int 0 ) ~> #push ... </k> [trusted]
endmodule

```

```{.k .transfer5a}

module TRANSFER5-SPEC
  imports ETHEREUM-SIMULATION

    rule
        <k>         #execute => (RETURN RET_ADDR:Int 32 ~> _) </k>
        <exit-code> 1                                         </exit-code>
        <mode>      NORMAL                                    </mode>
        <schedule>  DEFAULT                                   </schedule>
        <analysis>  /* _ */ .Map                              </analysis>

        <ethereum>
          <evm>
            <output>        /* _ */ .WordStack </output>
            <memoryUsed>    0 => _             </memoryUsed>
            <callDepth>     /* CALL_DEPTH */ 0 </callDepth>
            <callStack>     /* _ */ .List => _ </callStack>
            <interimStates> /* _ */ .List      </interimStates>
            <substateStack> /* _ */ .List      </substateStack>
            <callLog>       /* _ */ .Set       </callLog>

            <txExecState>
              <program>      %HKG_Program      </program>
              <programBytes> %HKG_ProgramBytes </programBytes>

              <id>     ACCT_ID   </id>
              <caller> CALLER_ID </caller>

              <callData>
                int2wordstack(F, 4)
                ++
                int2wordstack(TO_ID, 32)
                ++
                int2wordstack(VALUE, 32)
              </callData>

              <callValue> 0               </callValue>
              <wordStack> .WordStack => _ </wordStack>
              <localMem>
                .Map
                    =>
                .Map[ RET_ADDR := int2wordstack(RET_VAL, 32) ]
                _:Map
              </localMem>
              <pc>          0 => _              </pc>
              <gas>         /* G */ 100000 => _ </gas>
              <previousGas> _ => _              </previousGas>
              <static>      false               </static>
            </txExecState>

            <substate>
              <selfDestruct> /* _ */ .Set   </selfDestruct>
              <log>          /* _ */ .List  </log>
              <refund>       /* _ */ 0 => _ </refund>
            </substate>

            <gasPrice>          _         </gasPrice>
            <origin>            ORIGIN_ID </origin>

            <previousHash>      _         </previousHash>
            <ommersHash>        _         </ommersHash>
            <coinbase>          _         </coinbase>
            <stateRoot>         _         </stateRoot>
            <transactionsRoot>  _         </transactionsRoot>
            <receiptsRoot>      _         </receiptsRoot>
            <logsBloom>         _         </logsBloom>
            <difficulty>        _         </difficulty>
            <number>            _         </number>
            <gasLimit>          _         </gasLimit>
            <gasUsed>           _         </gasUsed>
            <timestamp>         _         </timestamp>
            <extraData>         _         </extraData>
            <mixHash>           _         </mixHash>
            <blockNonce>        _         </blockNonce>

            <ommerBlockHeaders> _         </ommerBlockHeaders>
            <blockhash>         _         </blockhash>
          </evm>

          <network>
            <activeAccounts> ACCT_ID |-> false /* _ */ </activeAccounts>

            <accounts>
              <account>
                <acctID>  ACCT_ID           </acctID>
                <balance> _                 </balance>
                <code>    %HKG_ProgramBytes </code>
                <storage>
                  keccak(int2wordstack(CALLER_ID, 32) ++ #padToWidth(32, #asByteStack(1))) |-> BAL_FROM
                  keccak(int2wordstack(TO_ID, 32)     ++ #padToWidth(32, #asByteStack(1))) |-> BAL_TO
                  _:Map
                </storage>
                <nonce>  _                  </nonce>
              </account>
              /* _ */
            </accounts>

            <txOrder>   _            </txOrder>
            <txPending> _            </txPending>
            <messages>  /* _ */ .Bag </messages>
          </network>
        </ethereum>
        requires 0 <=Int ACCT_ID   andBool ACCT_ID   <Int (2 ^Int 160)
         andBool 0 <=Int CALLER_ID andBool CALLER_ID <Int (2 ^Int 160)
         andBool 0 <=Int ORIGIN_ID andBool ORIGIN_ID <Int (2 ^Int 160)
         andBool F ==Int 2835717307 // TODO: auto gen
         andBool 0 <=Int TO_ID     andBool TO_ID     <Int (2 ^Int 160)
         andBool 0 ==Int VALUE
         andBool 0 <=Int BAL_FROM  andBool BAL_FROM  <Int (2 ^Int 256)
         andBool 0 <=Int BAL_TO    andBool BAL_TO    <Int (2 ^Int 256)
         andBool CALLER_ID =/=Int TO_ID
         andBool RET_VAL ==Int 0
          //orBool   BAL_TO +Int VALUE >=Int (2 ^Int 256) )
       //andBool G >Int 100000

    // TODO: properly consider exception preserving the input status
    //       using CALL GCAP ACCTTO VALUE ARGSTART ARGWIDTH RETSTART RETWIDTH

    // NOTE: negative VALUE is not possible since it is of `num256` type

      // to avoid unnecessary case split
      rule <k> LT W0 W1 => bool2int(W0  <Int W1) ~> #push ... </k> [trusted]
      rule <k> GT W0 W1 => bool2int(W0  >Int W1) ~> #push ... </k> [trusted]
      rule <k> EQ W0 W1 => bool2int(W0 ==Int W1) ~> #push ... </k> [trusted]
      rule <k> ISZERO W => bool2int(W  ==Int 0 ) ~> #push ... </k> [trusted]

endmodule

```

```{.k .transfer5b}
module TRANSFER5-SPEC
  imports ETHEREUM-SIMULATION

    rule
        <k>         #execute => (RETURN RET_ADDR:Int 32 ~> _) </k>
        <exit-code> 1                                         </exit-code>
        <mode>      NORMAL                                    </mode>
        <schedule>  DEFAULT                                   </schedule>
        <analysis>  /* _ */ .Map                              </analysis>

        <ethereum>
          <evm>
            <output>        /* _ */ .WordStack </output>
            <memoryUsed>    0 => _             </memoryUsed>
            <callDepth>     /* CALL_DEPTH */ 0 </callDepth>
            <callStack>     /* _ */ .List => _ </callStack>
            <interimStates> /* _ */ .List      </interimStates>
            <substateStack> /* _ */ .List      </substateStack>
            <callLog>       /* _ */ .Set       </callLog>

            <txExecState>
              <program>      %HKG_Program      </program>
              <programBytes> %HKG_ProgramBytes </programBytes>

              <id>     ACCT_ID   </id>
              <caller> CALLER_ID </caller>

              <callData>
                int2wordstack(F, 4)
                ++
                int2wordstack(TO_ID, 32)
                ++
                int2wordstack(VALUE, 32)
              </callData>

              <callValue> 0               </callValue>
              <wordStack> .WordStack => _ </wordStack>
              <localMem>
                .Map
                    =>
                .Map[ RET_ADDR := int2wordstack(RET_VAL, 32) ]
                _:Map
              </localMem>
              <pc>          0 => _              </pc>
              <gas>         /* G */ 100000 => _ </gas>
              <previousGas> _ => _              </previousGas>
              <static>      false               </static>
            </txExecState>

            <substate>
              <selfDestruct> /* _ */ .Set   </selfDestruct>
              <log>          /* _ */ .List  </log>
              <refund>       /* _ */ 0 => _ </refund>
            </substate>

            <gasPrice>          _         </gasPrice>
            <origin>            ORIGIN_ID </origin>

            <previousHash>      _         </previousHash>
            <ommersHash>        _         </ommersHash>
            <coinbase>          _         </coinbase>
            <stateRoot>         _         </stateRoot>
            <transactionsRoot>  _         </transactionsRoot>
            <receiptsRoot>      _         </receiptsRoot>
            <logsBloom>         _         </logsBloom>
            <difficulty>        _         </difficulty>
            <number>            _         </number>
            <gasLimit>          _         </gasLimit>
            <gasUsed>           _         </gasUsed>
            <timestamp>         _         </timestamp>
            <extraData>         _         </extraData>
            <mixHash>           _         </mixHash>
            <blockNonce>        _         </blockNonce>

            <ommerBlockHeaders> _         </ommerBlockHeaders>
            <blockhash>         _         </blockhash>
          </evm>

          <network>
            <activeAccounts> ACCT_ID |-> false /* _ */ </activeAccounts>

            <accounts>
              <account>
                <acctID>  ACCT_ID           </acctID>
                <balance> _                 </balance>
                <code>    %HKG_ProgramBytes </code>
                <storage>
                  keccak(int2wordstack(CALLER_ID, 32) ++ #padToWidth(32, #asByteStack(1))) |-> BAL_FROM
                  _:Map
                </storage>
                <nonce>  _                  </nonce>
              </account>
              /* _ */
            </accounts>

            <txOrder>   _            </txOrder>
            <txPending> _            </txPending>
            <messages>  /* _ */ .Bag </messages>
          </network>
        </ethereum>
        requires 0 <=Int ACCT_ID   andBool ACCT_ID   <Int (2 ^Int 160)
         andBool 0 <=Int CALLER_ID andBool CALLER_ID <Int (2 ^Int 160)
         andBool 0 <=Int ORIGIN_ID andBool ORIGIN_ID <Int (2 ^Int 160)
         andBool F ==Int 2835717307 // TODO: auto gen
         andBool 0 <=Int TO_ID     andBool TO_ID     <Int (2 ^Int 160)
         andBool 0 ==Int VALUE
         andBool 0 <=Int BAL_FROM  andBool BAL_FROM  <Int (2 ^Int 256)
         andBool 0 <=Int BAL_TO    andBool BAL_TO    <Int (2 ^Int 256)
         andBool CALLER_ID ==Int TO_ID
         andBool RET_VAL ==Int 0
          //orBool   BAL_TO +Int VALUE >=Int (2 ^Int 256) )
       //andBool G >Int 100000

    // TODO: properly consider exception preserving the input status
    //       using CALL GCAP ACCTTO VALUE ARGSTART ARGWIDTH RETSTART RETWIDTH

    // NOTE: negative VALUE is not possible since it is of `num256` type

      // to avoid unnecessary case split
      rule <k> LT W0 W1 => bool2int(W0  <Int W1) ~> #push ... </k> [trusted]
      rule <k> GT W0 W1 => bool2int(W0  >Int W1) ~> #push ... </k> [trusted]
      rule <k> EQ W0 W1 => bool2int(W0 ==Int W1) ~> #push ... </k> [trusted]
      rule <k> ISZERO W => bool2int(W  ==Int 0 ) ~> #push ... </k> [trusted]

endmodule

```


TransferFrom Function
---------------------


```{.k .transferFrom1}
module TRANSFERFROM-SPEC
  imports ETHEREUM-SIMULATION

  rule
    <k>         #execute => (RETURN RET_ADDR:Int 32 ~> _) </k>
    <exit-code> 1                                         </exit-code>
    <mode>      NORMAL                                    </mode>
    <schedule>  DEFAULT                                   </schedule>
    <analysis>  /* _ */ .Map                              </analysis>

    <ethereum>
      <evm>
        <output>        /* _ */ .WordStack </output>
        <memoryUsed>    0 => _             </memoryUsed>
        <callDepth>     /* CALL_DEPTH */ 0 </callDepth>
        <callStack>     /* _ */ .List => _ </callStack>
        <interimStates> /* _ */ .List      </interimStates>
        <substateStack> /* _ */ .List      </substateStack>
        <callLog>       /* _ */ .Set       </callLog>

        <txExecState>
          <program>      %HKG_Program      </program>
          <programBytes> %HKG_ProgramBytes </programBytes>

          <id>           ACCT_ID      </id>
          <caller>       CALLER_ID    </caller>

          <callData>
            int2wordstack(F, 4)
            ++
            int2wordstack(FROM_ID, 32)
            ++
            int2wordstack(TO_ID, 32)
            ++
            int2wordstack(VALUE, 32)
          </callData>

          <callValue> 0 </callValue>
          <wordStack> .WordStack => _ </wordStack>
          <localMem>
            .Map
                           =>
            .Map[ RET_ADDR := int2wordstack(RET_VAL, 32) ]
            _:Map
          </localMem>
          <pc>          0 => _              </pc>
          <gas>         /* G */ 100000 => _ </gas>
          <previousGas> _ => _              </previousGas>
          <static>     false                </static>
        </txExecState>

        <substate>
          <selfDestruct> /* _ */ .Set </selfDestruct>
          <log>
          (
            .List
          =>
            ListItem({ ACCT_ID
                     | /* TODO: hash("Transfer(address,address,num256)") */ 100389287136786176327247604509743168900146139575972864366142685224231313322991
                     : FROM_ID
                     : TO_ID
                     : .WordStack
                     | int2wordstack(VALUE, 32)
                     })
          )
            /* _ */
          </log>
          <refund> /* _ */ 0 => _ </refund>
        </substate>

        <gasPrice>          _         </gasPrice>
        <origin>            ORIGIN_ID </origin>

        <previousHash>      _         </previousHash>
        <ommersHash>        _         </ommersHash>
        <coinbase>          _         </coinbase>
        <stateRoot>         _         </stateRoot>
        <transactionsRoot>  _         </transactionsRoot>
        <receiptsRoot>      _         </receiptsRoot>
        <logsBloom>         _         </logsBloom>
        <difficulty>        _         </difficulty>
        <number>            _         </number>
        <gasLimit>          _         </gasLimit>
        <gasUsed>           _         </gasUsed>
        <timestamp>         _         </timestamp>
        <extraData>         _         </extraData>
        <mixHash>           _         </mixHash>
        <blockNonce>        _         </blockNonce>

        <ommerBlockHeaders> _         </ommerBlockHeaders>
        <blockhash>         _         </blockhash>
      </evm>

      <network>
        <activeAccounts> ACCT_ID |-> false /* _ */ </activeAccounts>

        <accounts>
          <account>
            <acctID> ACCT_ID </acctID>
            <balance> _ </balance>
            <code> %HKG_ProgramBytes </code>
            <storage>
              // sha3(0) +Word FROM_ID |-> (BAL_FROM => BAL_FROM -Int VALUE) // TODO: auto gen
              // sha3(0) +Word TO_ID   |-> (BAL_TO   => BAL_TO   +Int VALUE) // TODO: auto gen
              // sha3(sha3(1) +Word FROM_ID) +Word CALLER_ID |-> (ALLOW => ALLOW -Int VALUE)
	          keccak(int2wordstack(FROM_ID, 32) ++ #padToWidth(32, #asByteStack(1)))                                                            |-> (BAL_FROM => BAL_FROM -Int VALUE )
	          keccak(int2wordstack(TO_ID, 32)     ++ #padToWidth(32, #asByteStack(1)))                                                            |-> (BAL_TO   => BAL_TO   +Int VALUE )
       	      keccak(int2wordstack(CALLER_ID, 32)   ++ int2wordstack(keccak(int2wordstack(FROM_ID, 32) ++ #padToWidth(32, #asByteStack(2))), 32)) |-> (ALLOW    => ALLOW    -Int VALUE )
              _:Map
            </storage>
            <nonce> _ </nonce>
          </account>
          /* _ */
        </accounts>

        <txOrder> _ </txOrder>
        <txPending> _ </txPending>
        <messages> /* _ */ .Bag </messages>
      </network>
    </ethereum>
    requires 0 <=Int ACCT_ID   andBool ACCT_ID   <Int (2 ^Int 160)
     andBool 0 <=Int CALLER_ID andBool CALLER_ID <Int (2 ^Int 160)
     andBool 0 <=Int ORIGIN_ID andBool ORIGIN_ID <Int (2 ^Int 160)
     andBool F ==Int 599290589 // TODO: auto gen
     andBool 0 <=Int FROM_ID   andBool FROM_ID   <Int (2 ^Int 160)
     andBool 0 <=Int TO_ID     andBool TO_ID     <Int (2 ^Int 160)
     //TODO: Add Alternative else proof for exception when value is 0
     andBool 0 <Int VALUE     andBool  VALUE     <Int (2 ^Int 256)
     andBool 0 <=Int BAL_FROM  andBool BAL_FROM  <Int (2 ^Int 256)
     andBool 0 <=Int BAL_TO    andBool BAL_TO    <Int (2 ^Int 256)
     andBool 0 <=Int ALLOW     andBool ALLOW     <Int (2 ^Int 256)
     andBool FROM_ID =/=Int TO_ID
     andBool VALUE <=Int BAL_FROM
     andBool BAL_TO +Int VALUE <Int (2 ^Int 256) // viper overflow check: (VALUE ==Int 0 xorBool BAL_TO +Word VALUE >Int BAL_TO)
     andBool VALUE <=Int ALLOW
     andBool RET_VAL ==Int 1
   //andBool G >Int 100000

// NOTE: negative VALUE is not possible since it is of `num256` type

  // to avoid unnecessary case split
  rule <k> LT W0 W1 => bool2int(W0  <Int W1) ~> #push ... </k> [trusted]
  rule <k> GT W0 W1 => bool2int(W0  >Int W1) ~> #push ... </k> [trusted]
  rule <k> EQ W0 W1 => bool2int(W0 ==Int W1) ~> #push ... </k> [trusted]
  rule <k> ISZERO W => bool2int(W  ==Int 0 ) ~> #push ... </k> [trusted]

endmodule

```

```{.k .transferFrom2}
module TRANSFERFROM2-SPEC
  imports ETHEREUM-SIMULATION

  rule
    <k>         #execute => (RETURN RET_ADDR:Int 32 ~> _) </k>
    <exit-code> 1                                         </exit-code>
    <mode>      NORMAL                                    </mode>
    <schedule>  DEFAULT                                   </schedule>
    <analysis>  /* _ */ .Map                              </analysis>

    <ethereum>
      <evm>
        <output>        /* _ */ .WordStack </output>
        <memoryUsed>    0 => _             </memoryUsed>
        <callDepth>     /* CALL_DEPTH */ 0 </callDepth>
        <callStack>     /* _ */ .List => _ </callStack>
        <interimStates> /* _ */ .List      </interimStates>
        <substateStack> /* _ */ .List      </substateStack>
        <callLog>       /* _ */ .Set       </callLog>

        <txExecState>
          <program>      %HKG_Program      </program>
          <programBytes> %HKG_ProgramBytes </programBytes>

          <id>           ACCT_ID      </id>
          <caller>       CALLER_ID    </caller>

          <callData>
            int2wordstack(F, 4)
            ++
            int2wordstack(FROM_ID, 32)
            ++
            int2wordstack(TO_ID, 32)
            ++
            int2wordstack(VALUE, 32)
          </callData>

          <callValue> 0               </callValue>
          <wordStack> .WordStack => _ </wordStack>
          <localMem>
            .Map
                           =>
            .Map[ RET_ADDR := int2wordstack(RET_VAL, 32) ]
            _:Map
          </localMem>
          <pc>          0 => _              </pc>
          <gas>         /* G */ 100000 => _ </gas>
          <previousGas> _ => _              </previousGas>
          <static>      false               </static>
        </txExecState>

        <substate>
          <selfDestruct> /* _ */ .Set </selfDestruct>
          <log>
          (
            .List
          =>
            ListItem({ ACCT_ID
                     | /* TODO: hash("Transfer(address,address,num256)") */ 100389287136786176327247604509743168900146139575972864366142685224231313322991
                     : FROM_ID
                     : TO_ID
                     : .WordStack
                     | int2wordstack(VALUE, 32)
                     })
          )
            /* _ */
          </log>
          <refund> /* _ */ 0 => _ </refund>
        </substate>

        <gasPrice>          _         </gasPrice>
        <origin>            ORIGIN_ID </origin>

        <previousHash>      _         </previousHash>
        <ommersHash>        _         </ommersHash>
        <coinbase>          _         </coinbase>
        <stateRoot>         _         </stateRoot>
        <transactionsRoot>  _         </transactionsRoot>
        <receiptsRoot>      _         </receiptsRoot>
        <logsBloom>         _         </logsBloom>
        <difficulty>        _         </difficulty>
        <number>            _         </number>
        <gasLimit>          _         </gasLimit>
        <gasUsed>           _         </gasUsed>
        <timestamp>         _         </timestamp>
        <extraData>         _         </extraData>
        <mixHash>           _         </mixHash>
        <blockNonce>        _         </blockNonce>

        <ommerBlockHeaders> _         </ommerBlockHeaders>
        <blockhash>         _         </blockhash>
      </evm>

      <network>
        <activeAccounts> ACCT_ID |-> false /* _ */ </activeAccounts>

        <accounts>
          <account>
            <acctID> ACCT_ID </acctID>
            <balance> _ </balance>
            <code> %HKG_ProgramBytes </code>
            <storage>
	          keccak(int2wordstack(FROM_ID, 32) ++ #padToWidth(32, #asByteStack(1)))                                                              |-> BAL_FROM
       	      keccak(int2wordstack(CALLER_ID, 32)   ++ int2wordstack(keccak(int2wordstack(FROM_ID, 32) ++ #padToWidth(32, #asByteStack(2))), 32)) |-> (ALLOW   => ALLOW    -Int VALUE )
              _:Map
            </storage>
            <nonce> _ </nonce>
          </account>
          /* _ */
        </accounts>

        <txOrder> _ </txOrder>
        <txPending> _ </txPending>
        <messages> /* _ */ .Bag </messages>
      </network>
    </ethereum>
    requires 0 <=Int ACCT_ID   andBool ACCT_ID   <Int (2 ^Int 160)
     andBool 0 <=Int CALLER_ID andBool CALLER_ID <Int (2 ^Int 160)
     andBool 0 <=Int ORIGIN_ID andBool ORIGIN_ID <Int (2 ^Int 160)
     andBool F ==Int 599290589 // TODO: auto gen
     andBool 0 <=Int FROM_ID   andBool FROM_ID   <Int (2 ^Int 160)
     andBool 0 <=Int TO_ID     andBool TO_ID     <Int (2 ^Int 160)
     //TODO: Add Alternative else proof for exception when value is 0
     andBool 0 <Int VALUE     andBool  VALUE     <Int (2 ^Int 256)
     andBool 0 <=Int BAL_FROM  andBool BAL_FROM  <Int (2 ^Int 256)
     andBool 0 <=Int BAL_TO    andBool BAL_TO    <Int (2 ^Int 256)
     andBool 0 <=Int ALLOW     andBool ALLOW     <Int (2 ^Int 256)
     andBool FROM_ID ==Int TO_ID
     andBool VALUE <=Int BAL_FROM
     andBool BAL_TO +Int VALUE <Int (2 ^Int 256) // viper overflow check: (VALUE ==Int 0 xorBool BAL_TO +Word VALUE >Int BAL_TO)
     andBool VALUE <=Int ALLOW
     andBool RET_VAL ==Int 1
   //andBool G >Int 100000

// NOTE: negative VALUE is not possible since it is of `num256` type

  // to avoid unnecessary case split
  rule <k> LT W0 W1 => bool2int(W0  <Int W1) ~> #push ... </k> [trusted]
  rule <k> GT W0 W1 => bool2int(W0  >Int W1) ~> #push ... </k> [trusted]
  rule <k> EQ W0 W1 => bool2int(W0 ==Int W1) ~> #push ... </k> [trusted]
  rule <k> ISZERO W => bool2int(W  ==Int 0 ) ~> #push ... </k> [trusted]

endmodule

```

Allowance Function
------------------

Here we provide a specification file containing a reachability rule for the verifying the correctness of the HKG Token's Allowance Function.

```{.k .allowance}
module TOKEN-SPEC
imports ETHEREUM-SIMULATION

  rule
    <k>         #execute => (RETURN R:Int 32  ~> _) </k>
    <exit-code> 1                                   </exit-code>
    <mode>      NORMAL                              </mode>
    <schedule>  DEFAULT                             </schedule>
    <analysis>  /* _ */ .Map                        </analysis>

    <ethereum>
      <evm>
        <output>        /* _ */ .WordStack </output>
        <memoryUsed>    0 => _             </memoryUsed>
        <callDepth>     /* CALL_DEPTH */ 0 </callDepth>
        <callStack>     /* _ */ .List => _ </callStack>
        <interimStates> /* _ */ .List      </interimStates>
        <substateStack> /* _ */ .List      </substateStack>
        <callLog>       /* _ */ .Set       </callLog>

        <txExecState>
          <program>      %HKG_Program      </program>
          <programBytes> %HKG_ProgramBytes </programBytes>

          <id>     ACCT_ID   </id>
          <caller> CALLER_ID </caller>

          <callData> #abiCallData("allowance", #address(OWNER), #address(SPENDER)) </callData>

          <callValue> 0               </callValue>
          <wordStack> .WordStack => _ </wordStack>

          <localMem>
            .Map => ( .Map[ R := #asByteStackInWidth(ALLOWANCE, 32) ] _:Map)
          </localMem>

          <pc>          0  => _            </pc>
          <gas>         /* G */ 20000 => _ </gas>
          <previousGas> _ => _             </previousGas>
          <static>      false              </static>
        </txExecState>

        <substate>
          <selfDestruct> /* _ */ .Set  </selfDestruct>
          <log>          /* _ */ .List </log>
          <refund>       /* _ */ 0     </refund>
        </substate>

        <gasPrice>         _         </gasPrice>
        <origin>           ORIGIN_ID </origin>
        <previousHash>     _         </previousHash>
        <ommersHash>       _         </ommersHash>
        <coinbase>         _         </coinbase>
        <stateRoot>        _         </stateRoot>
        <transactionsRoot> _         </transactionsRoot>
        <receiptsRoot>     _         </receiptsRoot>
        <logsBloom>        _         </logsBloom>
        <difficulty>       _         </difficulty>
        <number>           _         </number>
        <gasLimit>         _         </gasLimit>
        <gasUsed>          _         </gasUsed>
        <timestamp>        _         </timestamp>
        <extraData>        _         </extraData>
        <mixHash>          _         </mixHash>
        <blockNonce>       _         </blockNonce>

        <ommerBlockHeaders> _ </ommerBlockHeaders>
        <blockhash>         _ </blockhash>
      </evm>

      <network>
        <activeAccounts> ACCT_ID |-> false /* _ */ </activeAccounts>

        <accounts>
          <account>
            <acctID>  ACCT_ID           </acctID>
            <balance> _                 </balance>
            <code>    %HKG_ProgramBytes </code>
            <storage>
              keccak(#asByteStackInWidth(SPENDER, 32) ++ #asByteStackInWidth(keccak(#asByteStackInWidth(OWNER, 32) ++ #asByteStackInWidth(2, 32)), 32)) |-> ALLOWANCE
              _:Map
            </storage>
            <nonce>  _                  </nonce>
          </account>
          /* _ */
        </accounts>

        <txOrder>   _            </txOrder>
        <txPending> _            </txPending>
        <messages>  /* _ */ .Bag </messages>
      </network>
    </ethereum>
    requires 0 <=Int ACCT_ID   andBool ACCT_ID   <Int (2 ^Int 160)
     andBool 0 <=Int CALLER_ID andBool CALLER_ID <Int (2 ^Int 160)
     andBool 0 <=Int ORIGIN_ID andBool ORIGIN_ID <Int (2 ^Int 160)
     andBool 0 <=Int OWNER     andBool OWNER     <Int (2 ^Int 160)
     andBool 0 <=Int SPENDER   andBool SPENDER   <Int (2 ^Int 160)
     andBool 0 <=Int ALLOWANCE andBool ALLOWANCE <Int (2 ^Int 256)

endmodule
```

Approve Function
----------------

Here we provide a specification file containing a reachability rule for the verifying the correctness of the HKG Token's APPROVE Function.

```{.k .approve}
module APPROVE-SPEC
  imports ETHEREUM-SIMULATION

  rule
    <k> #execute => (RETURN RET_ADDR:Int 32 ~> _) </k> // TODO: auto gen
    <exit-code> 1 </exit-code>
    <mode> NORMAL </mode>
    <schedule> DEFAULT </schedule> // TODO: pick a right one
    <analysis> /* _ */ .Map </analysis>

    <ethereum>
      <evm>
        <output> /* _ */ .WordStack </output>
        <memoryUsed> 0 => _ </memoryUsed>
        <callDepth> /* CALL_DEPTH */ 0 </callDepth> // TODO: check if <= 1024
        <callStack> /* _ */ .List => _ </callStack>
        <interimStates> /* _ */ .List </interimStates>
        <substateStack> /* _ */ .List </substateStack>
        <callLog> /* _ */ .Set </callLog>

        <txExecState>
          <program>
		%HKG_Program
          </program>
          <programBytes>
		%HKG_ProgramBytes
          </programBytes>

          <id> ACCT_ID </id> // contract owner
          <caller> CALLER_ID </caller> // who called this contract; in the begining, origin

          <callData> // TODO: auto gen
            int2wordstack(F, 4)
            ++
            int2wordstack(SPENDER, 32)
            ++
            int2wordstack(VALUE, 32)
          </callData>

          <callValue> 0 </callValue>
          <wordStack> .WordStack => _ </wordStack>
          <localMem> // TODO: auto gen
            .Map
          =>
            .Map[ RET_ADDR := int2wordstack(RET_VAL, 32) ]
            _:Map
          </localMem>
          <pc> 0 => _ </pc>
          <gas> /* G */ 100000 => _ </gas> // NOTE: user provided
          <previousGas> _ => _ </previousGas>
          <static> false </static>
        </txExecState>

        <substate>
          <selfDestruct> /* _ */ .Set </selfDestruct>
          <log>
          (
            .List
          =>
            ListItem({ ACCT_ID
                     | /* TODO: hash("Approval(address,address,num256)") */ 63486140976153616755203102783360879283472101686154884697241723088393386309925
                     : CALLER_ID
                     : SPENDER
                     : .WordStack
                     | int2wordstack(VALUE, 32)
                     })
          )
            /* _ */
          </log>
          <refund> /* _ */ 0 => _ </refund> // TODO: more detail
        </substate>

        <gasPrice> _ </gasPrice>
        <origin> ORIGIN_ID </origin> // who fires tx

        <previousHash> _ </previousHash>
        <ommersHash> _ </ommersHash>
        <coinbase> _ </coinbase>
        <stateRoot> _ </stateRoot>
        <transactionsRoot> _ </transactionsRoot>
        <receiptsRoot> _ </receiptsRoot>
        <logsBloom> _ </logsBloom>
        <difficulty> _ </difficulty>
        <number> _ </number>
        <gasLimit> _ </gasLimit>
        <gasUsed> _ </gasUsed>
        <timestamp> _ </timestamp>
        <extraData> _ </extraData>
        <mixHash> _ </mixHash>
        <blockNonce> _ </blockNonce>

        <ommerBlockHeaders> _ </ommerBlockHeaders>
        <blockhash> _ </blockhash>
      </evm>

      <network>
        <activeAccounts> ACCT_ID |-> false /* _ */ </activeAccounts>

        <accounts>
          <account>
            <acctID> ACCT_ID </acctID>
            <balance> _ </balance>
            <code>
		        %HKG_ProgramBytes
            </code>
            <storage>
	    keccak(int2wordstack(SPENDER, 32) ++ int2wordstack(keccak(int2wordstack(CALLER_ID, 32) ++ #padToWidth(32, #asByteStack(2))), 32)) |-> (_:Int => VALUE)
              _:Map
            </storage>
            <nonce> _ </nonce>
          </account>
          /* _ */
        </accounts>

        <txOrder> _ </txOrder>
        <txPending> _ </txPending>
        <messages> /* _ */ .Bag </messages>
      </network>
    </ethereum>
    requires 0 <=Int ACCT_ID   andBool ACCT_ID   <Int (2 ^Int 160)
     andBool 0 <=Int CALLER_ID andBool CALLER_ID <Int (2 ^Int 160)
     andBool 0 <=Int ORIGIN_ID andBool ORIGIN_ID <Int (2 ^Int 160)
     andBool F ==Int 157198259 // TODO: auto gen
     andBool 0 <=Int SPENDER   andBool SPENDER   <Int (2 ^Int 160)
     andBool 0 <=Int VALUE     andBool VALUE     <Int (2 ^Int 256)
     andBool RET_VAL ==Int 1
   //andBool G >Int 100000

// NOTE: negative VALUE is not possible since it is of `num256` type

endmodule
```

BalanceOf Function
------------------

Here we provide a specification file containing a reachability rule for the verifying the correctness of the HKG Token's BalanceOf Function.

```{.k .balanceOf}
module BALANCE-OF-SPEC
    imports ETHEREUM-SIMULATION
  rule
    <k> #execute => (RETURN R:Int 32  ~> _) </k>
    <exit-code> 1 </exit-code>
    <mode> NORMAL </mode>
    <schedule> DEFAULT </schedule> // TODO: pick a right one
    <analysis> /* _ */ .Map </analysis>

    <ethereum>
      <evm>
        <output> /* _ */ .WordStack </output>
        <memoryUsed> 0 => _ </memoryUsed>
        <callDepth> /* CALL_DEPTH */ 0 </callDepth> // TODO: check if <= 1024
        <callStack> /* _ */ .List => _ </callStack>
        <interimStates> /* _ */ .List </interimStates>
        <substateStack> /* _ */ .List </substateStack>
        <callLog> /* _ */ .Set </callLog>

        <txExecState>
          <program>
		%HKG_Program
          </program>
          <programBytes>
		%HKG_ProgramBytes
          </programBytes>

          <id> ACCT_ID </id> // contract owner
          <caller> CALLER_ID </caller> // who called this contract; in the begining, origin

          <callData>
            int2wordstack(F, 4)
            ++
            int2wordstack(O, 32)
          </callData>

          <callValue> 0 </callValue>
          <wordStack> .WordStack => _ </wordStack>
          <localMem>
            .Map
          =>
          (
            .Map[ R := int2wordstack(B, 32) ]
	    _:Map
          )
          </localMem>
          <pc> 0  => _ </pc>
          <gas> /* G */ 20000 => _ </gas>
          <previousGas> _ => _ </previousGas>
          <static> false </static>
        </txExecState>

        <substate>
          <selfDestruct> /* _ */ .Set </selfDestruct>
          <log> /* _ */ .List </log>
          <refund> /* _ */ 0 </refund>
        </substate>

        <gasPrice> _ </gasPrice>
        <origin> ORIGIN_ID </origin> // who fires tx

        <previousHash> _ </previousHash>
        <ommersHash> _ </ommersHash>
        <coinbase> _ </coinbase>
        <stateRoot> _ </stateRoot>
        <transactionsRoot> _ </transactionsRoot>
        <receiptsRoot> _ </receiptsRoot>
        <logsBloom> _ </logsBloom>
        <difficulty> _ </difficulty>
        <number> _ </number>
        <gasLimit> _ </gasLimit>
        <gasUsed> _ </gasUsed>
        <timestamp> _ </timestamp>
        <extraData> _ </extraData>
        <mixHash> _ </mixHash>
        <blockNonce> _ </blockNonce>

        <ommerBlockHeaders> _ </ommerBlockHeaders>
        <blockhash> _ </blockhash>
      </evm>

      <network>
        <activeAccounts> ACCT_ID |-> false /* _ */ </activeAccounts>

        <accounts>
          <account>
            <acctID> ACCT_ID </acctID>
            <balance> _ </balance>
            <code>
		%HKG_ProgramBytes
            </code>
            <storage>
	    keccak(int2wordstack(O, 32) ++ #padToWidth(32, #asByteStack(1))) |-> B:Int
              _:Map
            </storage>
            <nonce> _ </nonce>
          </account>
          /* _ */
        </accounts>

        <txOrder> _ </txOrder>
        <txPending> _ </txPending>
        <messages> /* _ */ .Bag </messages>
      </network>
    </ethereum>
    requires 0 <=Int ACCT_ID   andBool ACCT_ID   <Int (2 ^Int 160)
     andBool 0 <=Int CALLER_ID andBool CALLER_ID <Int (2 ^Int 160)
     andBool 0 <=Int ORIGIN_ID andBool ORIGIN_ID <Int (2 ^Int 160)
     andBool F ==Int 1889567281 // TODO: auto gen
     andBool 0 <=Int O andBool O <Int (2 ^Int 160)
     andBool 0 <=Int B andBool B <Int (2 ^Int 256)
   //andBool G >Int 20000

endmodule
```
