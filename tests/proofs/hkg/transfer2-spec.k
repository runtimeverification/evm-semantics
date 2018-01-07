// HKG Token - Full Proof Claims
// =============================

// We now present reachability claims used for verification, one for each function in the ERC20 specification.
// Since the HKG token contract contains only sequential code (no loops), we only need one reachability claim per branch per function.
// In the following claims, any symbol starting with a `%` indicates a constant which has been replaced by a symbol for clarity.
// In particular:

// -   `%HKG_Program` is the EVM bytecode for the ERC20-complaint Program;
// -   `VALUE` represents the symbolic amount to transfer;
// -   `BAL_FROM` and `BAL_TO` are the starting balances of accounts CALLER\_ID and TO\_ID, respectively;

// Transfer Function
// -----------------

// -   When "to" address is the same as calling address, total amount should remained unchanged.


module TRANSFER2-SPEC
  imports ETHEREUM-SIMULATION

  rule
    <k>         #execute => (RETURN RET_ADDR:Int 31 ~> _) </k>
    <exit-code> 0                                         </exit-code>
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

