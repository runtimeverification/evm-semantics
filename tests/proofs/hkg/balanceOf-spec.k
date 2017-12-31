// HKG Token - Full Proof Claims
// =============================

// We now present reachability claims used for verification, one for each function in the ERC20 specification.
// Since the HKG token contract contains only sequential code (no loops), we only need one reachability claim per branch per function.
// In the following claims, any symbol starting with a `%` indicates a constant which has been replaced by a symbol for clarity.
// In particular:

// -   `%HKG_Program` is the EVM bytecode for the ERC20-complaint Program;
// -   `VALUE` represents the symbolic amount to transfer;
// -   `BAL_FROM` and `BAL_TO` are the starting balances of accounts CALLER\_ID and TO\_ID, respectively;

// BalanceOf Function
// ------------------

// Here we provide a specification file containing a reachability rule for the verifying the correctness of the HKG Token's BalanceOf Function.


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

