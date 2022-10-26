requires "verification.k"

module DSTOKEN-TRANSFERFROM-FAIL-ROUGH-SPEC
    imports VERIFICATION

    // DSToken_transferFrom
    claim [DSToken.transferFrom.fail.rough]:
      <k> #execute ~> CONTINUATION => #halt ~> CONTINUATION </k>
      <exit-code> 1 </exit-code>
      <mode> NORMAL </mode>
      <schedule> ISTANBUL </schedule>
      <ethereum>
        <evm>
          <output> _ => ?_ </output>
          <statusCode> _ => ?FAILURE:EndStatusCode </statusCode>
          <callStack> _VCallStack </callStack>
          <interimStates> _ </interimStates>
          <touchedAccounts> _ => ?_ </touchedAccounts>
          <callState>
            <program> DSToken_bin_runtime </program>
            <jumpDests> #computeValidJumpDests(DSToken_bin_runtime) </jumpDests>
            <id> ACCT_ID </id>
            <caller> CALLER_ID </caller>
            <callData> #abiCallData("transferFrom", #address(ABI_src), #address(ABI_dst), #uint256(ABI_wad)) ++ CD => ?_ </callData>
            <callValue> VCallValue </callValue>
            <wordStack> .WordStack => ?_ </wordStack>
            <localMem> .Memory => ?_ </localMem>
            <pc> 0 => ?_ </pc>
            <gas> #gas(VGas) => ?_ </gas>
            <memoryUsed> 0 => ?_ </memoryUsed>
            <callGas> _ => ?_ </callGas>
            <static> false </static>
            <callDepth> VCallDepth => ?_ </callDepth>
          </callState>
          <substate>
            <selfDestruct> _VSelfDestruct </selfDestruct>
            <log> _ => ?_ </log>
            <refund> _Vrefund => ?_ </refund>
            <accessedAccounts> _ => ?_ </accessedAccounts>
            <accessedStorage> _ => ?_ </accessedStorage>
          </substate>
          <gasPrice> _ </gasPrice>
          <origin> ORIGIN_ID </origin>
          <blockhashes> _ </blockhashes>
          <block>
            <previousHash> _ </previousHash>
            <ommersHash> _ </ommersHash>
            <coinbase> _ </coinbase>
            <stateRoot> _ </stateRoot>
            <transactionsRoot> _ </transactionsRoot>
            <receiptsRoot> _ </receiptsRoot>
            <logsBloom> _ </logsBloom>
            <difficulty> _ </difficulty>
            <number> _BLOCK_NUMBER </number>
            <gasLimit> _ </gasLimit>
            <gasUsed> _ </gasUsed>
            <timestamp> TIME </timestamp>
            <extraData> _ </extraData>
            <mixHash> _ </mixHash>
            <blockNonce> _ </blockNonce>
            <baseFee> _ </baseFee>
            <ommerBlockHeaders> _ </ommerBlockHeaders>
          </block>
        </evm>
        <network>
          <chainID> VChainId </chainID>
          <activeAccounts> SetItem(ACCT_ID) _ </activeAccounts>
          <accounts>
            <account>
              <acctID> ACCT_ID </acctID>
              <balance> ACCT_ID_balance </balance>
              <code> DSToken_bin_runtime </code>
              <storage> ACCT_ID_STORAGE => ?_ACCT_ID_STORAGE </storage>
              <origStorage> ACCT_ID_ORIG_STORAGE </origStorage>
              <nonce> _Nonce_DSToken => ?_ </nonce>
            </account>
           ...
          </accounts>
          <txOrder> _ </txOrder>
          <txPending> _ </txPending>
          <messages> _ </messages>
        </network>
      </ethereum>
      requires #rangeAddress(ACCT_ID)
       andBool ACCT_ID =/=Int 0
       andBool #notPrecompileAddress(ACCT_ID)
       andBool #rangeAddress(CALLER_ID)
       andBool #rangeAddress(ORIGIN_ID)
       andBool #rangeUInt(256, TIME)
       andBool #rangeUInt(256, ACCT_ID_balance)
       andBool VCallDepth <=Int 1024
       andBool #rangeUInt(256, VCallValue)
       andBool #rangeUInt(256, VChainId)

       andBool (#rangeAddress(ABI_src)
       andBool (#rangeAddress(ABI_dst)
       andBool (#rangeUInt(256, ABI_wad)
       andBool (#rangeUInt(256, Gem_s)
       andBool (#rangeUInt(256, Gem_d)
       andBool (#rangeUInt(256, Allowance)
       andBool (#rangeAddress(Owner)
       andBool (#rangeBool(Stopped)
       andBool ((#sizeByteArray(CD) <=Int 1250000000)
       andBool ((#notPrecompileAddress(Owner))
       andBool ((ABI_src =/=Int ABI_dst)
       andBool (#rangeUInt(256, Junk_0)
       andBool (#rangeUInt(256, Junk_1)
       andBool (#rangeUInt(256, Junk_2)
       andBool (#rangeUInt(256, Junk_3))))))))))))))))

       andBool #lookup(ACCT_ID_STORAGE, #DSToken.allowance[ABI_src][CALLER_ID]) ==Int Allowance
       andBool #lookup(ACCT_ID_STORAGE, #DSToken.balances[ABI_src]) ==Int Gem_s
       andBool #lookup(ACCT_ID_STORAGE, #DSToken.balances[ABI_dst]) ==Int Gem_d
       andBool #lookup(ACCT_ID_STORAGE, #DSToken.owner_stopped) ==Int #WordPackAddrUInt8(Owner, Stopped)
       andBool #lookup(ACCT_ID_ORIG_STORAGE, #DSToken.allowance[ABI_src][CALLER_ID]) ==Int Junk_0
       andBool #lookup(ACCT_ID_ORIG_STORAGE, #DSToken.balances[ABI_src]) ==Int Junk_1
       andBool #lookup(ACCT_ID_ORIG_STORAGE, #DSToken.balances[ABI_dst]) ==Int Junk_2
       andBool #lookup(ACCT_ID_ORIG_STORAGE, #DSToken.owner_stopped) ==Int Junk_3
       andBool #DSToken.allowance[ABI_src][CALLER_ID] =/=Int #DSToken.balances[ABI_src]
       andBool #DSToken.allowance[ABI_src][CALLER_ID] =/=Int #DSToken.balances[ABI_dst]
       andBool #DSToken.allowance[ABI_src][CALLER_ID] =/=Int #DSToken.owner_stopped
       andBool #DSToken.balances[ABI_src] =/=Int #DSToken.balances[ABI_dst]
       andBool #DSToken.balances[ABI_src] =/=Int #DSToken.owner_stopped
       andBool #DSToken.balances[ABI_dst] =/=Int #DSToken.owner_stopped
       andBool notBool (
        (((#rangeUInt(256, Gem_s:Int -Int ABI_wad:Int)))
        andBool (((#rangeUInt(256, Gem_d:Int +Int ABI_wad:Int)))
        andBool (((Allowance:Int ==Int maxUInt256 orBool ABI_src:Int ==Int CALLER_ID:Int) orBool (ABI_wad:Int <=Int Allowance:Int))
        andBool ((VCallValue:Int ==Int 0)
        andBool ((Stopped:Int ==Int 0))))))
      )
       ensures
    ?FAILURE =/=K EVMC_SUCCESS

endmodule
