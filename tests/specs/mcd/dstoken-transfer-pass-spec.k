requires "verification.k"

module DSTOKEN-TRANSFER-SPEC
    imports VERIFICATION

    claim [DSToken.transfer.pass]:
      <k> #execute ~> CONTINUATION => #halt ~> CONTINUATION </k>
      <exit-code> 1 </exit-code>
      <mode> NORMAL </mode>
      <schedule> ISTANBUL </schedule>
      <ethereum>
        <evm>
          <output> _ => #buf(32, 1) </output>
          <statusCode> _ => EVMC_SUCCESS </statusCode>
          <callStack> _VCallStack </callStack>
          <interimStates> _ </interimStates>
          <touchedAccounts> _ => ?_ </touchedAccounts>
          <callState>
            <program> DSToken_bin_runtime </program>
            <jumpDests> #computeValidJumpDests(DSToken_bin_runtime) </jumpDests>
            <id> ACCT_ID </id>
            <caller> CALLER_ID </caller>
            <callData> #abiCallData("transfer", #address(ABI_usr), #uint256(ABI_wad)) +Bytes CD => ?_ </callData>
            <callValue> VCallValue </callValue>
            <wordStack> .WordStack => ?_ </wordStack>
            <localMem> .Bytes => ?_ </localMem>
            <pc> 0 => ?_ </pc>
            <gas> #gas(VGas) => #gas ( ( ( ( VGas -Int Csstore( ISTANBUL , ( Gem_c -Int ABI_wad ) , Gem_c , Junk_0 ) ) -Int Csstore( ISTANBUL , ( Gem_u +Int ABI_wad ) , Gem_u , Junk_1 ) ) +Int -6391 ) ) </gas>
            <memoryUsed> 0 => ?_ </memoryUsed>
            <callGas> _ => ?_ </callGas>
            <static> false </static>
            <callDepth> VCallDepth </callDepth>
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
            <withdrawalsRoot> _ </withdrawalsRoot>
          </block>
        </evm>
        <network>
          <chainID> VChainId </chainID>
          <accounts>
            <account>
              <acctID> ACCT_ID </acctID>
              <balance> ACCT_ID_balance </balance>
              <code> DSToken_bin_runtime </code>
              <storage> ACCT_ID_STORAGE => ACCT_ID_STORAGE [ #DSToken.balances[CALLER_ID] <- Gem_c -Int ABI_wad ] [ #DSToken.balances[ABI_usr] <- Gem_u +Int ABI_wad ] </storage>
              <origStorage> ACCT_ID_ORIG_STORAGE </origStorage>
              <nonce> Nonce_DSToken </nonce>
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
       andBool #rangeNonce(Nonce_DSToken)

       andBool (#rangeAddress(ABI_usr)
       andBool (#rangeUInt(256, ABI_wad)
       andBool (#rangeUInt(256, Gem_c)
       andBool (#rangeUInt(256, Gem_u)
       andBool (#rangeAddress(Owner)
       andBool (#rangeBool(Stopped)
       andBool ((lengthBytes(CD) <=Int 1250000000)
       andBool ((#notPrecompileAddress(Owner))
       andBool ((ABI_usr =/=Int CALLER_ID)
       andBool (#rangeUInt(256, Junk_0)
       andBool (#rangeUInt(256, Junk_1)
       andBool (#rangeUInt(256, Junk_2)
       andBool (((#rangeUInt(256, Gem_c -Int ABI_wad)))
       andBool (((#rangeUInt(256, Gem_u +Int ABI_wad)))
       andBool ((Stopped ==Int 0)
       andBool ((VCallValue ==Int 0)))))))))))))))))

       andBool #lookup(ACCT_ID_STORAGE, #DSToken.balances[CALLER_ID]) ==Int Gem_c
       andBool #lookup(ACCT_ID_STORAGE, #DSToken.balances[ABI_usr]) ==Int Gem_u
       andBool #lookup(ACCT_ID_STORAGE, #DSToken.owner_stopped) ==Int #WordPackAddrUInt8(Owner, Stopped)
       andBool #lookup(ACCT_ID_ORIG_STORAGE, #DSToken.balances[CALLER_ID]) ==Int Junk_0
       andBool #lookup(ACCT_ID_ORIG_STORAGE, #DSToken.balances[ABI_usr]) ==Int Junk_1
       andBool #lookup(ACCT_ID_ORIG_STORAGE, #DSToken.owner_stopped) ==Int Junk_2
       andBool #DSToken.balances[CALLER_ID] =/=Int #DSToken.balances[ABI_usr]
       andBool #DSToken.balances[CALLER_ID] =/=Int #DSToken.owner_stopped
       andBool #DSToken.balances[ABI_usr] =/=Int #DSToken.owner_stopped

endmodule
