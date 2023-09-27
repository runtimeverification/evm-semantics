requires "verification.k"
requires "dstoken-transfer-pass-spec.k"
requires "vat-slip-pass-spec.k"

module GEMJOIN-EXIT-PASS-ROUGH-SPEC
    imports VERIFICATION
    imports DSTOKEN-TRANSFER-PASS-SPEC
    imports VAT-SLIP-PASS-SPEC

    claim [GemJoin.exit.pass.rough]:
      <k> #execute ~> CONTINUATION => #halt ~> CONTINUATION </k>
      <exit-code> 1 </exit-code>
      <mode> NORMAL </mode>
      <schedule> ISTANBUL </schedule>
      <ethereum>
        <evm>
          <output> .Bytes </output>
          <statusCode> _ => EVMC_SUCCESS </statusCode>
          <callStack> _VCallStack </callStack>
          <interimStates> _ </interimStates>
          <touchedAccounts> _ => ?_ </touchedAccounts>
          <callState>
            <program> GemJoin_bin_runtime </program>
            <jumpDests> #computeValidJumpDests(GemJoin_bin_runtime) </jumpDests>
            <id> ACCT_ID </id>
            <caller> CALLER_ID </caller>
            <callData> #abiCallData("exit", #address(ABI_usr), #uint256(ABI_wad)) +Bytes CD => ?_ </callData>
            <callValue> VCallValue </callValue>
            <wordStack> .WordStack => ?_ </wordStack>
            <localMem> .Bytes => ?_ </localMem>
            <pc> 0 => ?_ </pc>
            <gas> #gas(VGas) => ?_ </gas>
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
              <code> GemJoin_bin_runtime </code>
              <storage> ACCT_ID_STORAGE => ACCT_ID_STORAGE  </storage>
              <origStorage> ACCT_ID_ORIG_STORAGE </origStorage>
              <nonce> Nonce_GemJoin </nonce>
            </account>
            <account>
              <acctID> Vat </acctID>
              <balance> Vat_balance </balance>
              <code> Vat_bin_runtime </code>
              <storage> Vat_STORAGE => Vat_STORAGE [ #Vat.gem[Ilk][CALLER_ID] <- Wad -Int ABI_wad ] </storage>
              <origStorage> Vat_ORIG_STORAGE </origStorage>
              <nonce> Nonce_Vat </nonce>
            </account>
            <account>
              <acctID> DSToken </acctID>
              <balance> DSToken_balance </balance>
              <code> DSToken_bin_runtime </code>
              <storage> DSToken_STORAGE => DSToken_STORAGE [ #DSToken.balances[ACCT_ID] <- Bal_adapter -Int ABI_wad ] [ #DSToken.balances[ABI_usr] <- Bal_usr     +Int ABI_wad ] </storage>
              <origStorage> DSToken_ORIG_STORAGE </origStorage>
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
       andBool #rangeNonce(Nonce_GemJoin)
       andBool #rangeNonce(Nonce_Vat)
       andBool #rangeNonce(Nonce_DSToken)

       andBool (#rangeAddress(ABI_usr)
       andBool (#rangeUInt(256, ABI_wad)
       andBool (#rangeAddress(Vat)
       andBool (#rangeBytes(32, Ilk)
       andBool (#rangeAddress(DSToken)
       andBool (#rangeUInt(256, May)
       andBool (#rangeUInt(256, Wad)
       andBool (#rangeUInt(256, Bal_usr)
       andBool (#rangeUInt(256, Bal_adapter)
       andBool (#rangeAddress(Owner)
       andBool (#rangeBool(Stopped)
       andBool (#rangeUInt(256, Vat_balance)
       andBool (#rangeUInt(256, DSToken_balance)
       andBool ((lengthBytes(CD) <=Int 1250000000)
       andBool ((#notPrecompileAddress(Vat))
       andBool ((#notPrecompileAddress(DSToken))
       andBool ((#notPrecompileAddress(Owner))
       andBool ((ACCT_ID =/=Int Vat)
       andBool ((ACCT_ID =/=Int DSToken)
       andBool ((ACCT_ID =/=Int ABI_usr)
       andBool ((Vat =/=Int 0)
       andBool ((DSToken =/=Int 0)
       andBool (#rangeUInt(256, Junk_0)
       andBool (#rangeUInt(256, Junk_1)
       andBool (#rangeUInt(256, Junk_2)
       andBool (#rangeUInt(256, Junk_3)
       andBool (#rangeUInt(256, Junk_4)
       andBool (#rangeUInt(256, Junk_5)
       andBool (#rangeUInt(256, Junk_6)
       andBool (#rangeUInt(256, Junk_7)
       andBool (((VCallValue ==Int 0))
       andBool (((VCallDepth <Int 1024))
       andBool (((Stopped ==Int 0))
       andBool (((May ==Int 1))
       andBool (((ABI_wad <=Int pow255))
       andBool ((#rangeUInt(256, Wad         -Int ABI_wad))
       andBool ((#rangeUInt(256, Bal_adapter -Int ABI_wad))
       andBool ((#rangeUInt(256, Bal_usr     +Int ABI_wad))))))))))))))))))))))))))))))))))))))))

       andBool #lookup(ACCT_ID_STORAGE, #GemJoin.vat) ==Int Vat
       andBool #lookup(ACCT_ID_STORAGE, #GemJoin.ilk) ==Int Ilk
       andBool #lookup(ACCT_ID_STORAGE, #GemJoin.gem) ==Int DSToken
       andBool #lookup(ACCT_ID_ORIG_STORAGE, #GemJoin.vat) ==Int Junk_0
       andBool #lookup(ACCT_ID_ORIG_STORAGE, #GemJoin.ilk) ==Int Junk_1
       andBool #lookup(ACCT_ID_ORIG_STORAGE, #GemJoin.gem) ==Int Junk_2
       andBool #GemJoin.vat =/=Int #GemJoin.ilk
       andBool #GemJoin.vat =/=Int #GemJoin.gem
       andBool #GemJoin.ilk =/=Int #GemJoin.gem
       andBool #lookup(Vat_STORAGE, #Vat.wards[ACCT_ID]) ==Int May
       andBool #lookup(Vat_STORAGE, #Vat.gem[Ilk][CALLER_ID]) ==Int Wad
       andBool #lookup(Vat_ORIG_STORAGE, #Vat.wards[ACCT_ID]) ==Int Junk_3
       andBool #lookup(Vat_ORIG_STORAGE, #Vat.gem[Ilk][CALLER_ID]) ==Int Junk_4
       andBool #Vat.wards[ACCT_ID] =/=Int #Vat.gem[Ilk][CALLER_ID]
       andBool #lookup(DSToken_STORAGE, #DSToken.balances[ACCT_ID]) ==Int Bal_adapter
       andBool #lookup(DSToken_STORAGE, #DSToken.balances[ABI_usr]) ==Int Bal_usr
       andBool #lookup(DSToken_STORAGE, #DSToken.owner_stopped) ==Int #WordPackAddrUInt8(Owner, Stopped)
       andBool #lookup(DSToken_ORIG_STORAGE, #DSToken.balances[ACCT_ID]) ==Int Junk_5
       andBool #lookup(DSToken_ORIG_STORAGE, #DSToken.balances[ABI_usr]) ==Int Junk_6
       andBool #lookup(DSToken_ORIG_STORAGE, #DSToken.owner_stopped) ==Int Junk_7
       andBool #DSToken.balances[ACCT_ID] =/=Int #DSToken.balances[ABI_usr]
       andBool #DSToken.balances[ACCT_ID] =/=Int #DSToken.owner_stopped
       andBool #DSToken.balances[ABI_usr] =/=Int #DSToken.owner_stopped

    [depends(DSTOKEN-TRANSFER-PASS-SPEC.DSToken.transfer.pass,VAT-SLIP-PASS-SPEC.Vat.slip.pass)]

endmodule
