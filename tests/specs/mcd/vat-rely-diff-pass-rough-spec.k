requires "verification.k"

module VAT-RELY-DIFF-PASS-ROUGH-SPEC
    imports VERIFICATION

    // Vat_rely-diff
    claim [Vat.rely-diff.pass.rough]:
      <k> #execute ~> CONTINUATION => #halt ~> CONTINUATION </k>
      <exit-code> 1 </exit-code>
      <mode> NORMAL </mode>
      <schedule> ISTANBUL </schedule>
      <ethereum>
        <evm>
          <output> .ByteArray </output>
          <statusCode> _ => EVMC_SUCCESS </statusCode>
          <endPC> _ => ?_ </endPC>
          <callStack> VCallStack </callStack>
          <interimStates> _ </interimStates>
          <touchedAccounts> _ => ?_ </touchedAccounts>
          <callState>
            <program> Vat_bin_runtime </program>
            <jumpDests> #computeValidJumpDests(Vat_bin_runtime) </jumpDests>
            <id> ACCT_ID </id>
            <caller> CALLER_ID </caller>
            <callData> #abiCallData("rely", #address(ABI_usr)) ++ CD => ?_ </callData>
            <callValue> VCallValue </callValue>
            <wordStack> .WordStack => ?_ </wordStack>
            <localMem> .Memory => ?_ </localMem>
            <pc> 0 => ?_ </pc>
            <gas> #gas(VGas) => ?_ </gas>
            <memoryUsed> 0 => ?_ </memoryUsed>
            <callGas> _ => ?_ </callGas>
            <static> false </static>
            <callDepth> VCallDepth </callDepth>
          </callState>
          <substate>
            <selfDestruct> VSelfDestruct </selfDestruct>
            <log> _ => ?_ </log>
            <refund> Vrefund => ?_ </refund>
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
            <number> BLOCK_NUMBER </number>
            <gasLimit> _ </gasLimit>
            <gasUsed> _ </gasUsed>
            <timestamp> TIME </timestamp>
            <extraData> _ </extraData>
            <mixHash> _ </mixHash>
            <blockNonce> _ </blockNonce>
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
              <code> Vat_bin_runtime </code>
              <storage> ACCT_ID_STORAGE => ACCT_ID_STORAGE [ #Vat.wards[ABI_usr] <- 1 ] </storage>
              <origStorage> ACCT_ID_ORIG_STORAGE </origStorage>
              <nonce> Nonce_Vat => ?_ </nonce>
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

     andBool (#rangeAddress(ABI_usr)
     andBool (#rangeUInt(256, May)
     andBool (#rangeUInt(256, Live)
     andBool ((#sizeByteArray(CD) <=Int 1250000000)
     andBool ((CALLER_ID =/=Int ABI_usr)
     andBool (#rangeUInt(256, Junk_0)
     andBool (#rangeUInt(256, Junk_1)
     andBool (#rangeUInt(256, Junk_2)
     andBool (#rangeUInt(256, Junk_3)
     andBool ((May ==Int 1)
     andBool ((Live ==Int 1)
     andBool ((VCallValue ==Int 0)))))))))))))

     andBool #lookup(ACCT_ID_STORAGE, #Vat.wards[CALLER_ID]) ==Int May
     andBool #lookup(ACCT_ID_STORAGE, #Vat.wards[ABI_usr]) ==Int Junk_0
     andBool #lookup(ACCT_ID_STORAGE, #Vat.live) ==Int Live
     andBool #lookup(ACCT_ID_ORIG_STORAGE, #Vat.wards[CALLER_ID]) ==Int Junk_1
     andBool #lookup(ACCT_ID_ORIG_STORAGE, #Vat.wards[ABI_usr]) ==Int Junk_2
     andBool #lookup(ACCT_ID_ORIG_STORAGE, #Vat.live) ==Int Junk_3
     andBool #Vat.wards[CALLER_ID] =/=Int #Vat.wards[ABI_usr]
     andBool #Vat.wards[CALLER_ID] =/=Int #Vat.live
     andBool #Vat.wards[ABI_usr] =/=Int #Vat.live

endmodule
