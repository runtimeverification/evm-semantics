requires "verification.k"

module VAT-HEAL-PASS-SPEC
    imports VERIFICATION

    claim [Vat.heal.pass]:
      <k> #execute ~> CONTINUATION => #halt ~> CONTINUATION </k>
      <mode> NORMAL </mode>
      <schedule> ISTANBUL </schedule>
      <useGas> true </useGas>
      <ethereum>
        <evm>
          <output> .Bytes </output>
          <statusCode> _ => EVMC_SUCCESS </statusCode>
          <callStack> _VCallStack </callStack>
          <interimStates> _ </interimStates>
          <touchedAccounts> _ => ?_ </touchedAccounts>
          <callState>
            <program> Vat_bin_runtime </program>
            <jumpDests> #computeValidJumpDests(Vat_bin_runtime) </jumpDests>
            <id> ACCT_ID </id>
            <caller> CALLER_ID </caller>
            <callData> #abiCallData("heal", #uint256(ABI_rad)) +Bytes CD => ?_ </callData>
            <callValue> VCallValue </callValue>
            <wordStack> .WordStack => ?WS </wordStack>
            <wordStackSize> 0 => #sizeWordStack(?WS) </wordStackSize>
            <localMem> .Bytes => ?_ </localMem>
            <pc> 0 => ?_ </pc>
            <gas> #gas(VGas) => #gas ( ( ( ( ( ( VGas -Int Csstore( ISTANBUL , ( Sin -Int ABI_rad ) , Sin , Junk_0 ) ) -Int Csstore( ISTANBUL , ( Dai -Int ABI_rad ) , Dai , Junk_1 ) ) -Int Csstore( ISTANBUL , ( Vice -Int ABI_rad ) , Vice , Junk_2 ) ) -Int Csstore( ISTANBUL , ( Debt -Int ABI_rad ) , Debt , Junk_3 ) ) +Int -8616 ) ) </gas>
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
            <blobGasUsed> _ </blobGasUsed>
            <excessBlobGas> _ </excessBlobGas>
            <beaconRoot> _ </beaconRoot>
          </block>
        </evm>
        <network>
          <chainID> VChainId </chainID>
          <accounts>
            <account>
              <acctID> ACCT_ID </acctID>
              <balance> ACCT_ID_balance </balance>
              <code> Vat_bin_runtime </code>
              <storage> ACCT_ID_STORAGE => ACCT_ID_STORAGE [ #Vat.sin[CALLER_ID] <- Sin -Int ABI_rad ] [ #Vat.dai[CALLER_ID] <- Dai -Int ABI_rad ] [ #Vat.vice <- Vice  -Int ABI_rad ] [ #Vat.debt <- Debt  -Int ABI_rad ] </storage>
              <origStorage> ACCT_ID_ORIG_STORAGE </origStorage>
              <nonce> Nonce_Vat </nonce>
              <transientStorage> _ </transientStorage>
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
       andBool #rangeNonce(Nonce_Vat)

       andBool (#rangeUInt(256, ABI_rad)
       andBool (#rangeUInt(256, Dai)
       andBool (#rangeUInt(256, Sin)
       andBool (#rangeUInt(256, Debt)
       andBool (#rangeUInt(256, Vice)
       andBool (lengthBytes(CD) <=Int 1250000000
       andBool (#rangeUInt(256, Junk_0)
       andBool (#rangeUInt(256, Junk_1)
       andBool (#rangeUInt(256, Junk_2)
       andBool (#rangeUInt(256, Junk_3)
       andBool (((VCallValue ==Int 0))
       andBool ((#rangeUInt(256, Dai -Int ABI_rad))
       andBool ((#rangeUInt(256, Sin -Int ABI_rad))
       andBool ((#rangeUInt(256, Debt  -Int ABI_rad))
       andBool ((#rangeUInt(256, Vice  -Int ABI_rad)))))))))))))))))

       andBool #lookup(ACCT_ID_STORAGE, #Vat.sin[CALLER_ID]) ==Int Sin
       andBool #lookup(ACCT_ID_STORAGE, #Vat.dai[CALLER_ID]) ==Int Dai
       andBool #lookup(ACCT_ID_STORAGE, #Vat.vice) ==Int Vice
       andBool #lookup(ACCT_ID_STORAGE, #Vat.debt) ==Int Debt
       andBool #lookup(ACCT_ID_ORIG_STORAGE, #Vat.sin[CALLER_ID]) ==Int Junk_0
       andBool #lookup(ACCT_ID_ORIG_STORAGE, #Vat.dai[CALLER_ID]) ==Int Junk_1
       andBool #lookup(ACCT_ID_ORIG_STORAGE, #Vat.vice) ==Int Junk_2
       andBool #lookup(ACCT_ID_ORIG_STORAGE, #Vat.debt) ==Int Junk_3
       andBool #Vat.sin[CALLER_ID] =/=Int #Vat.dai[CALLER_ID]
       andBool #Vat.sin[CALLER_ID] =/=Int #Vat.vice
       andBool #Vat.sin[CALLER_ID] =/=Int #Vat.debt
       andBool #Vat.dai[CALLER_ID] =/=Int #Vat.vice
       andBool #Vat.dai[CALLER_ID] =/=Int #Vat.debt
       andBool #Vat.vice =/=Int #Vat.debt

endmodule
