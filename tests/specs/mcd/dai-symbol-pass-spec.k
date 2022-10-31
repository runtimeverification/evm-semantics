requires "verification.k"

module DAI-SYMBOL-PASS-SPEC
    imports VERIFICATION

    // Dai_symbol
    claim [Dai.symbol.pass]:
      <k> #execute ~> CONTINUATION => #halt ~> CONTINUATION </k>
      <exit-code> 1 </exit-code>
      <mode> NORMAL </mode>
      <schedule> ISTANBUL </schedule>
      <ethereum>
        <evm>
          <output> _ => #asByteStackInWidthaux(32, 31, 32, #enc(#string("DAI"))) </output>
          <statusCode> _ => EVMC_SUCCESS </statusCode>
          <callStack> _VCallStack </callStack>
          <interimStates> _ </interimStates>
          <touchedAccounts> _ => ?_ </touchedAccounts>
          <callState>
            <program> Dai_bin_runtime </program>
            <jumpDests> #computeValidJumpDests(Dai_bin_runtime) </jumpDests>
            <id> ACCT_ID </id>
            <caller> CALLER_ID </caller>
            <callData> #abiCallData("symbol", .TypedArgs) ++ CD => ?_ </callData>
            <callValue> VCallValue </callValue>
            <wordStack> .WordStack => ?_ </wordStack>
            <localMem> .Memory => ?_ </localMem>
            <pc> 0 => ?_ </pc>
            <gas> #gas(VGas) => #gas ( ( VGas +Int -672 ) ) </gas>
            <memoryUsed> 0 => ?_ </memoryUsed>
            <callGas> _ => ?_ </callGas>
            <static> _ </static>
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
          </block>
        </evm>
        <network>
          <chainID> VChainId </chainID>
          <activeAccounts> SetItem(ACCT_ID) _ </activeAccounts>
          <accounts>
            <account>
              <acctID> ACCT_ID </acctID>
              <balance> ACCT_ID_balance </balance>
              <code> Dai_bin_runtime </code>
              <storage> ACCT_ID_STORAGE => ACCT_ID_STORAGE  </storage>
              <origStorage> ACCT_ID_ORIG_STORAGE </origStorage>
              <nonce> _Nonce_Dai => ?_ </nonce>
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

       andBool (#sizeByteArray(CD) <=Int 1250000000
       andBool ((VCallValue ==Int 0)))



endmodule
