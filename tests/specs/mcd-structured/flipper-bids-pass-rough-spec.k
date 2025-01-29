requires "verification.k"

module FLIPPER-BIDS-PASS-ROUGH-SPEC
    imports VERIFICATION

    // Flipper_bids
    claim [Flipper.bids.pass.rough]:
      <k> #execute ~> CONTINUATION => #halt ~> CONTINUATION </k>
      <mode> NORMAL </mode>
      <schedule> ISTANBUL </schedule>
      <useGas> true </useGas>
      <ethereum>
        <evm>
          <output> _ => #buf(32, Bid) +Bytes #buf(32, Lot) +Bytes #buf(32, Guy) +Bytes #buf(32, Tic) +Bytes #buf(32, End) +Bytes #buf(32, Usr) +Bytes #buf(32, Gal) +Bytes #buf(32, Tab) </output>
          <statusCode> _ => EVMC_SUCCESS </statusCode>
          <callStack> _VCallStack </callStack>
          <interimStates> _ </interimStates>
          <touchedAccounts> _ => ?_ </touchedAccounts>
          <callState>
            <program> Flipper_bin_runtime </program>
            <jumpDests> #computeValidJumpDests(Flipper_bin_runtime) </jumpDests>
            <id> ACCT_ID </id>
            <caller> CALLER_ID </caller>
            <callData> #abiCallData("bids", #uint256(ABI_n)) +Bytes CD => ?_ </callData>
            <callValue> VCallValue </callValue>
            <wordStack> .WordStack => ?_ </wordStack>
            <localMem> .Bytes => ?_ </localMem>
            <pc> 0 => ?_ </pc>
            <gas> #gas(VGas) => ?_ </gas>
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
            <createdAccounts> _ => ?_ </createdAccounts>
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
              <code> Flipper_bin_runtime </code>
              <storage>
                (#Flipper.bids[ABI_n].bid |-> Bid)
                (#Flipper.bids[ABI_n].lot |-> Lot)
                (#Flipper.bids[ABI_n].guy_tic_end |-> #WordPackAddrUInt48UInt48(Guy, Tic, End))
                (#Flipper.bids[ABI_n].usr |-> Usr)
                (#Flipper.bids[ABI_n].gal |-> Gal)
                (#Flipper.bids[ABI_n].tab |-> Tab)
                ACCT_ID_STORAGE
              </storage>
              <origStorage> ACCT_ID_ORIG_STORAGE </origStorage>
              <nonce> _Nonce_Flipper => ?_ </nonce>
              <transientStorage> _ </transientStorage>
            </account>
           ...
          </accounts>
          <txOrder> _ </txOrder>
          <txPending> _ </txPending>
          <messages> _ </messages>
          ...
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

       andBool (#rangeUInt(256, ABI_n)
       andBool (#rangeUInt(256, Bid)
       andBool (#rangeUInt(256, Lot)
       andBool (#rangeAddress(Guy)
       andBool (#rangeUInt(48, Tic)
       andBool (#rangeUInt(48, End)
       andBool (#rangeAddress(Usr)
       andBool (#rangeAddress(Gal)
       andBool (#rangeUInt(256, Tab)
       andBool (lengthBytes(CD) <=Int 1250000000
       andBool (#notPrecompileAddress(Guy)
       andBool (#notPrecompileAddress(Usr)
       andBool (#notPrecompileAddress(Gal)
       andBool ((VCallValue ==Int 0)))))))))))))))

endmodule
