requires "verification.k"

module FLIPPER-BIDS-PASS-ROUGH-SPEC
    imports VERIFICATION

    // Flipper_bids
    claim [Flipper.bids.pass.rough]:
      <k> #execute ~> CONTINUATION => #halt ~> CONTINUATION </k>
      <exit-code> 1 </exit-code>
      <mode> NORMAL </mode>
      <schedule> ISTANBUL </schedule>
      <ethereum>
        <evm>
          <output> _ => #buf(32, Bid) ++ #buf(32, Lot) ++ #buf(32, Guy) ++ #buf(32, Tic) ++ #buf(32, End) ++ #buf(32, Usr) ++ #buf(32, Gal) ++ #buf(32, Tab) </output>
          <statusCode> _ => EVMC_SUCCESS </statusCode>
          <callStack> _VCallStack </callStack>
          <interimStates> _ </interimStates>
          <touchedAccounts> _ => ?_ </touchedAccounts>
          <callState>
            <program> Flipper_bin_runtime </program>
            <jumpDests> #computeValidJumpDests(Flipper_bin_runtime) </jumpDests>
            <id> ACCT_ID </id>
            <caller> CALLER_ID </caller>
            <callData> #abiCallData("bids", #uint256(ABI_n)) ++ CD => ?_ </callData>
            <callValue> VCallValue </callValue>
            <wordStack> .WordStack => ?_ </wordStack>
            <localMem> .Memory => ?_ </localMem>
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
              <code> Flipper_bin_runtime </code>
              <storage> ACCT_ID_STORAGE => ACCT_ID_STORAGE  </storage>
              <origStorage> ACCT_ID_ORIG_STORAGE </origStorage>
              <nonce> _Nonce_Flipper => ?_ </nonce>
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

       andBool (#rangeUInt(256, ABI_n)
       andBool (#rangeUInt(256, Bid)
       andBool (#rangeUInt(256, Lot)
       andBool (#rangeAddress(Guy)
       andBool (#rangeUInt(48, Tic)
       andBool (#rangeUInt(48, End)
       andBool (#rangeAddress(Usr)
       andBool (#rangeAddress(Gal)
       andBool (#rangeUInt(256, Tab)
       andBool (#sizeByteArray(CD) <=Int 1250000000
       andBool (#notPrecompileAddress(Guy)
       andBool (#notPrecompileAddress(Usr)
       andBool (#notPrecompileAddress(Gal)
       andBool (#rangeUInt(256, Junk_0)
       andBool (#rangeUInt(256, Junk_1)
       andBool (#rangeUInt(256, Junk_2)
       andBool (#rangeUInt(256, Junk_3)
       andBool (#rangeUInt(256, Junk_4)
       andBool (#rangeUInt(256, Junk_5)
       andBool ((VCallValue ==Int 0)))))))))))))))))))))

       andBool #lookup(ACCT_ID_STORAGE, #Flipper.bids[ABI_n].bid) ==Int Bid
       andBool #lookup(ACCT_ID_STORAGE, #Flipper.bids[ABI_n].lot) ==Int Lot
       andBool #lookup(ACCT_ID_STORAGE, #Flipper.bids[ABI_n].guy_tic_end) ==Int #WordPackAddrUInt48UInt48(Guy, Tic, End)
       andBool #lookup(ACCT_ID_STORAGE, #Flipper.bids[ABI_n].usr) ==Int Usr
       andBool #lookup(ACCT_ID_STORAGE, #Flipper.bids[ABI_n].gal) ==Int Gal
       andBool #lookup(ACCT_ID_STORAGE, #Flipper.bids[ABI_n].tab) ==Int Tab
       andBool #lookup(ACCT_ID_ORIG_STORAGE, #Flipper.bids[ABI_n].bid) ==Int Junk_0
       andBool #lookup(ACCT_ID_ORIG_STORAGE, #Flipper.bids[ABI_n].lot) ==Int Junk_1
       andBool #lookup(ACCT_ID_ORIG_STORAGE, #Flipper.bids[ABI_n].guy_tic_end) ==Int Junk_2
       andBool #lookup(ACCT_ID_ORIG_STORAGE, #Flipper.bids[ABI_n].usr) ==Int Junk_3
       andBool #lookup(ACCT_ID_ORIG_STORAGE, #Flipper.bids[ABI_n].gal) ==Int Junk_4
       andBool #lookup(ACCT_ID_ORIG_STORAGE, #Flipper.bids[ABI_n].tab) ==Int Junk_5
       andBool #Flipper.bids[ABI_n].bid =/=Int #Flipper.bids[ABI_n].lot
       andBool #Flipper.bids[ABI_n].bid =/=Int #Flipper.bids[ABI_n].guy_tic_end
       andBool #Flipper.bids[ABI_n].bid =/=Int #Flipper.bids[ABI_n].usr
       andBool #Flipper.bids[ABI_n].bid =/=Int #Flipper.bids[ABI_n].gal
       andBool #Flipper.bids[ABI_n].bid =/=Int #Flipper.bids[ABI_n].tab
       andBool #Flipper.bids[ABI_n].lot =/=Int #Flipper.bids[ABI_n].guy_tic_end
       andBool #Flipper.bids[ABI_n].lot =/=Int #Flipper.bids[ABI_n].usr
       andBool #Flipper.bids[ABI_n].lot =/=Int #Flipper.bids[ABI_n].gal
       andBool #Flipper.bids[ABI_n].lot =/=Int #Flipper.bids[ABI_n].tab
       andBool #Flipper.bids[ABI_n].guy_tic_end =/=Int #Flipper.bids[ABI_n].usr
       andBool #Flipper.bids[ABI_n].guy_tic_end =/=Int #Flipper.bids[ABI_n].gal
       andBool #Flipper.bids[ABI_n].guy_tic_end =/=Int #Flipper.bids[ABI_n].tab
       andBool #Flipper.bids[ABI_n].usr =/=Int #Flipper.bids[ABI_n].gal
       andBool #Flipper.bids[ABI_n].usr =/=Int #Flipper.bids[ABI_n].tab
       andBool #Flipper.bids[ABI_n].gal =/=Int #Flipper.bids[ABI_n].tab

endmodule
