requires "end-arithmetic-spec.k"
requires "vat-move-diff-pass-spec.k"

module END-PACK-PASS-ROUGH-SPEC
    imports END-ARITHMETIC-SPEC
    imports VAT-MOVE-DIFF-PASS-SPEC

    claim [End.pack.pass.rough]:
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
            <program> End_bin_runtime </program>
            <jumpDests> #computeValidJumpDests(End_bin_runtime) </jumpDests>
            <id> ACCT_ID </id>
            <caller> CALLER_ID </caller>
            <callData> #abiCallData("pack", #uint256(ABI_wad)) +Bytes CD => ?_ </callData>
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
              <code> End_bin_runtime </code>
              <storage> ACCT_ID_STORAGE => ACCT_ID_STORAGE [ #End.bag[CALLER_ID] <- Bag +Int ABI_wad ] </storage>
              <origStorage> ACCT_ID_ORIG_STORAGE </origStorage>
              <nonce> Nonce_End </nonce>
            </account>
            <account>
              <acctID> Vat </acctID>
              <balance> Vat_balance </balance>
              <code> Vat_bin_runtime </code>
              <storage> Vat_STORAGE => Vat_STORAGE [ #Vat.dai[CALLER_ID] <- Dai -Int ABI_wad *Int #Ray ] [ #Vat.dai[Vow] <- Joy +Int ABI_wad *Int #Ray ] </storage>
              <origStorage> Vat_ORIG_STORAGE </origStorage>
              <nonce> Nonce_Vat </nonce>
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
       andBool #rangeNonce(Nonce_End)
       andBool #rangeNonce(Nonce_Vat)

       andBool (#rangeUInt(256, ABI_wad)
       andBool (#rangeAddress(Vat)
       andBool (#rangeAddress(Vow)
       andBool (#rangeUInt(256, Debt)
       andBool (#rangeUInt(256, Bag)
       andBool (#rangeUInt(256, Joy)
       andBool (#rangeUInt(256, Dai)
       andBool (#rangeUInt(256, Can)
       andBool (#rangeUInt(256, Vat_balance)
       andBool ((lengthBytes(CD) <=Int 1250000000)
       andBool ((#notPrecompileAddress(Vat))
       andBool ((#notPrecompileAddress(Vow))
       andBool ((ACCT_ID =/=Int Vat)
       andBool ((CALLER_ID =/=Int Vow)
       andBool ((CALLER_ID =/=Int ACCT_ID)
       andBool ((Vat =/=Int 0)
       andBool (#rangeUInt(256, Junk_0)
       andBool (#rangeUInt(256, Junk_1)
       andBool (#rangeUInt(256, Junk_2)
       andBool (#rangeUInt(256, Junk_3)
       andBool (#rangeUInt(256, Junk_4)
       andBool (#rangeUInt(256, Junk_5)
       andBool (#rangeUInt(256, Junk_6)
       andBool (((Debt =/=Int 0))
       andBool (((Can  ==Int 1))
       andBool (((VCallValue ==Int 0))
       andBool (((VCallDepth <Int 1024))
       andBool ((#rangeUInt(256, Bag +Int ABI_wad))
       andBool ((#rangeUInt(256, ABI_wad *Int #Ray))
       andBool ((#rangeUInt(256, Dai -Int (ABI_wad *Int #Ray)))
       andBool ((#rangeUInt(256, Joy +Int (ABI_wad *Int #Ray))))))))))))))))))))))))))))))))))

       andBool #lookup(ACCT_ID_STORAGE, #End.vat) ==Int Vat
       andBool #lookup(ACCT_ID_STORAGE, #End.vow) ==Int Vow
       andBool #lookup(ACCT_ID_STORAGE, #End.debt) ==Int Debt
       andBool #lookup(ACCT_ID_STORAGE, #End.bag[CALLER_ID]) ==Int Bag
       andBool #lookup(ACCT_ID_ORIG_STORAGE, #End.vat) ==Int Junk_0
       andBool #lookup(ACCT_ID_ORIG_STORAGE, #End.vow) ==Int Junk_1
       andBool #lookup(ACCT_ID_ORIG_STORAGE, #End.debt) ==Int Junk_2
       andBool #lookup(ACCT_ID_ORIG_STORAGE, #End.bag[CALLER_ID]) ==Int Junk_3
       andBool #End.vat =/=Int #End.vow
       andBool #End.vat =/=Int #End.debt
       andBool #End.vat =/=Int #End.bag[CALLER_ID]
       andBool #End.vow =/=Int #End.debt
       andBool #End.vow =/=Int #End.bag[CALLER_ID]
       andBool #End.debt =/=Int #End.bag[CALLER_ID]
       andBool #lookup(Vat_STORAGE, #Vat.can[CALLER_ID][ACCT_ID]) ==Int Can
       andBool #lookup(Vat_STORAGE, #Vat.dai[CALLER_ID]) ==Int Dai
       andBool #lookup(Vat_STORAGE, #Vat.dai[Vow]) ==Int Joy
       andBool #lookup(Vat_ORIG_STORAGE, #Vat.can[CALLER_ID][ACCT_ID]) ==Int Junk_4
       andBool #lookup(Vat_ORIG_STORAGE, #Vat.dai[CALLER_ID]) ==Int Junk_5
       andBool #lookup(Vat_ORIG_STORAGE, #Vat.dai[Vow]) ==Int Junk_6
       andBool #Vat.can[CALLER_ID][ACCT_ID] =/=Int #Vat.dai[CALLER_ID]
       andBool #Vat.can[CALLER_ID][ACCT_ID] =/=Int #Vat.dai[Vow]
       andBool #Vat.dai[CALLER_ID] =/=Int #Vat.dai[Vow]

    [depends(END-ARITHMETIC-SPEC.End.adduu.pass,END-ARITHMETIC-SPEC.End.muluu.pass,VAT-MOVE-DIFF-PASS-SPEC.Vat.move-diff.pass)]

endmodule
