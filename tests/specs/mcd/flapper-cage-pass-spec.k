requires "verification.k"

module FLAPPER-CAGE-PASS-SPEC
    imports VERIFICATION

    claim [Flapper.cage.pass]:
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
            <program> Flapper_bin_runtime </program>
            <jumpDests> #computeValidJumpDests(Flapper_bin_runtime) </jumpDests>
            <id> ACCT_ID </id>
            <caller> CALLER_ID </caller>
            <callData> #abiCallData("cage", #uint256(ABI_rad)) +Bytes CD => ?_ </callData>
            <callValue> VCallValue </callValue>
            <wordStack> .WordStack => ?_ </wordStack>
            <localMem> .Bytes => ?_ </localMem>
            <pc> 0 => ?_ </pc>
            <gas> #gas(VGas) => #gas ( ( ( ( ( VGas -Int Csstore( ISTANBUL , 0 , Live , Junk_2 ) ) -Int Csstore( ISTANBUL , ( Dai_a -Int ABI_rad ) , Dai_a , Junk_5 ) ) -Int Csstore( ISTANBUL , ( Dai_u +Int ABI_rad ) , Dai_u , Junk_6 ) ) +Int -15964 ) ) </gas>
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
              <code> Flapper_bin_runtime </code>
              <storage> ACCT_ID_STORAGE => ACCT_ID_STORAGE [ #Flapper.live <- 0 ] </storage>
              <origStorage> ACCT_ID_ORIG_STORAGE </origStorage>
              <nonce> Nonce_Flapper </nonce>
            </account>
            <account>
              <acctID> Vat </acctID>
              <balance> Vat_balance </balance>
              <code> Vat_bin_runtime </code>
              <storage> Vat_STORAGE => Vat_STORAGE [ #Vat.dai[ACCT_ID] <- Dai_a -Int ABI_rad ] [ #Vat.dai[CALLER_ID] <- Dai_u +Int ABI_rad ] </storage>
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
       andBool #rangeNonce(Nonce_Flapper)
       andBool #rangeNonce(Nonce_Vat)

       andBool (#rangeUInt(256, ABI_rad)
       andBool (#rangeAddress(Vat)
       andBool (#rangeUInt(256, Ward)
       andBool (#rangeUInt(256, Live)
       andBool (#rangeUInt(256, Dai_a)
       andBool (#rangeUInt(256, Dai_u)
       andBool (#rangeUInt(256, Vat_balance)
       andBool ((lengthBytes(CD) <=Int 1250000000)
       andBool ((#notPrecompileAddress(Vat))
       andBool ((CALLER_ID =/=Int ACCT_ID)
       andBool (ACCT_ID =/=Int Vat
       andBool ((Vat =/=Int 0)
       andBool (#rangeUInt(256, Junk_0)
       andBool (#rangeUInt(256, Junk_1)
       andBool (#rangeUInt(256, Junk_2)
       andBool (#rangeUInt(256, Junk_3)
       andBool (#rangeUInt(256, Junk_4)
       andBool (#rangeUInt(256, Junk_5)
       andBool (#rangeUInt(256, Junk_6)
       andBool (((Ward ==Int 1))
       andBool (((VCallDepth <Int 1024))
       andBool (((VCallValue ==Int 0))
       andBool ((#rangeUInt(256, Dai_a -Int ABI_rad))
       andBool ((#rangeUInt(256, Dai_u +Int ABI_rad))))))))))))))))))))))))))

       andBool #lookup(ACCT_ID_STORAGE, #Flapper.wards[CALLER_ID]) ==Int Ward
       andBool #lookup(ACCT_ID_STORAGE, #Flapper.vat) ==Int Vat
       andBool #lookup(ACCT_ID_STORAGE, #Flapper.live) ==Int Live
       andBool #lookup(ACCT_ID_ORIG_STORAGE, #Flapper.wards[CALLER_ID]) ==Int Junk_0
       andBool #lookup(ACCT_ID_ORIG_STORAGE, #Flapper.vat) ==Int Junk_1
       andBool #lookup(ACCT_ID_ORIG_STORAGE, #Flapper.live) ==Int Junk_2
       andBool #Flapper.wards[CALLER_ID] =/=Int #Flapper.vat
       andBool #Flapper.wards[CALLER_ID] =/=Int #Flapper.live
       andBool #Flapper.vat =/=Int #Flapper.live
       andBool #lookup(Vat_STORAGE, #Vat.can[ACCT_ID][ACCT_ID]) ==Int Junk_3
       andBool #lookup(Vat_STORAGE, #Vat.dai[ACCT_ID]) ==Int Dai_a
       andBool #lookup(Vat_STORAGE, #Vat.dai[CALLER_ID]) ==Int Dai_u
       andBool #lookup(Vat_ORIG_STORAGE, #Vat.can[ACCT_ID][ACCT_ID]) ==Int Junk_4
       andBool #lookup(Vat_ORIG_STORAGE, #Vat.dai[ACCT_ID]) ==Int Junk_5
       andBool #lookup(Vat_ORIG_STORAGE, #Vat.dai[CALLER_ID]) ==Int Junk_6
       andBool #Vat.can[ACCT_ID][ACCT_ID] =/=Int #Vat.dai[ACCT_ID]
       andBool #Vat.can[ACCT_ID][ACCT_ID] =/=Int #Vat.dai[CALLER_ID]
       andBool #Vat.dai[ACCT_ID] =/=Int #Vat.dai[CALLER_ID]

endmodule
