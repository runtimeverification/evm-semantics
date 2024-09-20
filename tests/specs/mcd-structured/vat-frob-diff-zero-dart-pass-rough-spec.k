requires "verification.k"
requires "vat-arithmetic-spec.k"

module VAT-FROB-DIFF-ZERO-DART-PASS-ROUGH-SPEC
    imports VERIFICATION
    imports VAT-ARITHMETIC-SPEC

    // Vat_frob-diff-zero-dart
    claim [Vat.frob-diff-zero-dart.pass.rough]:
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
            <callData> #abiCallData("frob", #bytes32(ABI_i), #address(ABI_u), #address(ABI_v), #address(ABI_w), #int256(ABI_dink), #int256(ABI_dart)) +Bytes CD => ?_ </callData>
            <callValue> VCallValue </callValue>
            <wordStack> .WordStack => ?_ </wordStack>
            <wordStackSize> 0 => ?_ </wordStackSize>
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
              <storage>
                (#Vat.gem[ABI_i][ABI_v] |-> Gem_iv)
                (#Vat.urns[ABI_i][ABI_u].ink |-> Urn_ink)
                ACCT_ID_STORAGE =>
                  (#Vat.gem[ABI_i][ABI_v] |-> Gem_iv -Int ABI_dink)
                  (#Vat.urns[ABI_i][ABI_u].ink |-> Urn_ink +Int ABI_dink)
                  ACCT_ID_STORAGE
              </storage>
              <origStorage> ACCT_ID_ORIG_STORAGE </origStorage>
              <nonce> _Nonce_Vat => ?_ </nonce>
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

       andBool (#rangeBytes(32, ABI_i)
       andBool (#rangeAddress(ABI_u)
       andBool (#rangeAddress(ABI_v)
       andBool (#rangeAddress(ABI_w)
       andBool (#rangeSInt(256, ABI_dink)
       andBool (#rangeSInt(256, ABI_dart)
       andBool (#rangeUInt(256, Ilk_rate)
       andBool (#rangeUInt(256, Ilk_spot)
       andBool (#rangeUInt(256, Ilk_dust)
       andBool (#rangeUInt(256, Ilk_Art)
       andBool (#rangeUInt(256, Urn_ink)
       andBool (#rangeUInt(256, Urn_art)
       andBool (#rangeUInt(256, Gem_iv)
       andBool (#rangeUInt(256, Can_u)
       andBool (#rangeUInt(256, Can_v)
       andBool (#rangeUInt(256, Live)
       andBool ((lengthBytes(CD) <=Int 1250000000)
       andBool ((ABI_u =/=Int ABI_v)
       andBool ((ABI_v =/=Int ABI_w)
       andBool ((ABI_u =/=Int ABI_w)
       andBool ((ABI_dink =/=Int 0)
       andBool ((ABI_dart ==Int 0)
       andBool ((((#rangeUInt(256, Urn_ink +Int ABI_dink))))
       andBool ((((#rangeUInt(256, Gem_iv  -Int ABI_dink))))
       andBool ((((#rangeUInt(256, (Urn_ink +Int ABI_dink) *Int Ilk_spot))))
       andBool ((((#rangeUInt(256, Urn_art *Int Ilk_rate))))
       andBool ((((#rangeUInt(256, Ilk_Art *Int Ilk_rate))))
       andBool (((#rangeSInt(256, Ilk_rate)))
       andBool ((VCallValue ==Int 0)
       andBool ((Live ==Int 1)
       andBool ((Ilk_rate =/=Int 0)
       andBool (((ABI_dink >=Int 0) orBool (((Urn_art *Int Ilk_rate) <=Int ((Urn_ink +Int ABI_dink) *Int Ilk_spot))))
       andBool (((ABI_dink >=Int 0) orBool (ABI_u ==Int CALLER_ID orBool Can_u ==Int 1))
       andBool (((ABI_dink <=Int 0) orBool (ABI_v ==Int CALLER_ID orBool Can_v ==Int 1))
       andBool (((Urn_art ==Int 0) orBool ((Urn_art *Int Ilk_rate) >=Int Ilk_dust)))))))))))))))))))))))))))))))))))))

       // TODO: These are to be brought back into the structure once booster unification improves
       andBool #lookup(ACCT_ID_STORAGE, #Vat.ilks[ABI_i].rate) ==Int Ilk_rate
       andBool #lookup(ACCT_ID_STORAGE, #Vat.ilks[ABI_i].spot) ==Int Ilk_spot
       andBool #lookup(ACCT_ID_STORAGE, #Vat.ilks[ABI_i].dust) ==Int Ilk_dust
       andBool #lookup(ACCT_ID_STORAGE, #Vat.can[ABI_u][CALLER_ID]) ==Int Can_u
       andBool #lookup(ACCT_ID_STORAGE, #Vat.can[ABI_v][CALLER_ID]) ==Int Can_v
       andBool #lookup(ACCT_ID_STORAGE, #Vat.urns[ABI_i][ABI_u].art) ==Int Urn_art
       andBool #lookup(ACCT_ID_STORAGE, #Vat.ilks[ABI_i].Art) ==Int Ilk_Art
       andBool #lookup(ACCT_ID_STORAGE, #Vat.live) ==Int Live

    [depends(VAT-ARITHMETIC-SPEC.Vat.addui.pass,VAT-ARITHMETIC-SPEC.Vat.subui.pass,VAT-ARITHMETIC-SPEC.Vat.mului.pass,VAT-ARITHMETIC-SPEC.Vat.muluu.pass)]

endmodule
