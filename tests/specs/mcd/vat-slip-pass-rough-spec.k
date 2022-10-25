requires "verification.k"

module VAT-SLIP-PASS-ROUGH-SPEC
    imports VERIFICATION

    // Vat_slip
    claim [Vat.slip.pass.rough]:
      <k> #execute ~> CONTINUATION => #halt ~> CONTINUATION </k>
      <exit-code> 1 </exit-code>
      <mode> NORMAL </mode>
      <schedule> ISTANBUL </schedule>
      <ethereum>
        <evm>
          <output> .ByteArray </output>
          <statusCode> _ => EVMC_SUCCESS </statusCode>
          <callStack> _VCallStack </callStack>
          <interimStates> _ </interimStates>
          <touchedAccounts> _ => ?_ </touchedAccounts>
          <callState>
            <program> Vat_bin_runtime </program>
            <jumpDests> #computeValidJumpDests(Vat_bin_runtime) </jumpDests>
            <id> ACCT_ID </id>
            <caller> CALLER_ID </caller>
            <callData> #abiCallData("slip", #bytes32(ABI_ilk), #address(ABI_usr), #int256(ABI_wad)) ++ CD => ?_ </callData>
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
              <code> Vat_bin_runtime </code>
              <storage> ACCT_ID_STORAGE => ACCT_ID_STORAGE [ #Vat.gem[ABI_ilk][ABI_usr] <- Gem +Int ABI_wad ] </storage>
              <origStorage> ACCT_ID_ORIG_STORAGE </origStorage>
              <nonce> _Nonce_Vat => ?_ </nonce>
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

       andBool (#rangeBytes(32, ABI_ilk)
       andBool (#rangeAddress(ABI_usr)
       andBool (#rangeSInt(256, ABI_wad)
       andBool (#rangeUInt(256, May)
       andBool (#rangeUInt(256, Gem)
       andBool (#sizeByteArray(CD) <=Int 1250000000
       andBool (#rangeUInt(256, Junk_0)
       andBool (#rangeUInt(256, Junk_1)
       andBool (((May ==Int 1))
       andBool (((VCallValue ==Int 0))
       andBool ((#rangeUInt(256, Gem +Int ABI_wad)))))))))))))

       andBool #lookup(ACCT_ID_STORAGE, #Vat.wards[CALLER_ID]) ==Int May
       andBool #lookup(ACCT_ID_STORAGE, #Vat.gem[ABI_ilk][ABI_usr]) ==Int Gem
       andBool #lookup(ACCT_ID_ORIG_STORAGE, #Vat.wards[CALLER_ID]) ==Int Junk_0
       andBool #lookup(ACCT_ID_ORIG_STORAGE, #Vat.gem[ABI_ilk][ABI_usr]) ==Int Junk_1
       andBool #Vat.wards[CALLER_ID] =/=Int #Vat.gem[ABI_ilk][ABI_usr]

    // Vat_addui
    claim [Vat.addui.pass]:
      <k> #execute ~> CONTINUATION => #execute ~> CONTINUATION </k>
      <exit-code> 1 </exit-code>
      <mode> NORMAL </mode>
      <schedule> ISTANBUL </schedule>
      <ethereum>
        <evm>
          <output> VOutput => VOutput </output>
          <statusCode> _ => ?_ </statusCode>
          <callStack> _VCallStack </callStack>
          <interimStates> _ </interimStates>
          <touchedAccounts> _ => ?_ </touchedAccounts>
          <callState>
            <program> Vat_bin_runtime </program>
            <jumpDests> #computeValidJumpDests(Vat_bin_runtime) </jumpDests>
            <id> ACCT_ID </id>
            <caller> CALLER_ID </caller>
            <callData> _ => ?_ </callData>
            <callValue> VCallValue </callValue>
            <wordStack> chop(ABI_y) : ABI_x : JMPTO : WS  =>  JMPTO : ABI_x +Int ABI_y : WS </wordStack>
            <localMem> _ </localMem>
            <pc> 13112 => 13174 </pc>
            <gas> #gas(VGas) => #if ( ABI_y <Int 0 andBool 0 <=Int ( ABI_x +Int ABI_y ) )
              #then   #gas ( ( VGas +Int -128 ) )
              #else   #if chop( ABI_y ) <=Int 0
                #then   #gas ( ( VGas +Int -114 ) )
                #else   #gas ( ( VGas +Int -128 ) )
              #fi
            #fi </gas>
            <memoryUsed> VMemoryUsed </memoryUsed>
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
              <code> Vat_bin_runtime </code>
              <storage> ACCT_ID_STORAGE => ACCT_ID_STORAGE  </storage>
              <origStorage> ACCT_ID_ORIG_STORAGE </origStorage>
              <nonce> _Nonce_Vat => ?_ </nonce>
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

       andBool (#rangeUInt(256, ABI_x)
       andBool (#rangeSInt(256, ABI_y)
       andBool ((#sizeWordStack(WS) <=Int 1015)
       andBool (#rangeUInt(256, VMemoryUsed)
       andBool ((#rangeUInt(256, ABI_x +Int ABI_y)))))))


    [trusted, matching(infGas)]


endmodule
