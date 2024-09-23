requires "verification.k"

module POT-JOIN-PASS-ROUGH-SPEC
    imports VERIFICATION

    // Pot_join
    claim [Pot.join.pass.rough]:
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
            <program> Pot_bin_runtime </program>
            <jumpDests> #computeValidJumpDests(Pot_bin_runtime) </jumpDests>
            <id> ACCT_ID </id>
            <caller> CALLER_ID </caller>
            <callData> #abiCallData("join", #uint256(ABI_wad)) +Bytes CD => ?_ </callData>
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
              <code> Pot_bin_runtime </code>
              <storage>
                (#Pot.pie[CALLER_ID] |-> Pie_u)
                (#Pot.Pie |-> Pie_tot)
                (#Pot.chi |-> Chi)
                (#Pot.rho |-> Rho)
                (#Pot.vat |-> Vat)
                ACCT_ID_STORAGE =>
                  (#Pot.pie[CALLER_ID] |-> Pie_u +Int ABI_wad)
                  (#Pot.Pie |-> Pie_tot +Int ABI_wad)
                  (#Pot.chi |-> Chi)
                  (#Pot.rho |-> Rho)
                  (#Pot.vat |-> Vat)
                  ACCT_ID_STORAGE
              </storage>
              <origStorage> ACCT_ID_ORIG_STORAGE </origStorage>
              <nonce> Nonce_Pot </nonce>
              <transientStorage> _ </transientStorage>
            </account>
            <account>
              <acctID> Vat </acctID>
              <balance> Vat_balance </balance>
              <code> Vat_bin_runtime </code>
              <storage>
                (#Vat.can[CALLER_ID][ACCT_ID] |-> Can)
                (#Vat.dai[CALLER_ID] |-> Dai_u)
                (#Vat.dai[ACCT_ID] |-> Dai_p)
                Vat_STORAGE =>
                  (#Vat.can[CALLER_ID][ACCT_ID] |-> Can)
                  (#Vat.dai[CALLER_ID] |-> Dai_u -Int Chi *Int ABI_wad)
                  (#Vat.dai[ACCT_ID] |-> Dai_p +Int Chi *Int ABI_wad)
                  Vat_STORAGE
              </storage>
              <origStorage> Vat_ORIG_STORAGE </origStorage>
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
       andBool #rangeNonce(Nonce_Pot)
       andBool #rangeNonce(Nonce_Vat)

       andBool (#rangeUInt(256, ABI_wad)
       andBool (#rangeUInt(256, Pie_u)
       andBool (#rangeUInt(256, Pie_tot)
       andBool (#rangeUInt(256, Chi)
       andBool (#rangeUInt(256, Rho)
       andBool (#rangeAddress(Vat)
       andBool (#rangeUInt(256, Can)
       andBool (#rangeUInt(256, Dai_u)
       andBool (#rangeUInt(256, Dai_p)
       andBool (#rangeUInt(256, Vat_balance)
       andBool ((lengthBytes(CD) <=Int 1250000000)
       andBool ((#notPrecompileAddress(Vat))
       andBool ((ACCT_ID =/=Int Vat)
       andBool ((ACCT_ID =/=Int CALLER_ID)
       andBool ((Vat =/=Int 0)
       andBool (((VCallValue ==Int 0))
       andBool (((VCallDepth <Int 1024))
       andBool (((Can ==Int 1))
       andBool (((Rho ==Int TIME))
       andBool ((#rangeUInt(256, Pie_u +Int ABI_wad))
       andBool ((#rangeUInt(256, Pie_tot +Int ABI_wad))
       andBool ((#rangeUInt(256, Chi *Int ABI_wad))
       andBool ((#rangeUInt(256, Dai_u -Int Chi *Int ABI_wad))
       andBool ((#rangeUInt(256, Dai_p +Int Chi *Int ABI_wad))))))))))))))))))))))))))

    // Pot_adduu
    claim [Pot.adduu.pass]:
      <k> #execute ~> CONTINUATION => #execute ~> CONTINUATION </k>
      <mode> NORMAL </mode>
      <schedule> ISTANBUL </schedule>
      <useGas> true </useGas>
      <ethereum>
        <evm>
          <output> VOutput => VOutput </output>
          <statusCode> _ => ?_ </statusCode>
          <callStack> _VCallStack </callStack>
          <interimStates> _ </interimStates>
          <touchedAccounts> _ => ?_ </touchedAccounts>
          <callState>
            <program> Pot_bin_runtime </program>
            <jumpDests> #computeValidJumpDests(Pot_bin_runtime) </jumpDests>
            <id> ACCT_ID </id>
            <caller> CALLER_ID </caller>
            <callData> _ => ?_ </callData>
            <callValue> VCallValue </callValue>
            <wordStack> ABI_y : ABI_x : JMPTO : WS  =>  JMPTO : ABI_x +Int ABI_y : WS </wordStack>
            <wordStackSize> WSSIZE => WSSIZE -Int 1 </wordStackSize>
            <localMem> _ </localMem>
            <pc> 4851 => 4876 </pc>
            <gas> #gas(VGas) => #gas ( ( VGas +Int -54 ) ) </gas>
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
              <code> Pot_bin_runtime </code>
              <storage> ACCT_ID_STORAGE => ACCT_ID_STORAGE  </storage>
              <origStorage> _ACCT_ID_ORIG_STORAGE </origStorage>
              <nonce> Nonce_Pot </nonce>
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
       andBool #rangeNonce(Nonce_Pot)

       andBool (#rangeUInt(256, ABI_x)
       andBool (#rangeUInt(256, ABI_y)
       andBool ((3 <=Int WSSIZE)
       andBool ((WSSIZE <=Int 100)
       andBool (#rangeUInt(256, VMemoryUsed)
       andBool ((#rangeUInt(256, ABI_x +Int ABI_y))))))))

    [trusted]

    // Pot_muluu
    claim [Pot.muluu.pass]:
      <k> #execute ~> CONTINUATION => #execute ~> CONTINUATION </k>
      <mode> NORMAL </mode>
      <schedule> ISTANBUL </schedule>
      <useGas> true </useGas>
      <ethereum>
        <evm>
          <output> VOutput => VOutput </output>
          <statusCode> _ => ?_ </statusCode>
          <callStack> _VCallStack </callStack>
          <interimStates> _ </interimStates>
          <touchedAccounts> _ => ?_ </touchedAccounts>
          <callState>
            <program> Pot_bin_runtime </program>
            <jumpDests> #computeValidJumpDests(Pot_bin_runtime) </jumpDests>
            <id> ACCT_ID </id>
            <caller> CALLER_ID </caller>
            <callData> _ => ?_ </callData>
            <callValue> VCallValue </callValue>
            <wordStack> ABI_y : ABI_x : JMPTO : WS  =>  JMPTO : ABI_x *Int ABI_y : WS </wordStack>
            <wordStackSize> WSSIZE => WSSIZE -Int 1 </wordStackSize>
            <localMem> _ </localMem>
            <pc> 4877 => 4920 </pc>
            <gas> #gas(VGas) => #if ABI_y ==Int 0
              #then   #gas ( ( VGas +Int -54 ) )
              #else   #gas ( ( VGas +Int -106 ) )
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
              <code> Pot_bin_runtime </code>
              <storage> ACCT_ID_STORAGE => ACCT_ID_STORAGE  </storage>
              <origStorage> _ACCT_ID_ORIG_STORAGE </origStorage>
              <nonce> Nonce_Pot </nonce>
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
       andBool #rangeNonce(Nonce_Pot)

       andBool (#rangeUInt(256, ABI_x)
       andBool (#rangeUInt(256, ABI_y)
       andBool ((3 <=Int WSSIZE)
       andBool ((WSSIZE <=Int 1000)
       andBool (#rangeUInt(256, VMemoryUsed)
       andBool ((#rangeUInt(256, ABI_x *Int ABI_y))))))))

    [trusted]

    // Vat_move-diff
    claim [Vat.move-diff.pass]:
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
            <callData> #abiCallData("move", #address(ABI_src), #address(ABI_dst), #uint256(ABI_rad)) +Bytes CD => ?_ </callData>
            <callValue> VCallValue </callValue>
            <wordStack> .WordStack => ?_ </wordStack>
            <wordStackSize> 0 => ?_ </wordStackSize>
            <localMem> .Bytes => ?_ </localMem>
            <pc> 0 => ?_ </pc>
            <gas> #gas(VGas) => #gas ( ( ( ( VGas -Int Csstore( ISTANBUL , ( Dai_src -Int ABI_rad ) , Dai_src , Junk_1 ) ) -Int Csstore( ISTANBUL , ( Dai_dst +Int ABI_rad ) , Dai_dst , Junk_2 ) ) +Int -7943 ) ) </gas>
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
                (#Vat.can[ABI_src][CALLER_ID] |-> May)
                (#Vat.dai[ABI_src] |-> Dai_src)
                (#Vat.dai[ABI_dst] |-> Dai_dst)
                ACCT_ID_STORAGE =>
                  (#Vat.can[ABI_src][CALLER_ID] |-> May)
                  (#Vat.dai[ABI_src] |-> (Dai_src -Int ABI_rad))
                  (#Vat.dai[ABI_dst] |-> (Dai_dst +Int ABI_rad))
                  ACCT_ID_STORAGE
              </storage>
              <origStorage>
                (#Vat.dai[ABI_src] |-> Junk_1)
                (#Vat.dai[ABI_dst] |-> Junk_2)
                ACCT_ID_ORIG_STORAGE
              </origStorage>
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

       andBool (#rangeAddress(ABI_src)
       andBool (#rangeAddress(ABI_dst)
       andBool (#rangeUInt(256, ABI_rad)
       andBool (#rangeUInt(256, Dai_dst)
       andBool (#rangeUInt(256, Dai_src)
       andBool (#rangeUInt(256, May)
       andBool ((lengthBytes(CD) <=Int 1250000000)
       andBool ((ABI_src =/=Int ABI_dst)
       andBool (#rangeUInt(256, Junk_1)
       andBool (#rangeUInt(256, Junk_2)
       andBool ((((May ==Int 1 orBool ABI_src ==Int CALLER_ID)))
       andBool (((VCallValue ==Int 0))
       andBool ((#rangeUInt(256, Dai_src -Int ABI_rad))
       andBool ((#rangeUInt(256, Dai_dst +Int ABI_rad))))))))))))))))

    [trusted]

endmodule
