requires "verification.k"

module FLOPPER-DENT-GUY-DIFF-TIC-NOT-0-PASS-ROUGH-SPEC
    imports VERIFICATION

    // Flopper_dent-guy-diff-tic-not-0
    claim [Flopper.dent-guy-diff-tic-not-0.pass.rough]:
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
            <program> Flopper_bin_runtime </program>
            <jumpDests> #computeValidJumpDests(Flopper_bin_runtime) </jumpDests>
            <id> ACCT_ID </id>
            <caller> CALLER_ID </caller>
            <callData> #abiCallData("dent", #uint256(ABI_id), #uint256(ABI_lot), #uint256(ABI_bid)) +Bytes CD => ?_ </callData>
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
              <code> Flopper_bin_runtime </code>
              <storage>
                (#Flopper.live |-> Live)
                (#Flopper.vat |-> Vat)
                (#Flopper.beg |-> Beg)
                (#Flopper.ttl_tau |-> #WordPackUInt48UInt48(Ttl, Tau))
                (#Flopper.bids[ABI_id].bid |-> Bid)
                (#Flopper.bids[ABI_id].lot |-> Lot)
                (#Flopper.bids[ABI_id].guy_tic_end |-> #WordPackAddrUInt48UInt48(Guy, Tic, End))
                ACCT_ID_STORAGE =>
                  (#Flopper.live |-> Live)
                  (#Flopper.vat |-> Vat)
                  (#Flopper.beg |-> Beg)
                  (#Flopper.ttl_tau |-> #WordPackUInt48UInt48(Ttl, Tau))
                  (#Flopper.bids[ABI_id].bid |-> Bid)
                  (#Flopper.bids[ABI_id].lot |-> ABI_lot)
                  (#Flopper.bids[ABI_id].guy_tic_end |-> #WordPackAddrUInt48UInt48(CALLER_ID, TIME +Int Ttl, End))
                  ACCT_ID_STORAGE
              </storage>
              <origStorage> ACCT_ID_ORIG_STORAGE </origStorage>
              <nonce> Nonce_Flopper </nonce>
              <transientStorage> _ </transientStorage>
            </account>
            <account>
              <acctID> Vat </acctID>
              <balance> Vat_balance </balance>
              <code> Vat_bin_runtime </code>
              <storage>
                (#Vat.can[CALLER_ID][ACCT_ID] |-> CanMove)
                (#Vat.dai[CALLER_ID] |-> Dai_a)
                (#Vat.dai[Guy] |-> Dai_g)
                Vat_STORAGE =>
                  (#Vat.can[CALLER_ID][ACCT_ID] |-> CanMove)
                  (#Vat.dai[CALLER_ID] |-> Dai_a -Int ABI_bid)
                  (#Vat.dai[Guy] |-> Dai_g +Int ABI_bid)
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
       andBool #rangeNonce(Nonce_Flopper)
       andBool #rangeNonce(Nonce_Vat)

       andBool (#rangeUInt(256, ABI_id)
       andBool (#rangeUInt(256, ABI_lot)
       andBool (#rangeUInt(256, ABI_bid)
       andBool (#rangeUInt(256, Live)
       andBool (#rangeAddress(Vat)
       andBool (#rangeUInt(256, Beg)
       andBool (#rangeUInt(48, Ttl)
       andBool (#rangeUInt(48, Tau)
       andBool (#rangeUInt(256, Bid)
       andBool (#rangeUInt(256, Lot)
       andBool (#rangeAddress(Guy)
       andBool (#rangeUInt(48, Tic)
       andBool (#rangeUInt(48, End)
       andBool (#rangeUInt(256, CanMove)
       andBool (#rangeUInt(256, Dai_a)
       andBool (#rangeUInt(256, Dai_g)
       andBool (#rangeUInt(256, Vat_balance)
       andBool ((lengthBytes(CD) <=Int 1250000000)
       andBool ((#notPrecompileAddress(Vat))
       andBool ((#notPrecompileAddress(Guy))
       andBool ((ACCT_ID =/=Int Vat)
       andBool ((CALLER_ID =/=Int ACCT_ID)
       andBool ((CALLER_ID =/=Int Guy)
       andBool ((#rangeUInt(48, TIME))
       andBool ((Tic =/=Int 0)
       andBool ((Vat =/=Int 0)
       andBool ((((Live ==Int 1)))
       andBool ((((Guy =/=Int 0)))
       andBool ((((Tic >Int TIME)))
       andBool ((((End >Int TIME)))
       andBool ((((ABI_bid ==Int Bid)))
       andBool ((((ABI_lot <Int  Lot)))
       andBool ((((Lot *Int #Wad <=Int maxUInt256)))
       andBool ((((Beg *Int ABI_lot <=Int Lot *Int #Wad)))
       andBool ((((CanMove ==Int 1)))
       andBool ((((VCallValue ==Int 0)))
       andBool ((((VCallDepth <Int 1024)))
       andBool (((#rangeUInt(256, Dai_a -Int ABI_bid)))
       andBool (((#rangeUInt(256, Dai_g +Int ABI_bid)))
       andBool ((#rangeUInt(48, TIME +Int Ttl))))))))))))))))))))))))))))))))))))))))))

    // Flopper_muluu
    claim [Flopper.muluu.pass]:
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
            <program> Flopper_bin_runtime </program>
            <jumpDests> #computeValidJumpDests(Flopper_bin_runtime) </jumpDests>
            <id> ACCT_ID </id>
            <caller> CALLER_ID </caller>
            <callData> _ => ?_ </callData>
            <callValue> VCallValue </callValue>
            <wordStack> ABI_y : ABI_x : JMPTO : WS  =>  JMPTO : ABI_x *Int ABI_y : WS </wordStack>
            <wordStackSize> WSSize => WSSize -Int 1 </wordStackSize>
            <localMem> _ </localMem>
            <pc> 8685 => 8728 </pc>
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
              <code> Flopper_bin_runtime </code>
              <storage> ACCT_ID_STORAGE => ACCT_ID_STORAGE  </storage>
              <origStorage> _ACCT_ID_ORIG_STORAGE </origStorage>
              <nonce> Nonce_Flopper </nonce>
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
       andBool #rangeNonce(Nonce_Flopper)

       andBool (#rangeUInt(256, ABI_x)
       andBool (#rangeUInt(256, ABI_y)
       andBool ((3 <=Int WSSize)
       andBool ((WSSize <=Int 1000)
       andBool (#rangeUInt(256, VMemoryUsed)
       andBool ((#rangeUInt(256, ABI_x *Int ABI_y))))))))

    [trusted]

    // Flopper_addu48u48
    claim [Flopper.addu48u48.pass]:
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
            <program> Flopper_bin_runtime </program>
            <jumpDests> #computeValidJumpDests(Flopper_bin_runtime) </jumpDests>
            <id> ACCT_ID </id>
            <caller> CALLER_ID </caller>
            <callData> _ => ?_ </callData>
            <callValue> VCallValue </callValue>
            <wordStack> ABI_y : ABI_x : JMPTO : WS  =>  JMPTO : ABI_x +Int ABI_y : WS </wordStack>
            <wordStackSize> WSSize => WSSize -Int 1 </wordStackSize>
            <localMem> _ </localMem>
            <pc> 8757 => 8798 </pc>
            <gas> #gas(VGas) => #gas ( ( VGas +Int -66 ) ) </gas>
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
              <code> Flopper_bin_runtime </code>
              <storage> ACCT_ID_STORAGE => ACCT_ID_STORAGE  </storage>
              <origStorage> _ACCT_ID_ORIG_STORAGE </origStorage>
              <nonce> Nonce_Flopper </nonce>
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
       andBool #rangeNonce(Nonce_Flopper)

       andBool (#rangeUInt(48, ABI_x)
       andBool (#rangeUInt(48, ABI_y)
       andBool ((3 <=Int WSSize)
       andBool ((WSSize <=Int 100)
       andBool (#rangeUInt(256, VMemoryUsed)
       andBool ((#rangeUInt(48, ABI_x +Int ABI_y))))))))

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
