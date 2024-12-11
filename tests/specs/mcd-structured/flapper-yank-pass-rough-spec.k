requires "verification.k"

module FLAPPER-YANK-PASS-ROUGH-SPEC
    imports VERIFICATION

    // Flapper_yank
    claim [Flapper.yank.pass.rough]:
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
            <program> Flapper_bin_runtime </program>
            <jumpDests> #computeValidJumpDests(Flapper_bin_runtime) </jumpDests>
            <id> ACCT_ID </id>
            <caller> CALLER_ID </caller>
            <callData> #abiCallData("yank", #uint256(ABI_id)) +Bytes CD => ?_ </callData>
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
              <code> Flapper_bin_runtime </code>
              <storage>
                (#Flapper.live |-> Live)
                (#Flapper.gem |-> DSToken)
                (#Flapper.bids[ABI_id].bid |-> Bid)
                (#Flapper.bids[ABI_id].lot |-> Lot)
                (#Flapper.bids[ABI_id].guy_tic_end |-> #WordPackAddrUInt48UInt48(Guy, Tic, End))
                ACCT_ID_STORAGE =>
                  (#Flapper.live |-> Live)
                  (#Flapper.gem |-> DSToken)
                  (#Flapper.bids[ABI_id].bid |-> 0)
                  (#Flapper.bids[ABI_id].lot |-> 0)
                  (#Flapper.bids[ABI_id].guy_tic_end |-> 0)
                  ACCT_ID_STORAGE
              </storage>
              <origStorage> ACCT_ID_ORIG_STORAGE </origStorage>
              <nonce> Nonce_Flapper </nonce>
              <transientStorage> _ </transientStorage>
            </account>
            <account>
              <acctID> DSToken </acctID>
              <balance> DSToken_balance </balance>
              <code> DSToken_bin_runtime </code>
              <storage>
                (#DSToken.balances[ACCT_ID] |-> Gem_a)
                (#DSToken.balances[Guy] |-> Gem_g)
                (#DSToken.owner_stopped |-> #WordPackAddrUInt8(Owner, Stopped))
                DSToken_STORAGE =>
                  (#DSToken.balances[ACCT_ID] |-> Gem_a -Int Bid)
                  (#DSToken.balances[Guy] |-> Gem_g +Int Bid)
                  (#DSToken.owner_stopped |-> #WordPackAddrUInt8(Owner, Stopped))
                  DSToken_STORAGE
              </storage>
              <origStorage>
                DSToken_ORIG_STORAGE
              </origStorage>
              <nonce> Nonce_DSToken </nonce>
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

       andBool (#rangeUInt(256, ABI_id)
       andBool (#rangeUInt(256, Live)
       andBool (#rangeAddress(DSToken)
       andBool (#rangeUInt(256, Bid)
       andBool (#rangeUInt(256, Lot)
       andBool (#rangeAddress(Guy)
       andBool (#rangeUInt(48, Tic)
       andBool (#rangeUInt(48, End)
       andBool (#rangeUInt(256, Gem_a)
       andBool (#rangeUInt(256, Gem_g)
       andBool (#rangeBool(Stopped)
       andBool (#rangeAddress(Owner)
       andBool (#rangeUInt(256, DSToken_balance)
       andBool ((lengthBytes(CD) <=Int 1250000000)
       andBool ((#notPrecompileAddress(DSToken))
       andBool ((#notPrecompileAddress(Guy))
       andBool ((#notPrecompileAddress(Owner))
       andBool ((ACCT_ID =/=Int DSToken)
       andBool (((DSToken =/=Int 0))
       andBool ((ACCT_ID =/=Int Guy)
       andBool (((Live ==Int 0))
       andBool (((Guy =/=Int 0))
       andBool (((Stopped ==Int 0))
       andBool (((VCallDepth <Int 1024))
       andBool (((VCallValue ==Int 0))
       andBool ((#rangeUInt(256, Gem_a -Int Bid))
       andBool ((#rangeUInt(256, Gem_g +Int Bid)))))))))))))))))))))))))))))

       andBool #rangeNonce(Nonce_Flapper)
       andBool #rangeNonce(Nonce_DSToken)

    // TO DISCUSS: This specification cannot be useful for the above, because it
    // changes #DSToken.allowance[ABI_src][CALLER_ID], but the above spec does not.
    // DSToken_move
    claim [DSToken.move.pass]:
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
            <program> DSToken_bin_runtime </program>
            <jumpDests> #computeValidJumpDests(DSToken_bin_runtime) </jumpDests>
            <id> ACCT_ID </id>
            <caller> CALLER_ID </caller>
            <callData> #abiCallData("move", #address(ABI_src), #address(ABI_dst), #uint256(ABI_wad)) +Bytes CD => ?_ </callData>
            <callValue> VCallValue </callValue>
            <wordStack> .WordStack => ?_ </wordStack>
            <localMem> .Bytes => ?_ </localMem>
            <pc> 0 => ?_ </pc>
            <gas> #gas(VGas) => #if ( Allowance ==Int maxUInt256 )
              #then   #gas ( ( ( ( VGas -Int Csstore( ISTANBUL , ( Gem_s -Int ABI_wad ) , Gem_s , Junk_1 ) ) -Int Csstore( ISTANBUL , ( Gem_d +Int ABI_wad ) , Gem_d , Junk_2 ) ) +Int -7281 ) )
              #else   #gas ( ( ( ( ( VGas -Int Csstore( ISTANBUL , ( Allowance -Int ABI_wad ) , Allowance , Junk_0 ) ) -Int Csstore( ISTANBUL , ( Gem_s -Int ABI_wad ) , Gem_s , Junk_1 ) ) -Int Csstore( ISTANBUL , ( Gem_d +Int ABI_wad ) , Gem_d , Junk_2 ) ) +Int -9538 ) )
            #fi </gas>
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
              <code> DSToken_bin_runtime </code>
              <storage>
                (#DSToken.allowance[ABI_src][CALLER_ID] |-> Allowance)
                (#DSToken.balances[ABI_src] |-> Gem_s)
                (#DSToken.balances[ABI_dst] |-> Gem_d)
                (#DSToken.owner_stopped |-> #WordPackAddrUInt8(Owner, Stopped))
                ACCT_ID_STORAGE =>
                  (#DSToken.allowance[ABI_src][CALLER_ID] |-> #if Allowance ==Int maxUInt256 #then Allowance #else Allowance -Int ABI_wad #fi)
                  (#DSToken.balances[ABI_src] |-> Gem_s -Int ABI_wad)
                  (#DSToken.balances[ABI_dst] |-> Gem_d +Int ABI_wad)
                  (#DSToken.owner_stopped |-> #WordPackAddrUInt8(Owner, Stopped))
                  ACCT_ID_STORAGE
              </storage>
              <origStorage>
                (#DSToken.allowance[ABI_src][CALLER_ID] |-> Junk_0)
                (#DSToken.balances[ABI_src] |-> Junk_1)
                (#DSToken.balances[ABI_dst] |-> Junk_2)
                ACCT_ID_ORIG_STORAGE
              </origStorage>
              <nonce> Nonce_DSToken </nonce>
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

       andBool (#rangeAddress(ABI_src)
       andBool (#rangeAddress(ABI_dst)
       andBool (#rangeUInt(256, ABI_wad)
       andBool (#rangeUInt(256, Gem_s)
       andBool (#rangeUInt(256, Gem_d)
       andBool (#rangeUInt(256, Allowance)
       andBool (#rangeAddress(Owner)
       andBool (#rangeBool(Stopped)
       andBool ((lengthBytes(CD) <=Int 1250000000)
       andBool ((#notPrecompileAddress(Owner))
       andBool ((ABI_src =/=Int ABI_dst)
       andBool ((ABI_src =/=Int CALLER_ID)
       andBool (#rangeUInt(256, Junk_0)
       andBool (#rangeUInt(256, Junk_1)
       andBool (#rangeUInt(256, Junk_2)
       andBool (((#rangeUInt(256, Gem_s -Int ABI_wad)))
       andBool (((#rangeUInt(256, Gem_d +Int ABI_wad)))
       andBool (((Allowance ==Int maxUInt256) orBool (ABI_wad <=Int Allowance))
       andBool ((VCallValue ==Int 0)
       andBool ((Stopped ==Int 0)))))))))))))))))))))

       andBool #rangeNonce(Nonce_DSToken)

    [trusted]

endmodule
