requires "verification.k"

module FLAPPER-YANK-PASS-ROUGH-SPEC
    imports VERIFICATION

    // Flapper_yank
    claim [Flapper.yank.pass.rough]:
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
          <accounts>
            <account>
              <acctID> ACCT_ID </acctID>
              <balance> ACCT_ID_balance </balance>
              <code> Flapper_bin_runtime </code>
              <storage> ACCT_ID_STORAGE => ACCT_ID_STORAGE [ #Flapper.bids[ABI_id].bid <- 0 ] [ #Flapper.bids[ABI_id].lot <- 0 ] [ #Flapper.bids[ABI_id].guy_tic_end <- 0 ] </storage>
              <origStorage> ACCT_ID_ORIG_STORAGE </origStorage>
              <nonce> Nonce_Flapper </nonce>
            </account>
            <account>
              <acctID> DSToken </acctID>
              <balance> DSToken_balance </balance>
              <code> DSToken_bin_runtime </code>
              <storage> DSToken_STORAGE => DSToken_STORAGE [ #DSToken.balances[ACCT_ID] <- Gem_a -Int Bid ] [ #DSToken.balances[Guy] <- Gem_g +Int Bid ] </storage>
              <origStorage> DSToken_ORIG_STORAGE </origStorage>
              <nonce> Nonce_DSToken </nonce>
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
       andBool (#rangeUInt(256, Junk_0)
       andBool (#rangeUInt(256, Junk_1)
       andBool (#rangeUInt(256, Junk_2)
       andBool (#rangeUInt(256, Junk_3)
       andBool (#rangeUInt(256, Junk_4)
       andBool (#rangeUInt(256, Junk_5)
       andBool (#rangeUInt(256, Junk_6)
       andBool (#rangeUInt(256, Junk_7)
       andBool (((Live ==Int 0))
       andBool (((Guy =/=Int 0))
       andBool (((Stopped ==Int 0))
       andBool (((VCallDepth <Int 1024))
       andBool (((VCallValue ==Int 0))
       andBool ((#rangeUInt(256, Gem_a -Int Bid))
       andBool ((#rangeUInt(256, Gem_g +Int Bid)))))))))))))))))))))))))))))))))))))

       andBool #lookup(ACCT_ID_STORAGE, #Flapper.live) ==Int Live
       andBool #lookup(ACCT_ID_STORAGE, #Flapper.gem) ==Int DSToken
       andBool #lookup(ACCT_ID_STORAGE, #Flapper.bids[ABI_id].bid) ==Int Bid
       andBool #lookup(ACCT_ID_STORAGE, #Flapper.bids[ABI_id].lot) ==Int Lot
       andBool #lookup(ACCT_ID_STORAGE, #Flapper.bids[ABI_id].guy_tic_end) ==Int #WordPackAddrUInt48UInt48(Guy, Tic, End)
       andBool #lookup(ACCT_ID_ORIG_STORAGE, #Flapper.live) ==Int Junk_0
       andBool #lookup(ACCT_ID_ORIG_STORAGE, #Flapper.gem) ==Int Junk_1
       andBool #lookup(ACCT_ID_ORIG_STORAGE, #Flapper.bids[ABI_id].bid) ==Int Junk_2
       andBool #lookup(ACCT_ID_ORIG_STORAGE, #Flapper.bids[ABI_id].lot) ==Int Junk_3
       andBool #lookup(ACCT_ID_ORIG_STORAGE, #Flapper.bids[ABI_id].guy_tic_end) ==Int Junk_4
       andBool #Flapper.live =/=Int #Flapper.gem
       andBool #Flapper.live =/=Int #Flapper.bids[ABI_id].bid
       andBool #Flapper.live =/=Int #Flapper.bids[ABI_id].lot
       andBool #Flapper.live =/=Int #Flapper.bids[ABI_id].guy_tic_end
       andBool #Flapper.gem =/=Int #Flapper.bids[ABI_id].bid
       andBool #Flapper.gem =/=Int #Flapper.bids[ABI_id].lot
       andBool #Flapper.gem =/=Int #Flapper.bids[ABI_id].guy_tic_end
       andBool #Flapper.bids[ABI_id].bid =/=Int #Flapper.bids[ABI_id].lot
       andBool #Flapper.bids[ABI_id].bid =/=Int #Flapper.bids[ABI_id].guy_tic_end
       andBool #Flapper.bids[ABI_id].lot =/=Int #Flapper.bids[ABI_id].guy_tic_end
       andBool #lookup(DSToken_STORAGE, #DSToken.balances[ACCT_ID]) ==Int Gem_a
       andBool #lookup(DSToken_STORAGE, #DSToken.balances[Guy]) ==Int Gem_g
       andBool #lookup(DSToken_STORAGE, #DSToken.owner_stopped) ==Int #WordPackAddrUInt8(Owner, Stopped)
       andBool #lookup(DSToken_ORIG_STORAGE, #DSToken.balances[ACCT_ID]) ==Int Junk_5
       andBool #lookup(DSToken_ORIG_STORAGE, #DSToken.balances[Guy]) ==Int Junk_6
       andBool #lookup(DSToken_ORIG_STORAGE, #DSToken.owner_stopped) ==Int Junk_7
       andBool #DSToken.balances[ACCT_ID] =/=Int #DSToken.balances[Guy]
       andBool #DSToken.balances[ACCT_ID] =/=Int #DSToken.owner_stopped
       andBool #DSToken.balances[Guy] =/=Int #DSToken.owner_stopped
       andBool #rangeNonce(Nonce_Flapper)
       andBool #rangeNonce(Nonce_DSToken)

    // DSToken_move
    claim [DSToken.move.pass]:
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
            <program> DSToken_bin_runtime </program>
            <jumpDests> #computeValidJumpDests(DSToken_bin_runtime) </jumpDests>
            <id> ACCT_ID </id>
            <caller> CALLER_ID </caller>
            <callData> #abiCallData("move", #address(ABI_src), #address(ABI_dst), #uint256(ABI_wad)) +Bytes CD => ?_ </callData>
            <callValue> VCallValue </callValue>
            <wordStack> .WordStack => ?_ </wordStack>
            <localMem> .Bytes => ?_ </localMem>
            <pc> 0 => ?_ </pc>
            <gas> #gas(VGas) => #if ( #lookup( ACCT_ID_STORAGE , #hashedLocation("Solidity", 2, ABI_src CALLER_ID .IntList) ) ==Int maxUInt256 andBool ( Allowance ==Int maxUInt256 andBool ( maxUInt256 ==Int maxUInt256 orBool ABI_wad <=Int maxUInt256 ) ) )
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
          </block>
        </evm>
        <network>
          <chainID> VChainId </chainID>
          <accounts>
            <account>
              <acctID> ACCT_ID </acctID>
              <balance> ACCT_ID_balance </balance>
              <code> DSToken_bin_runtime </code>
              <storage> ACCT_ID_STORAGE => ACCT_ID_STORAGE [ #DSToken.allowance[ABI_src][CALLER_ID] <- #if (ABI_src ==Int CALLER_ID orBool Allowance ==Int maxUInt256) #then Allowance #else Allowance -Int ABI_wad #fi ] [ #DSToken.balances[ABI_src] <- Gem_s -Int ABI_wad ] [ #DSToken.balances[ABI_dst] <- Gem_d +Int ABI_wad ] </storage>
              <origStorage> ACCT_ID_ORIG_STORAGE </origStorage>
              <nonce> Nonce_DSToken </nonce>
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
       andBool (#rangeUInt(256, Junk_3)
       andBool (((#rangeUInt(256, Gem_s -Int ABI_wad)))
       andBool (((#rangeUInt(256, Gem_d +Int ABI_wad)))
       andBool (((Allowance ==Int maxUInt256) orBool (ABI_wad <=Int Allowance))
       andBool ((VCallValue ==Int 0)
       andBool ((Stopped ==Int 0))))))))))))))))))))))

       andBool #lookup(ACCT_ID_STORAGE, #DSToken.allowance[ABI_src][CALLER_ID]) ==Int Allowance
       andBool #lookup(ACCT_ID_STORAGE, #DSToken.balances[ABI_src]) ==Int Gem_s
       andBool #lookup(ACCT_ID_STORAGE, #DSToken.balances[ABI_dst]) ==Int Gem_d
       andBool #lookup(ACCT_ID_STORAGE, #DSToken.owner_stopped) ==Int #WordPackAddrUInt8(Owner, Stopped)
       andBool #lookup(ACCT_ID_ORIG_STORAGE, #DSToken.allowance[ABI_src][CALLER_ID]) ==Int Junk_0
       andBool #lookup(ACCT_ID_ORIG_STORAGE, #DSToken.balances[ABI_src]) ==Int Junk_1
       andBool #lookup(ACCT_ID_ORIG_STORAGE, #DSToken.balances[ABI_dst]) ==Int Junk_2
       andBool #lookup(ACCT_ID_ORIG_STORAGE, #DSToken.owner_stopped) ==Int Junk_3
       andBool #DSToken.allowance[ABI_src][CALLER_ID] =/=Int #DSToken.balances[ABI_src]
       andBool #DSToken.allowance[ABI_src][CALLER_ID] =/=Int #DSToken.balances[ABI_dst]
       andBool #DSToken.allowance[ABI_src][CALLER_ID] =/=Int #DSToken.owner_stopped
       andBool #DSToken.balances[ABI_src] =/=Int #DSToken.balances[ABI_dst]
       andBool #DSToken.balances[ABI_src] =/=Int #DSToken.owner_stopped
       andBool #DSToken.balances[ABI_dst] =/=Int #DSToken.owner_stopped
       andBool #rangeNonce(Nonce_DSToken)
    [trusted]


endmodule
