requires "verification.k"

module CAT-ILKS-PASS-SPEC
  imports VERIFICATION

    // Cat_ilks
    rule [Cat.ilks.pass]:
      <k> #execute ~> CONTINUATION => #halt ~> CONTINUATION </k>
      <exit-code> 1 </exit-code>
      <mode> NORMAL </mode>
      <schedule> ISTANBUL </schedule>
      <ethereum>
        <evm>
          <output> _ => #buf(32, Flip) ++ #buf(32, Chop) ++ #buf(32, Lump) </output>
          <statusCode> _ => EVMC_SUCCESS </statusCode>
          <endPC> _ => ?_ </endPC>
          <callStack> VCallStack </callStack>
          <interimStates> _ </interimStates>
          <touchedAccounts> _ => ?_ </touchedAccounts>
          <callState>
            <program> Cat_bin_runtime </program>
            <jumpDests> #computeValidJumpDests(Cat_bin_runtime) </jumpDests>
            <id> ACCT_ID </id>
            <caller> CALLER_ID </caller>
            <callData> #abiCallData("ilks", #bytes32(ABI_ilk)) ++ CD => ?_ </callData>
            <callValue> VCallValue </callValue>
            <wordStack> .WordStack => ?_ </wordStack>
            <localMem> .Map => ?_ </localMem>
            <pc> 0 => ?_ </pc>
            <gas> VGas => VGas -Int (2977) </gas>
            <memoryUsed> 0 => ?_ </memoryUsed>
            <callGas> _ => ?_ </callGas>
            <static> _ </static>
            <callDepth> VCallDepth </callDepth>
          </callState>
          <substate>
            <selfDestruct> VSelfDestruct </selfDestruct>
            <log> _ => ?_ </log>
            <refund> _ => ?_ </refund>
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
            <number> BLOCK_NUMBER </number>
            <gasLimit> _ </gasLimit>
            <gasUsed> _ </gasUsed>
            <timestamp> TIME </timestamp>
            <extraData> _ </extraData>
            <mixHash> _ </mixHash>
            <blockNonce> _ </blockNonce>
            <ommerBlockHeaders> _ </ommerBlockHeaders>
          </block>
        </evm>
        <network>
          <chainID> VChainId </chainID>
          <activeAccounts> SetItem(ACCT_ID)
          SetItem(1)
          SetItem(2)
          SetItem(3)
          SetItem(4)
          SetItem(5)
          SetItem(6)
          SetItem(7)
          SetItem(8)
          SetItem(9) _ </activeAccounts>
          <accounts>
            <account>
              <acctID> ACCT_ID </acctID>
              <balance> ACCT_ID_balance </balance>
              <code> Cat_bin_runtime </code>
              <storage>
               .Map
              [#Cat.ilks[ABI_ilk].flip <- (Flip) => Flip]
              [#Cat.ilks[ABI_ilk].chop <- (Chop) => Chop]
              [#Cat.ilks[ABI_ilk].lump <- (Lump) => Lump]
                _:Map
               </storage>
              <origStorage>
               .Map
              [#Cat.ilks[ABI_ilk].flip <- (Junk_0)]
              [#Cat.ilks[ABI_ilk].chop <- (Junk_1)]
              [#Cat.ilks[ABI_ilk].lump <- (Junk_2)]
                _:Map
               </origStorage>
              <nonce> Nonce_Cat => ?_ </nonce>
            </account>
            <account>
              <acctID> 1 </acctID>
              <balance> ECREC_BAL </balance>
              <code> .WordStack </code>
              <storage> _:Map </storage>
              <origStorage> _ </origStorage>
              <nonce> _ </nonce>
            </account>
            <account>
              <acctID> 2 </acctID>
              <balance> SHA256_BAL </balance>
              <code> .WordStack </code>
              <storage> _:Map </storage>
              <origStorage> _ </origStorage>
              <nonce> _ </nonce>
            </account>
            <account>
              <acctID> 3 </acctID>
              <balance> RIP160_BAL </balance>
              <code> .WordStack </code>
              <storage> _:Map </storage>
              <origStorage> _ </origStorage>
              <nonce> _ </nonce>
            </account>
            <account>
              <acctID> 4 </acctID>
              <balance> ID_BAL </balance>
              <code> .WordStack </code>
              <storage> _:Map </storage>
              <origStorage> _ </origStorage>
              <nonce> _ </nonce>
            </account>
            <account>
              <acctID> 5 </acctID>
              <balance> MODEXP_BAL </balance>
              <code> .WordStack </code>
              <storage> _:Map </storage>
              <origStorage> _ </origStorage>
              <nonce> _ </nonce>
            </account>
            <account>
              <acctID> 6 </acctID>
              <balance> ECADD_BAL </balance>
              <code> .WordStack </code>
              <storage> _:Map </storage>
              <origStorage> _ </origStorage>
              <nonce> _ </nonce>
            </account>
            <account>
              <acctID> 7 </acctID>
              <balance> ECMUL_BAL </balance>
              <code> .WordStack </code>
              <storage> _:Map </storage>
              <origStorage> _ </origStorage>
              <nonce> _ </nonce>
            </account>
            <account>
              <acctID> 8 </acctID>
              <balance> ECPAIRING_BAL </balance>
              <code> .WordStack </code>
              <storage> _:Map </storage>
              <origStorage> _ </origStorage>
              <nonce> _ </nonce>
            </account>
            <account>
              <acctID> 9 </acctID>
              <balance> BLAKE2_BAL </balance>
              <code> .WordStack </code>
              <storage> _:Map </storage>
              <origStorage> _ </origStorage>
              <nonce> _ </nonce>
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
     andBool #rangeUInt(256, ECREC_BAL)
     andBool #rangeUInt(256, SHA256_BAL)
     andBool #rangeUInt(256, RIP160_BAL)
     andBool #rangeUInt(256, ID_BAL)
     andBool #rangeUInt(256, MODEXP_BAL)
     andBool #rangeUInt(256, ECADD_BAL)
     andBool #rangeUInt(256, ECMUL_BAL)
     andBool #rangeUInt(256, ECPAIRING_BAL)
     andBool #rangeUInt(256, BLAKE2_BAL)
     andBool VCallDepth <=Int 1024
     andBool #rangeUInt(256, VCallValue)
     andBool #rangeUInt(256, VChainId)

     andBool (#rangeBytes(32, ABI_ilk)
     andBool (#rangeUInt(256, Chop)
     andBool (#rangeAddress(Flip)
     andBool (#rangeUInt(256, Lump)
     andBool (#sizeByteArray(CD) <=Int 1250000000
     andBool (#notPrecompileAddress(Flip)
     andBool (2300 <Int VGas -Int (2977)
     andBool (#rangeUInt(256, Junk_0)
     andBool (#rangeUInt(256, Junk_1)
     andBool (#rangeUInt(256, Junk_2)
     andBool ((VCallValue ==Int 0))))))))))))

endmodule
