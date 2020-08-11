requires "verification.k"

module VAT-MOVE-DIFF-SPEC
  imports VERIFICATION

    // Vat_move-diff
    rule [Vat.move-diff.pass]:
      <k> #execute ~> CONTINUATION => #halt ~> CONTINUATION </k>
      <exit-code> 1 </exit-code>
      <mode> NORMAL </mode>
      <schedule> ISTANBUL </schedule>
      <ethereum>
        <evm>
          <output> .ByteArray </output>
          <statusCode> _ => EVMC_SUCCESS </statusCode>
          <endPC> _ => ?_ </endPC>
          <callStack> _VCallStack </callStack>
          <interimStates> _ </interimStates>
          <touchedAccounts> _ => ?_ </touchedAccounts>
          <callState>
            <program> Vat_bin_runtime </program>
            <jumpDests> #computeValidJumpDests(Vat_bin_runtime) </jumpDests>
            <id> ACCT_ID </id>
            <caller> CALLER_ID </caller>
            <callData> #abiCallData("move", #address(ABI_src), #address(ABI_dst), #uint256(ABI_rad)) ++ CD => ?_ </callData>
            <callValue> VCallValue </callValue>
            <wordStack> .WordStack => ?_ </wordStack>
            <localMem> .Memory => ?_ </localMem>
            <pc> 0 => ?_ </pc>
            <gas> VGas => ?_ </gas>
            <memoryUsed> 0 => ?_ </memoryUsed>
            <callGas> _ => ?_ </callGas>
            <static> false </static>
            <callDepth> VCallDepth </callDepth>
          </callState>
          <substate>
            <selfDestruct> _VSelfDestruct </selfDestruct>
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
            <number> _BLOCK_NUMBER </number>
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
              <code> Vat_bin_runtime </code>
              <storage> STORAGE
                     => STORAGE
                          [ #Vat.dai[ABI_src] <- Dai_src -Int ABI_rad ]
                          [ #Vat.dai[ABI_dst] <- Dai_dst +Int ABI_rad ]
              </storage>
              <origStorage> ORIG_STORAGE </origStorage>
              <nonce> _Nonce_Vat => ?_ </nonce>
            </account>
            <account>
              <acctID> 1 </acctID>
              <balance> ECREC_BAL </balance>
              <code> .ByteArray </code>
              <storage> _:Map </storage>
              <origStorage> _ </origStorage>
              <nonce> _ </nonce>
            </account>
            <account>
              <acctID> 2 </acctID>
              <balance> SHA256_BAL </balance>
              <code> .ByteArray </code>
              <storage> _:Map </storage>
              <origStorage> _ </origStorage>
              <nonce> _ </nonce>
            </account>
            <account>
              <acctID> 3 </acctID>
              <balance> RIP160_BAL </balance>
              <code> .ByteArray </code>
              <storage> _:Map </storage>
              <origStorage> _ </origStorage>
              <nonce> _ </nonce>
            </account>
            <account>
              <acctID> 4 </acctID>
              <balance> ID_BAL </balance>
              <code> .ByteArray </code>
              <storage> _:Map </storage>
              <origStorage> _ </origStorage>
              <nonce> _ </nonce>
            </account>
            <account>
              <acctID> 5 </acctID>
              <balance> MODEXP_BAL </balance>
              <code> .ByteArray </code>
              <storage> _:Map </storage>
              <origStorage> _ </origStorage>
              <nonce> _ </nonce>
            </account>
            <account>
              <acctID> 6 </acctID>
              <balance> ECADD_BAL </balance>
              <code> .ByteArray </code>
              <storage> _:Map </storage>
              <origStorage> _ </origStorage>
              <nonce> _ </nonce>
            </account>
            <account>
              <acctID> 7 </acctID>
              <balance> ECMUL_BAL </balance>
              <code> .ByteArray </code>
              <storage> _:Map </storage>
              <origStorage> _ </origStorage>
              <nonce> _ </nonce>
            </account>
            <account>
              <acctID> 8 </acctID>
              <balance> ECPAIRING_BAL </balance>
              <code> .ByteArray </code>
              <storage> _:Map </storage>
              <origStorage> _ </origStorage>
              <nonce> _ </nonce>
            </account>
            <account>
              <acctID> 9 </acctID>
              <balance> BLAKE2_BAL </balance>
              <code> .ByteArray </code>
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

     andBool (#rangeAddress(ABI_src)
     andBool (#rangeAddress(ABI_dst)
     andBool (#rangeUInt(256, ABI_rad)
     andBool (#rangeUInt(256, Dai_dst)
     andBool (#rangeUInt(256, Dai_src)
     andBool (#rangeUInt(256, May)
     andBool ((#sizeByteArray(CD) <=Int 1250000000)
     andBool ((ABI_src =/=Int ABI_dst)
     andBool (2300 <Int ( VGas -Int ( (#if ( ( Dai_src ==K ( Dai_src -Int ABI_rad ) ) orBool (notBool ( Junk_1 ==K Dai_src ) ) ) #then 0 #else 4200 #fi) +Int ( (#if ( ( Dai_dst ==K ( Dai_dst +Int ABI_rad ) ) orBool (notBool ( Junk_2 ==K Dai_dst ) ) ) #then 0 #else 4200 #fi) +Int ( (#if ( ( Junk_2 ==K 0 ) andBool (notBool ( ( Dai_dst ==K ( Dai_dst +Int ABI_rad ) ) orBool (notBool ( Junk_2 ==K Dai_dst ) ) ) ) ) #then 15000 #else 0 #fi) +Int 9543 ) ) ) )
     andBool (#rangeUInt(256, Junk_0)
     andBool (#rangeUInt(256, Junk_1)
     andBool (#rangeUInt(256, Junk_2)
     andBool ((((May ==Int 1 orBool ABI_src ==Int CALLER_ID)))
     andBool (((VCallValue ==Int 0))
     andBool ((#rangeUInt(256, Dai_src -Int ABI_rad))
     andBool ((#rangeUInt(256, Dai_dst +Int ABI_rad))))))))))))))))))

     andBool ((#lookup(STORAGE, #Vat.can[ABI_src][CALLER_ID]) ==Int May    )
     andBool ((#lookup(STORAGE, #Vat.dai[ABI_src]           ) ==Int Dai_src)
     andBool ((#lookup(STORAGE, #Vat.dai[ABI_dst]           ) ==Int Dai_dst))))

     andBool ((#lookup(ORIG_STORAGE, #Vat.can[ABI_src][CALLER_ID]) ==Int Junk_0)
     andBool ((#lookup(ORIG_STORAGE, #Vat.dai[ABI_src]           ) ==Int Junk_1)
     andBool ((#lookup(ORIG_STORAGE, #Vat.dai[ABI_dst]           ) ==Int Junk_2))))

endmodule
