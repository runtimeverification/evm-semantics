requires "verification.k"

module OPEN-CDP-SPEC
  imports VERIFICATION

    // DssCdpManager_open
    rule [DssCdpManager.open.pass.rough]:
      <k> #execute ~> CONTINUATION => #halt ~> CONTINUATION </k>
      <exit-code> 1 </exit-code>
      <mode> NORMAL </mode>
      <schedule> ISTANBUL </schedule>
      <ethereum>
        <evm>
          <output> _ => #padToWidth(32, #asByteStack(Cdpi +Int 1)) </output>
          <statusCode> _ => EVMC_SUCCESS </statusCode>
          <endPC> _ => ?_ </endPC>
          <callStack> VCallStack </callStack>
          <interimStates> _ </interimStates>
          <touchedAccounts> _ => ?_ </touchedAccounts>
          <callState>
            <program> DssCdpManager_bin_runtime </program>
            <jumpDests> #computeValidJumpDests(DssCdpManager_bin_runtime) </jumpDests>
            <id> ACCT_ID </id>
            <caller> CALLER_ID </caller>
            <callData> #abiCallData("open", #bytes32(ABI_ilk), #address(ABI_usr)) ++ CD => ?_ </callData>
            <callValue> VCallValue </callValue>
            <wordStack> .WordStack => ?_ </wordStack>
            <localMem> .Map => ?_ </localMem>
            <pc> 0 => ?_ </pc>
            <gas> VGas => ?_ </gas>
            <memoryUsed> 0 => ?_ </memoryUsed>
            <callGas> _ => ?_ </callGas>
            <static> false </static>
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
          <activeAccounts> SetItem(Urn)
          SetItem(Vat)
          SetItem(ACCT_ID)
          SetItem(1)
          SetItem(2)
          SetItem(3)
          SetItem(4)
          SetItem(5)
          SetItem(6)
          SetItem(7)
          SetItem(8) _ </activeAccounts>
          <accounts>
            <account>
              <acctID> Urn </acctID>
              <balance> Urn_balance </balance>
              <code> .WordStack => UrnHandler_bin_runtime </code>
              <storage>
               .Map => (.Map

              )
               </storage>
              <origStorage>
               .Map
               </origStorage>
              <nonce> 0 => 1 </nonce>
            </account>
            <account>
              <acctID> Vat </acctID>
              <balance> Vat_balance </balance>
              <code> Vat_bin_runtime </code>
              <storage> Vat_Storage => ?Vat_Storage </storage>
              <origStorage> Vat_OrigStorage </origStorage>
              <nonce> Nonce_Vat => ?_ </nonce>
            </account>
            <account>
              <acctID> ACCT_ID </acctID>
              <balance> ACCT_ID_balance </balance>
              <code> DssCdpManager_bin_runtime </code>
              <storage> ACCT_ID_Storage => ?ACCT_ID_Storage </storage>
              <origStorage> ACCT_ID_OrigStorage </origStorage>
              <nonce> Nonce_DssCdpManager => ?_ </nonce>
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
     andBool (#rangeAddress(ABI_usr)
     andBool (#rangeAddress(Vat)
     andBool (#rangeUInt(256, Cdpi)
     andBool (#rangeAddress(Urn)
     andBool (#rangeUInt(256, Last)
     andBool (#rangeUInt(256, Count)
     andBool (#rangeAddress(Own)
     andBool (#rangeBytes(32, Ilk)
     andBool (#rangeUInt(256, First)
     andBool (#rangeUInt(256, Prev)
     andBool (#rangeUInt(256, Next)
     andBool (#rangeUInt(256, Urn_balance)
     andBool (#rangeUInt(256, Vat_balance)
     andBool ((0 <=Int #sizeByteArray(CD))
     andBool ((#sizeByteArray(CD) <=Int 1250000000)
     andBool ((#notPrecompileAddress(Vat))
     andBool ((#notPrecompileAddress(Urn))
     andBool ((#notPrecompileAddress(Own))
     andBool ((ACCT_ID =/=Int Urn)
     andBool ((ACCT_ID =/=Int Vat)
     andBool ((#newAddr(ACCT_ID, Nonce_DssCdpManager) ==Int Urn)
     andBool ((#newAddr(ACCT_ID, Nonce_DssCdpManager) =/=Int Vat)
     andBool (VGas >=Int 3000000
     andBool (#rangeUInt(256, Junk_0)
     andBool (#rangeUInt(256, Junk_1)
     andBool (#rangeUInt(256, Junk_2)
     andBool (#rangeUInt(256, Junk_3)
     andBool (#rangeUInt(256, Junk_4)
     andBool (#rangeUInt(256, Junk_5)
     andBool (#rangeUInt(256, Junk_6)
     andBool (#rangeUInt(256, Junk_7)
     andBool (#rangeUInt(256, Junk_8)
     andBool (#rangeUInt(256, Junk_9)
     andBool (#rangeUInt(256, Junk_10)
     andBool (((#rangeUInt(256, Cdpi +Int 1)))
     andBool (((#rangeUInt(256, Count +Int 1)))
     andBool ((VCallValue ==Int 0)
     andBool ((ABI_usr =/=Int 0)
     andBool ((VCallDepth <Int 1023)))))))))))))))))))))))))))))))))))))))))

     andBool (#lookup(Vat_Storage, #Vat.can[Urn][ACCT_ID]) ==Int 0)

     andBool (#lookup(Vat_OrigStorage, #Vat.can[Urn][ACCT_ID]) ==Int Junk_0)

     andBool ((#lookup(ACCT_ID_Storage, #DssCdpManager.vat)                    ==Int Vat)
     andBool ((#lookup(ACCT_ID_Storage, #DssCdpManager.cdpi)                   ==Int Cdpi)
     andBool ((#lookup(ACCT_ID_Storage, #DssCdpManager.urns[Cdpi +Int 1])      ==Int 0)
     andBool ((#lookup(ACCT_ID_Storage, #DssCdpManager.last[ABI_usr])          ==Int Last)
     andBool ((#lookup(ACCT_ID_Storage, #DssCdpManager.count[ABI_usr])         ==Int Count)
     andBool ((#lookup(ACCT_ID_Storage, #DssCdpManager.owns[Cdpi +Int 1])      ==Int Own)
     andBool ((#lookup(ACCT_ID_Storage, #DssCdpManager.ilks[Cdpi +Int 1])      ==Int Ilk)
     andBool ((#lookup(ACCT_ID_Storage, #DssCdpManager.first[ABI_usr])         ==Int First)
     andBool ((#lookup(ACCT_ID_Storage, #DssCdpManager.list[Cdpi +Int 1].prev) ==Int Prev)
     andBool ((#lookup(ACCT_ID_Storage, #DssCdpManager.list[Last].next)        ==Int Next)))))))))))

     andBool ((#lookup(ACCT_ID_OrigStorage, #DssCdpManager.vat)                    ==Int Junk_1)
     andBool ((#lookup(ACCT_ID_OrigStorage, #DssCdpManager.cdpi)                   ==Int Junk_2)
     andBool ((#lookup(ACCT_ID_OrigStorage, #DssCdpManager.urns[Cdpi +Int 1])      ==Int Junk_3)
     andBool ((#lookup(ACCT_ID_OrigStorage, #DssCdpManager.last[ABI_usr])          ==Int Junk_4)
     andBool ((#lookup(ACCT_ID_OrigStorage, #DssCdpManager.count[ABI_usr])         ==Int Junk_5)
     andBool ((#lookup(ACCT_ID_OrigStorage, #DssCdpManager.owns[Cdpi +Int 1])      ==Int Junk_6)
     andBool ((#lookup(ACCT_ID_OrigStorage, #DssCdpManager.ilks[Cdpi +Int 1])      ==Int Junk_7)
     andBool ((#lookup(ACCT_ID_OrigStorage, #DssCdpManager.first[ABI_usr])         ==Int Junk_8)
     andBool ((#lookup(ACCT_ID_OrigStorage, #DssCdpManager.list[Cdpi +Int 1].prev) ==Int Junk_9)
     andBool ((#lookup(ACCT_ID_OrigStorage, #DssCdpManager.list[Last].next)        ==Int Junk_10)))))))))))

     ensures (#lookup(?Vat_Storage, #Vat.can[Urn][ACCT_ID]) ==Int 1)

     andBool ((#lookup(?ACCT_ID_Storage, #DssCdpManager.vat)                    ==Int Vat)
     andBool ((#lookup(?ACCT_ID_Storage, #DssCdpManager.cdpi)                   ==Int Cdpi +Int 1)
     andBool ((#lookup(?ACCT_ID_Storage, #DssCdpManager.urns[Cdpi +Int 1])      ==Int Urn)
     andBool ((#lookup(?ACCT_ID_Storage, #DssCdpManager.last[ABI_usr])          ==Int Cdpi +Int 1)
     andBool ((#lookup(?ACCT_ID_Storage, #DssCdpManager.count[ABI_usr])         ==Int Count +Int 1)
     andBool ((#lookup(?ACCT_ID_Storage, #DssCdpManager.owns[Cdpi +Int 1])      ==Int ABI_usr)
     andBool ((#lookup(?ACCT_ID_Storage, #DssCdpManager.ilks[Cdpi +Int 1])      ==Int ABI_ilk)
     andBool ((#lookup(?ACCT_ID_Storage, #DssCdpManager.first[ABI_usr])         ==Int #if First ==Int 0 #then Cdpi +Int 1 #else First #fi)
     andBool ((#lookup(?ACCT_ID_Storage, #DssCdpManager.list[Cdpi +Int 1].prev) ==Int #if Last =/=Int 0 #then Last #else Prev #fi)
     andBool ((#lookup(?ACCT_ID_Storage, #DssCdpManager.list[Last].next)        ==Int #if Last =/=Int 0 #then Cdpi +Int 1 #else Next #fi)))))))))))
endmodule
