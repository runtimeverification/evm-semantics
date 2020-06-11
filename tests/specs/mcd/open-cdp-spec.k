requires "rules.k"
requires "bin_runtime.k"

module VERIFICATION
  imports ETHEREUM-SIMULATION
  imports EVM
  imports RULES
  imports BIN_RUNTIME

  // step 132 - could not simplify #sizeWordStack(#padToWidth(32, _), _) or #sizeWordStack(_ ++ _, _)
  rule #sizeWordStack(WS1 ++ WS2, N) => #sizeWordStack(WS1) +Int #sizeWordStack(WS2) +Int N
  rule #sizeWordStack(#padToWidth(32, #asByteStack(I)), N) => N +Int 32 requires 0 <=Int I andBool I <Int pow256

  // step 164 - sizeWordStack(_, _) + 68 <Int 4
  rule 0 <=Int #sizeWordStack ( _ , _ ) => true [smt-lemma]

  // step 262 - #asWord(96 : 144 : 222 : 197 : takeWordStack(28, #padToWidth(32, #asByteStack(ABI_ilk)))) >>Int 224 <Int 2160673182
  rule #asWord(WS) >>Int M => #asWord(#take(#sizeWordStack(WS) -Int (M /Int 8), WS)) requires 0 <=Int M andBool M modInt 8 ==Int 0
  rule #sizeWordStack(#take(M, WS), N) => M +Int N requires 0 <=Int M

  // step 730 - #unsigned(#sizeWordStack(CD, 0) +Int 64) <Int 64
  rule #unsigned(#sizeWordStack(WS, N) +Int M) => #sizeWordStack(WS, N) +Int M requires 0 <=Int M andBool #sizeWordStack(WS, N) +Int M <Int maxSInt256

  // step 811 - #asWord(#padToWidth(32, #asByteStack(ABI_ilk)))
  rule #asWord(#padToWidth(32, #asByteStack(VALUE))) => VALUE requires 0 <=Int VALUE andBool VALUE <Int pow256

  // step 1188 - ((maxUInt160 & #asWord(takeWordStack(32,
  //                                                        dropWordStack(1,
  //                                                        dropWordStack(1,
  //                                                        dropWordStack(1,
  //                                                        dropWordStack(1,
  //                                                        dropWordStack(1,
  //                                                        dropWordStack(1,
  //                                                        dropWordStack(1,
  //                                                        dropWordStack(1,
  //                                                        dropWordStack(1,
  //                                                        dropWordStack(1,
  //                                                        dropWordStack(1,
  //                                                        dropWordStack(1,
  //                                                        dropWordStack(1,
  //                                                        dropWordStack(1,
  //                                                        dropWordStack(1,
  //                                                        dropWordStack(1,
  //                                                        dropWordStack(1,
  //                                                        dropWordStack(1,
  //                                                        dropWordStack(1,
  //                                                        dropWordStack(1,
  //                                                        dropWordStack(1,
  //                                                        dropWordStack(1,
  //                                                        dropWordStack(1,
  //                                                        dropWordStack(1,
  //                                                        dropWordStack(1,
  //                                                        dropWordStack(1,
  //                                                        dropWordStack(1,
  //                                                        dropWordStack(1,
  //                                                        dropWordStack(1,
  //                                                        dropWordStack(1,
  //                                                        dropWordStack(1, (
  //                                                        dropWordStack(1, #padToWidth(32 , #asByteStack(ABI_ilk))) ++ (#padToWidth(32, #asByteStack(ABI_usr)) ++ CD)))))))))))))))))))))))))) )))))))))) ==K 0)
  rule #drop(N, WS ++ WS') => #drop(N, WS) ++ WS' requires N <=Int #sizeWordStack(WS)
  rule #sizeWordStack(#drop(N, WS), M) => M +Int #sizeWordStack(WS) -Int N requires N <=Int #sizeWordStack(WS)
  rule WS ++ WS' => WS' requires #sizeWordStack(WS) ==Int 0

  // step 1406 - #lookup(_39 [ 0                      <- Vat   ]
  //                         [ 1                      <- Cdpi  ]
  //                         [ hash2(Cdpi + 1, 2)     <- 0     ]
  //                         [ hash2(ABI_usr , 7)     <- Last  ]
  //                         [ hash2(ABI_usr , 8)     <- Count ]
  //                         [ hash2(Cdpi + 1, 4)     <- Own   ]
  //                         [ hash2(Cdpi + 1, 5)     <- Ilk   ]
  //                         [ hash2(ABI_usr , 6)     <- First ]
  //                         [ hash2(Cdpi + 1, 3)     <- Prev  ]
  //                         [ hash2(Last    , 3) + 1 <- Next  ]
  //                    , 1
  //                    )
  rule #lookup(MAP [ KEY <- VALUE ], KEY') => #lookup(MAP, KEY') requires KEY =/=K KEY'
  rule #lookup(MAP [ KEY <- VALUE ], KEY') => VALUE              requires KEY  ==K KEY'
  rule hash2(_, _)        ==K 1 => false
  rule hash2(_, _) +Int I ==K 1 => false requires I =/=Int 0
  rule hash2(_, _)        ==K 0 => false
  rule hash2(_, _) +Int I ==K 0 => false requires I =/=Int 0

  // step 2177 - DEST in DESTS
  rule #computeValidJumpDests(#padToWidth(32, #asByteStack(ADDR)) => .WordStack, I => I +Int 32, RESULT) requires 0 <=Int ADDR andBool ADDR <Int pow256

  // step 3165 - #range(MAP [ N := #padToWidth(_, _) ] [ N' <- _ ], END, WIDTH, _)
  rule #range(MAP [ N := BA:ByteArray ] => MAP, END, WIDTH, WS) requires END <Int N orBool N +Int WIDTH +Int #sizeWordStack(BA) -Int 1 <=Int END
  rule #range(MAP [ N <- _            ] => MAP, END, WIDTH, WS) requires END <Int N orBool N +Int WIDTH                                <=Int END
endmodule

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
      <output> _ => #buf(32, Cdpi +Int 1) </output>
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
          <storage>
            _:Map
          [#Vat.can[Urn][ACCT_ID] <- (0) => 1]
           </storage>
          <origStorage>
            _:Map
          [#Vat.can[Urn][ACCT_ID] <- (Junk_0)]
           </origStorage>
          <nonce> Nonce_Vat => ?_ </nonce>
        </account>
        <account>
          <acctID> ACCT_ID </acctID>
          <balance> ACCT_ID_balance </balance>
          <code> DssCdpManager_bin_runtime </code>
          <storage>
            _:Map
          [#DssCdpManager.vat <- (Vat) => Vat]
          [#DssCdpManager.cdpi <- (Cdpi) => Cdpi +Int 1]
          [#DssCdpManager.urns[Cdpi +Int 1] <- (0) => Urn]
          [#DssCdpManager.last[ABI_usr] <- (Last) => Cdpi +Int 1]
          [#DssCdpManager.count[ABI_usr] <- (Count) => Count +Int 1]
          [#DssCdpManager.owns[Cdpi +Int 1] <- (Own) => ABI_usr]
          [#DssCdpManager.ilks[Cdpi +Int 1] <- (Ilk) => ABI_ilk]
          [#DssCdpManager.first[ABI_usr] <- (First) => #if First ==Int 0 #then Cdpi +Int 1 #else First #fi]
          [#DssCdpManager.list[Cdpi +Int 1].prev <- (Prev) => #if Last =/=Int 0 #then Last #else Prev #fi]
          [#DssCdpManager.list[Last].next <- (Next) => #if Last =/=Int 0 #then Cdpi +Int 1 #else Next #fi]
           </storage>
          <origStorage>
            _:Map
          [#DssCdpManager.vat <- (Junk_1)]
          [#DssCdpManager.cdpi <- (Junk_2)]
          [#DssCdpManager.urns[Cdpi +Int 1] <- (Junk_3)]
          [#DssCdpManager.last[ABI_usr] <- (Junk_4)]
          [#DssCdpManager.count[ABI_usr] <- (Junk_5)]
          [#DssCdpManager.owns[Cdpi +Int 1] <- (Junk_6)]
          [#DssCdpManager.ilks[Cdpi +Int 1] <- (Junk_7)]
          [#DssCdpManager.first[ABI_usr] <- (Junk_8)]
          [#DssCdpManager.list[Cdpi +Int 1].prev <- (Junk_9)]
          [#DssCdpManager.list[Last].next <- (Junk_10)]
           </origStorage>
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

// Vat_hope
rule [Vat.hope.pass]:
  <k> #execute ~> CONTINUATION => #halt ~> CONTINUATION </k>
  <exit-code> 1 </exit-code>
  <mode> NORMAL </mode>
  <schedule> ISTANBUL </schedule>
  <ethereum>
    <evm>
      <output> .WordStack </output>
      <statusCode> _ => EVMC_SUCCESS </statusCode>
      <endPC> _ => ?_ </endPC>
      <callStack> VCallStack </callStack>
      <interimStates> _ </interimStates>
      <touchedAccounts> _ => ?_ </touchedAccounts>
      <callState>
        <program> Vat_bin_runtime </program>
        <jumpDests> #computeValidJumpDests(Vat_bin_runtime) </jumpDests>
        <id> ACCT_ID </id>
        <caller> CALLER_ID </caller>
        <callData> #abiCallData("hope", #address(ABI_usr)) ++ CD => ?_ </callData>
        <callValue> VCallValue </callValue>
        <wordStack> .WordStack => ?_ </wordStack>
        <localMem> .Map => ?_ </localMem>
        <pc> 0 => ?_ </pc>
        <gas> VGas => ( VGas -Int ( (#if ( ( Junk_0 ==K 1 ) orBool (notBool ( Junk_1 ==K Junk_0 ) ) ) #then 0 #else 4200 #fi) +Int ( (#if ( ( Junk_1 ==K 0 ) andBool (notBool ( ( Junk_0 ==K 1 ) orBool (notBool ( Junk_1 ==K Junk_0 ) ) ) ) ) #then 15000 #else 0 #fi) +Int 5624 ) ) ) </gas>
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
      <activeAccounts> SetItem(ACCT_ID)
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
          <acctID> ACCT_ID </acctID>
          <balance> ACCT_ID_balance </balance>
          <code> Vat_bin_runtime </code>
          <storage>
            _:Map
          [#Vat.can[CALLER_ID][ABI_usr] <- (Junk_0) => 1]
           </storage>
          <origStorage>
            _:Map
          [#Vat.can[CALLER_ID][ABI_usr] <- (Junk_1)]
           </origStorage>
          <nonce> Nonce_Vat => ?_ </nonce>
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

  andBool (#rangeAddress(ABI_usr)
  andBool (0 <=Int #sizeByteArray(CD)
  andBool (#sizeByteArray(CD) <=Int 1250000000
  andBool (2300 <Int ( VGas -Int ( (#if ( ( Junk_0 ==K 1 ) orBool (notBool ( Junk_1 ==K Junk_0 ) ) ) #then 0 #else 4200 #fi) +Int ( (#if ( ( Junk_1 ==K 0 ) andBool (notBool ( ( Junk_0 ==K 1 ) orBool (notBool ( Junk_1 ==K Junk_0 ) ) ) ) ) #then 15000 #else 0 #fi) +Int 5624 ) ) )
  andBool (#rangeUInt(256, Junk_0)
  andBool (#rangeUInt(256, Junk_1)
  andBool ((VCallValue ==Int 0))))))))
[trusted]


endmodule
