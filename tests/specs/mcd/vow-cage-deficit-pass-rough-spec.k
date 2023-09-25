requires "vow-arithmetic-spec.k"
requires "vat-dai-pass-spec.k"
requires "vat-sin-pass-spec.k"
requires "vat-heal-pass-spec.k"
requires "flapper-cage-pass-spec.k"
requires "flopper-cage-pass-spec.k"

module VOW-CAGE-DEFICIT-PASS-ROUGH-SPEC
    imports VOW-ARITHMETIC-SPEC
    imports VAT-DAI-PASS-SPEC
    imports VAT-SIN-PASS-SPEC
    imports VAT-HEAL-PASS-SPEC
    imports FLAPPER-CAGE-PASS-SPEC
    imports FLOPPER-CAGE-PASS-SPEC

    claim [Vow.cage-deficit.pass.rough]:
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
            <program> Vow_bin_runtime </program>
            <jumpDests> #computeValidJumpDests(Vow_bin_runtime) </jumpDests>
            <id> ACCT_ID </id>
            <caller> CALLER_ID </caller>
            <callData> #abiCallData("cage", .TypedArgs) +Bytes CD => ?_ </callData>
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
            <withdrawalsRoot> _ </withdrawalsRoot>
          </block>
        </evm>
        <network>
          <chainID> VChainId </chainID>
          <accounts>
            <account>
              <acctID> ACCT_ID </acctID>
              <balance> ACCT_ID_balance </balance>
              <code> Vow_bin_runtime </code>
              <storage> ACCT_ID_STORAGE => ACCT_ID_STORAGE [ #Vow.live <- 0 ] [ #Vow.Sin <- 0 ] [ #Vow.Ash <- 0 ] </storage>
              <origStorage> ACCT_ID_ORIG_STORAGE </origStorage>
              <nonce> Nonce_Vow </nonce>
            </account>
            <account>
              <acctID> Vat </acctID>
              <balance> Vat_balance </balance>
              <code> Vat_bin_runtime </code>
              <storage> Vat_STORAGE => Vat_STORAGE [ #Vat.dai[Flapper] <- 0 ] [ #Vat.dai[ACCT_ID] <- 0 ] [ #Vat.sin[ACCT_ID] <- Sin_v -Int (Dai_v +Int Dai_f) ] [ #Vat.vice <- Vice -Int (Dai_v +Int Dai_f) ] [ #Vat.debt <- Debt -Int (Dai_v +Int Dai_f) ] </storage>
              <origStorage> Vat_ORIG_STORAGE </origStorage>
              <nonce> Nonce_Vat </nonce>
            </account>
            <account>
              <acctID> Flapper </acctID>
              <balance> Flapper_balance </balance>
              <code> Flapper_bin_runtime </code>
              <storage> Flapper_STORAGE => Flapper_STORAGE [ #Flapper.live <- 0 ] </storage>
              <origStorage> Flapper_ORIG_STORAGE </origStorage>
              <nonce> Nonce_Flapper </nonce>
            </account>
            <account>
              <acctID> Flopper </acctID>
              <balance> Flopper_balance </balance>
              <code> Flopper_bin_runtime </code>
              <storage> Flopper_STORAGE => Flopper_STORAGE [ #Flopper.live <- 0 ] [ #Flopper.vow <- ACCT_ID ] </storage>
              <origStorage> Flopper_ORIG_STORAGE </origStorage>
              <nonce> Nonce_Flopper </nonce>
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
       andBool #rangeNonce(Nonce_Vow)
       andBool #rangeNonce(Nonce_Vat)
       andBool #rangeNonce(Nonce_Flapper)
       andBool #rangeNonce(Nonce_Flopper)

       andBool (#rangeAddress(Vat)
       andBool (#rangeAddress(Flapper)
       andBool (#rangeAddress(Flopper)
       andBool (#rangeAddress(FlapVat)
       andBool (#rangeUInt(256, MayFlap)
       andBool (#rangeUInt(256, MayFlop)
       andBool (#rangeUInt(256, Dai_v)
       andBool (#rangeUInt(256, Sin_v)
       andBool (#rangeUInt(256, Dai_f)
       andBool (#rangeUInt(256, Debt)
       andBool (#rangeUInt(256, Vice)
       andBool (#rangeUInt(256, Live)
       andBool (#rangeUInt(256, Sin)
       andBool (#rangeUInt(256, Ash)
       andBool (#rangeUInt(256, FlapLive)
       andBool (#rangeUInt(256, FlopLive)
       andBool (#rangeAddress(FlopVow)
       andBool (#rangeUInt(256, Vat_balance)
       andBool (#rangeUInt(256, Flapper_balance)
       andBool (#rangeUInt(256, Flopper_balance)
       andBool ((lengthBytes(CD) <=Int 1250000000)
       andBool ((#notPrecompileAddress(Vat))
       andBool ((#notPrecompileAddress(Flapper))
       andBool ((#notPrecompileAddress(Flopper))
       andBool ((#notPrecompileAddress(FlapVat))
       andBool ((#notPrecompileAddress(FlopVow))
       andBool ((ACCT_ID =/=Int Vat)
       andBool ((ACCT_ID =/=Int Flapper)
       andBool ((ACCT_ID =/=Int Flopper)
       andBool ((Dai_v +Int Dai_f <Int Sin_v)
       andBool ((Flapper =/=Int ACCT_ID)
       andBool ((Flapper =/=Int Vat)
       andBool ((Flopper =/=Int ACCT_ID)
       andBool ((Flopper =/=Int Vat)
       andBool ((Flopper =/=Int Flapper)
       andBool ((FlapVat ==Int  Vat)
       andBool ((Vat =/=Int 0)
       andBool ((Flapper =/=Int 0)
       andBool ((Flopper =/=Int 0)
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
       andBool (#rangeUInt(256, Junk_11)
       andBool (#rangeUInt(256, Junk_12)
       andBool (#rangeUInt(256, Junk_13)
       andBool (#rangeUInt(256, Junk_14)
       andBool (#rangeUInt(256, Junk_15)
       andBool (#rangeUInt(256, Junk_16)
       andBool (#rangeUInt(256, Junk_17)
       andBool (#rangeUInt(256, Junk_18)
       andBool (#rangeUInt(256, Junk_19)
       andBool (((VCallValue ==Int 0))
       andBool (((VCallDepth <Int 1023))
       andBool (((Live ==Int 1))
       andBool (((Can ==Int 1))
       andBool (((MayFlap ==Int 1))
       andBool (((MayFlop ==Int 1))
       andBool ((#rangeUInt(256, Debt -Int (Dai_v +Int Dai_f)))
       andBool ((#rangeUInt(256, Vice -Int (Dai_v +Int Dai_f))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))

       andBool #lookup(ACCT_ID_STORAGE, #Vow.wards[CALLER_ID]) ==Int Can
       andBool #lookup(ACCT_ID_STORAGE, #Vow.vat) ==Int Vat
       andBool #lookup(ACCT_ID_STORAGE, #Vow.flopper) ==Int Flopper
       andBool #lookup(ACCT_ID_STORAGE, #Vow.flapper) ==Int Flapper
       andBool #lookup(ACCT_ID_STORAGE, #Vow.live) ==Int Live
       andBool #lookup(ACCT_ID_STORAGE, #Vow.Sin) ==Int Sin
       andBool #lookup(ACCT_ID_STORAGE, #Vow.Ash) ==Int Ash
       andBool #lookup(ACCT_ID_ORIG_STORAGE, #Vow.wards[CALLER_ID]) ==Int Junk_0
       andBool #lookup(ACCT_ID_ORIG_STORAGE, #Vow.vat) ==Int Junk_1
       andBool #lookup(ACCT_ID_ORIG_STORAGE, #Vow.flopper) ==Int Junk_2
       andBool #lookup(ACCT_ID_ORIG_STORAGE, #Vow.flapper) ==Int Junk_3
       andBool #lookup(ACCT_ID_ORIG_STORAGE, #Vow.live) ==Int Junk_4
       andBool #lookup(ACCT_ID_ORIG_STORAGE, #Vow.Sin) ==Int Junk_5
       andBool #lookup(ACCT_ID_ORIG_STORAGE, #Vow.Ash) ==Int Junk_6
       andBool #Vow.wards[CALLER_ID] =/=Int #Vow.vat
       andBool #Vow.wards[CALLER_ID] =/=Int #Vow.flopper
       andBool #Vow.wards[CALLER_ID] =/=Int #Vow.flapper
       andBool #Vow.wards[CALLER_ID] =/=Int #Vow.live
       andBool #Vow.wards[CALLER_ID] =/=Int #Vow.Sin
       andBool #Vow.wards[CALLER_ID] =/=Int #Vow.Ash
       andBool #Vow.vat =/=Int #Vow.flopper
       andBool #Vow.vat =/=Int #Vow.flapper
       andBool #Vow.vat =/=Int #Vow.live
       andBool #Vow.vat =/=Int #Vow.Sin
       andBool #Vow.vat =/=Int #Vow.Ash
       andBool #Vow.flopper =/=Int #Vow.flapper
       andBool #Vow.flopper =/=Int #Vow.live
       andBool #Vow.flopper =/=Int #Vow.Sin
       andBool #Vow.flopper =/=Int #Vow.Ash
       andBool #Vow.flapper =/=Int #Vow.live
       andBool #Vow.flapper =/=Int #Vow.Sin
       andBool #Vow.flapper =/=Int #Vow.Ash
       andBool #Vow.live =/=Int #Vow.Sin
       andBool #Vow.live =/=Int #Vow.Ash
       andBool #Vow.Sin =/=Int #Vow.Ash
       andBool #lookup(Vat_STORAGE, #Vat.can[Flapper][Flapper]) ==Int Junk_7
       andBool #lookup(Vat_STORAGE, #Vat.dai[Flapper]) ==Int Dai_f
       andBool #lookup(Vat_STORAGE, #Vat.dai[ACCT_ID]) ==Int Dai_v
       andBool #lookup(Vat_STORAGE, #Vat.sin[ACCT_ID]) ==Int Sin_v
       andBool #lookup(Vat_STORAGE, #Vat.vice) ==Int Vice
       andBool #lookup(Vat_STORAGE, #Vat.debt) ==Int Debt
       andBool #lookup(Vat_ORIG_STORAGE, #Vat.can[Flapper][Flapper]) ==Int Junk_8
       andBool #lookup(Vat_ORIG_STORAGE, #Vat.dai[Flapper]) ==Int Junk_9
       andBool #lookup(Vat_ORIG_STORAGE, #Vat.dai[ACCT_ID]) ==Int Junk_10
       andBool #lookup(Vat_ORIG_STORAGE, #Vat.sin[ACCT_ID]) ==Int Junk_11
       andBool #lookup(Vat_ORIG_STORAGE, #Vat.vice) ==Int Junk_12
       andBool #lookup(Vat_ORIG_STORAGE, #Vat.debt) ==Int Junk_13
       andBool #Vat.can[Flapper][Flapper] =/=Int #Vat.dai[Flapper]
       andBool #Vat.can[Flapper][Flapper] =/=Int #Vat.dai[ACCT_ID]
       andBool #Vat.can[Flapper][Flapper] =/=Int #Vat.sin[ACCT_ID]
       andBool #Vat.can[Flapper][Flapper] =/=Int #Vat.vice
       andBool #Vat.can[Flapper][Flapper] =/=Int #Vat.debt
       andBool #Vat.dai[Flapper] =/=Int #Vat.dai[ACCT_ID]
       andBool #Vat.dai[Flapper] =/=Int #Vat.sin[ACCT_ID]
       andBool #Vat.dai[Flapper] =/=Int #Vat.vice
       andBool #Vat.dai[Flapper] =/=Int #Vat.debt
       andBool #Vat.dai[ACCT_ID] =/=Int #Vat.sin[ACCT_ID]
       andBool #Vat.dai[ACCT_ID] =/=Int #Vat.vice
       andBool #Vat.dai[ACCT_ID] =/=Int #Vat.debt
       andBool #Vat.sin[ACCT_ID] =/=Int #Vat.vice
       andBool #Vat.sin[ACCT_ID] =/=Int #Vat.debt
       andBool #Vat.vice =/=Int #Vat.debt
       andBool #lookup(Flapper_STORAGE, #Flapper.wards[ACCT_ID]) ==Int MayFlap
       andBool #lookup(Flapper_STORAGE, #Flapper.vat) ==Int FlapVat
       andBool #lookup(Flapper_STORAGE, #Flapper.live) ==Int FlapLive
       andBool #lookup(Flapper_ORIG_STORAGE, #Flapper.wards[ACCT_ID]) ==Int Junk_14
       andBool #lookup(Flapper_ORIG_STORAGE, #Flapper.vat) ==Int Junk_15
       andBool #lookup(Flapper_ORIG_STORAGE, #Flapper.live) ==Int Junk_16
       andBool #Flapper.wards[ACCT_ID] =/=Int #Flapper.vat
       andBool #Flapper.wards[ACCT_ID] =/=Int #Flapper.live
       andBool #Flapper.vat =/=Int #Flapper.live
       andBool #lookup(Flopper_STORAGE, #Flopper.wards[ACCT_ID]) ==Int MayFlop
       andBool #lookup(Flopper_STORAGE, #Flopper.live) ==Int FlopLive
       andBool #lookup(Flopper_STORAGE, #Flopper.vow) ==Int FlopVow
       andBool #lookup(Flopper_ORIG_STORAGE, #Flopper.wards[ACCT_ID]) ==Int Junk_17
       andBool #lookup(Flopper_ORIG_STORAGE, #Flopper.live) ==Int Junk_18
       andBool #lookup(Flopper_ORIG_STORAGE, #Flopper.vow) ==Int Junk_19
       andBool #Flopper.wards[ACCT_ID] =/=Int #Flopper.live
       andBool #Flopper.wards[ACCT_ID] =/=Int #Flopper.vow
       andBool #Flopper.live =/=Int #Flopper.vow

    [depends(VOW-ARITHMETIC-SPEC.Vow.minuu.pass,VAT-DAI-PASS-SPEC.Vat.dai.pass,VAT-SIN-PASS-SPEC.Vat.sin.pass,VAT-HEAL-PASS-SPEC.Vat.heal.pass,FLAPPER-CAGE-PASS-SPEC.Flapper.cage.pass,FLOPPER-CAGE-PASS-SPEC.Flopper.cage.pass)]

endmodule
