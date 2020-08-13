requires "verification.k"

module CAT-EXHAUSTIVENESS-SPEC
  imports VERIFICATION

// Cat__exhaustiveness
rule [Cat..exhaustiveness]:
  <k> #execute ~> CONTINUATION => #halt ~> CONTINUATION </k>
  <exit-code> 1 </exit-code>
  <mode> NORMAL </mode>
  <schedule> ISTANBUL </schedule>
  <ethereum>
    <evm>
      <output> _ => VOutput </output>
      <statusCode> _ => EVMC_REVERT </statusCode>
      <endPC> _ => ?_ </endPC>
      <callStack> VCallStack </callStack>
      <interimStates> _ </interimStates>
      <touchedAccounts> _ => ?_ </touchedAccounts>
      <callState>
        <program> Cat_bin_runtime </program>
        <jumpDests> #computeValidJumpDests(Cat_bin_runtime) </jumpDests>
        <id> ACCT_ID </id>
        <caller> CALLER_ID </caller>
        <callData> VCallData </callData>
        <callValue> VCallValue </callValue>
        <wordStack> .WordStack => ?_ </wordStack>
        <localMem> .Map => ?_ </localMem>
        <pc> 0 => ?_ </pc>
        <gas> VGas => ?_ </gas>
        <memoryUsed> 0 => ?_ </memoryUsed>
        <callGas> _ => ?_ </callGas>
        <static> VStatic </static>
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
      <activeAccounts> VActiveAccounts </activeAccounts>
      <accounts> _ </accounts>
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
 andBool 1171202608 =/=Int #asWord(VCallData [ 0 .. 4 ])
 andBool 1763987465 =/=Int #asWord(VCallData [ 0 .. 4 ])
 andBool 2622662641 =/=Int #asWord(VCallData [ 0 .. 4 ])
 andBool 436938878  =/=Int #asWord(VCallData [ 0 .. 4 ])
 andBool 3572022915 =/=Int #asWord(VCallData [ 0 .. 4 ])
 andBool 3958158237 =/=Int #asWord(VCallData [ 0 .. 4 ])
 andBool 3647180086 =/=Int #asWord(VCallData [ 0 .. 4 ])
 andBool 2507842956 =/=Int #asWord(VCallData [ 0 .. 4 ])
 andBool 1710941022 =/=Int #asWord(VCallData [ 0 .. 4 ])
 andBool 911646327  =/=Int #asWord(VCallData [ 0 .. 4 ])
 andBool 1651291077 =/=Int #asWord(VCallData [ 0 .. 4 ])
 andBool 3207937467 =/=Int #asWord(VCallData [ 0 .. 4 ])
 andBool VGas >=Int 40000000

endmodule
