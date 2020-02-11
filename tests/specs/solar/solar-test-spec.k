requires "verification.k"
requires "evm-imp-specs.k"

module SOLAR-TEST-SPEC
  imports VERIFICATION
  imports EVM-IMP-SPECS

  rule
    <k> #saveEthereum         V_CONF_BEFORE
     ~> #saveOutput           V_OUT_BEFORE
     ~> #saveStorage  ACCT_ID V_STORAGE_BEFORE
     ~> #saveLog              V_LOG_BEFORE
     ~> #mkCallShortcut V_CONF_BEFORE CALLER_ID ACCT_ID
                        #abiCallData("add", #uint256(VALUE))       V_ADD_OUT
     ~> #assert #getStatusCode ==S  EVMC_SUCCESS
     ~> #assert #getStorage(ACCT_ID) =/=S #var(V_STORAGE_BEFORE)
     ~> #assert #getLog ==S (#var(V_LOG_BEFORE) +List ListItem(#abiEventLog(ACCT_ID, "TestEvent", #uint256(OLD_S), #uint256(SUM))))
     ~> #assert #getOutput ==S #var(V_ADD_OUT)
     ~> #assert #sizeByteArrayExp( #buf(33, SUM) ) ==S 33
     ~> #assert (true ||S false)  ==S true
     ~> #assert (true ||S false) =/=S false
     ~> #assert (true &&S false)  ==S false
     ~> #restoreEthereum V_CONF_BEFORE //TODO test that current config == what was saved initially.
     => . </k>
    <exit-code> 1 </exit-code>
    <mode> NORMAL </mode>
    <schedule> CONSTANTINOPLE </schedule>

    <ethereum>
      <evm>
        <output> _ => _ </output>
        <statusCode> _ => _ </statusCode>
        <callStack> _ </callStack>
        <interimStates> _ </interimStates>
        <touchedAccounts> _ => _ </touchedAccounts>

        <callState>
          <program> _ => _ </program>
          <jumpDests> _ => _ </jumpDests>

          <id> _ => _ </id> // contract owner
          <caller> _ => _ </caller> // who called this contract; in the begining, origin // msg.sender

          <callData> _ => _ </callData>

          <callValue> 0 </callValue>
          <wordStack> .WordStack => _ </wordStack>
          <localMem> .Map => _ </localMem>
          <pc> 0 => _ </pc>
          <gas> _ => _ </gas>
          <memoryUsed> 0 => _ </memoryUsed>
          <callGas> #gas(INITGAS, 0, 0) => _ </callGas>

          <static> false </static> // NOTE: non-static call
          <callDepth> CALL_DEPTH => _ </callDepth>
        </callState>

        <substate>
          <selfDestruct> _ </selfDestruct>
          <log> _:List => _ </log>
          <refund> _ => _ </refund>
        </substate>

        <gasPrice> _ </gasPrice>
        <origin> ORIGIN_ID </origin> // who fires tx
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
          <number> _ </number>
          <gasLimit> _ </gasLimit>
          <gasUsed> _ </gasUsed>
          <timestamp> _ </timestamp>
          <extraData> _ </extraData>
          <mixHash> _ </mixHash>
          <blockNonce> _ </blockNonce>

          <ommerBlockHeaders> _ </ommerBlockHeaders>
        </block>
      </evm>

      <network>
        <chainID> 0 </chainID>
        <activeAccounts> SetItem(ACCT_ID) _:Set </activeAccounts>

        <accounts>
          <account>
            <acctID> ACCT_ID </acctID>
            <balance> _ </balance>
            <code> #parseByteStack("0x6080604052348015600f57600080fd5b506004361060285760003560e01c80631003e2d214602d575b600080fd5b605660048036036020811015604157600080fd5b8101908080359060200190929190505050606c565b6040518082815260200191505060405180910390f35b6000806000549050600083600054019050806000819055507ff3ca124a697ba07e8c5e80bebcfcc48991fc16a63170e8a9206e30508960d0038282604051808381526020018281526020019250505060405180910390a1809250505091905056fea265627a7a72305820ed1e920507073a2945660ee1bec248841bfcaf34bbdce4b5eeb69be1a7dfb6d264736f6c634300050a0032") </code>
            <storage>     #hashedLocation("Solidity", 0, .IntList) |-> (OLD_S => _) _:Map </storage>
            <origStorage> #hashedLocation("Solidity", 0, .IntList) |-> (OLD_S => _) _:Map </origStorage>
            <nonce> _ </nonce>
          </account>
          ...
        </accounts>

        <txOrder> _ </txOrder>
        <txPending> _ </txPending>
        <messages> _ </messages>
      </network>
    </ethereum>
    <commandVars> .Map  => _ </commandVars>
    requires #rangeAddress(ACCT_ID)
     andBool #rangeAddress(CALLER_ID)
     andBool #rangeAddress(ORIGIN_ID)
     andBool #range(0 <= CALL_DEPTH < 1020) // providing enough room for 4 calls, including test calls
     andBool notBool (ACCT_ID in #precompiledAccounts(CONSTANTINOPLE))
     andBool #rangeUInt(256, OLD_S)
     andBool #rangeUInt(256, VALUE)
     andBool SUM   ==Int OLD_S +Int VALUE
     andBool #rangeUInt(256, SUM)
     andBool V_CONF_BEFORE            ==K String2Id("V_CONF_BEFORE")
     andBool V_OUT_BEFORE             ==K String2Id("V_OUT_BEFORE")
     andBool V_STORAGE_BEFORE         ==K String2Id("V_STORAGE_BEFORE")
     andBool V_LOG_BEFORE             ==K String2Id("V_LOG_BEFORE")
     andBool V_ADD_OUT                ==K String2Id("V_ADD_OUT")

endmodule
