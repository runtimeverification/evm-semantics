requires "imp-specs-abstract-semantics.k"
requires "evm-imp-specs.k"
requires "verification.k"

module IMP-SPECS-TEST-SPEC
  imports IMP-SPECS-ABSTRACT-SEMANTICS
  imports EVM-IMP-SPECS
  imports VERIFICATION

  rule
    <k> #saveEthereum         V_CONF_BEFORE
     ~> #saveOutput           V_OUT_BEFORE
     ~> #saveStorage  ACCT_ID V_STORAGE_BEFORE
     ~> #saveLog              V_LOG_BEFORE
     ~> #mkCallShortcut V_CONF_BEFORE CALLER_ID ACCT_ID
                        #abiCallData("add", #uint256(VALUE))       V_ADD_OUT
     ~> #assert #getStatusCode ==S  EVMC_SUCCESS
     //Cannot verify due to limitations in Map unification. Lemmas don't help.
     //~> #assert #getStorage(ACCT_ID) =/=S #var(V_STORAGE_BEFORE)
     ~> #assume SUM:Int ==S OLD_S +Int VALUE
     ~> #assert #getLog ==S (#var(V_LOG_BEFORE) +List ListItem(#abiEventLog(ACCT_ID, "TestEvent", #uint256(OLD_S), #uint256(SUM))))
     ~> #assert #getOutput ==S #var(V_ADD_OUT)
     ~> #assert #sizeByteArrayExp( #buf(33, SUM) ) ==S 33
     ~> #assert (true ||S false)  ==S true
     ~> #assert (true ||S false) =/=S false
     ~> #assert (true &&S false)  ==S false
     ~> #restoreEthereum V_CONF_BEFORE
     ~> #assert #getOutput            ==S #var(V_OUT_BEFORE)
     ~> #assert #getStorage(ACCT_ID)  ==S #var(V_STORAGE_BEFORE)
     ~> #assert #getLog               ==S #var(V_LOG_BEFORE)
     => . </k>
    <exit-code> 1 </exit-code>
    <mode> NORMAL </mode>
    <schedule> CONSTANTINOPLE </schedule>

    <ethereum>
      <evm>
        <output> _ => _ </output>
        <statusCode> _ => _ </statusCode>
        <endPC> _ => ?_ </endPC>
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
            <code> #parseByteStack("0x608060405260043610603f576000357c0100000000000000000000000000000000000000000000000000000000900463ffffffff1680631003e2d2146044575b600080fd5b348015604f57600080fd5b50607960048036036020811015606457600080fd5b8101908080359060200190929190505050608f565b6040518082815260200191505060405180910390f35b6000806000549050600083600054019050806000819055507ff3ca124a697ba07e8c5e80bebcfcc48991fc16a63170e8a9206e30508960d0038282604051808381526020018281526020019250505060405180910390a1809250505091905056fea165627a7a72305820e8d8d91789cd954b1fa9161f34d260c3ad3764cdb8b8e9117be8eec773574ec90029") </code>
            <storage>     #hashedLocation("Solidity", 0, .IntList) |-> (OLD_S => _) .Map </storage>
            <origStorage> #hashedLocation("Solidity", 0, .IntList) |-> (OLD_S => _) .Map </origStorage>
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
     andBool VALUE =/=Int 0
     andBool #rangeUInt(256, SUM)
     andBool V_CONF_BEFORE            ==K String2Id("V_CONF_BEFORE")
     andBool V_OUT_BEFORE             ==K String2Id("V_OUT_BEFORE")
     andBool V_STORAGE_BEFORE         ==K String2Id("V_STORAGE_BEFORE")
     andBool V_LOG_BEFORE             ==K String2Id("V_LOG_BEFORE")
     andBool V_ADD_OUT                ==K String2Id("V_ADD_OUT")

endmodule
