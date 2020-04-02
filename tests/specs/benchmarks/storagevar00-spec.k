requires "abstract-semantics.k"
requires "verification.k"

module STORAGEVAR00-SPEC
  imports ETHEREUM-SIMULATION
  imports ABSTRACT-SEMANTICS
  imports VERIFICATION

  // fn-execute 
  rule
    <k> (#execute => #halt) ~> _ </k>
    <exit-code> 1 </exit-code>
    <mode> NORMAL </mode>
    <schedule> ISTANBUL </schedule>
    <ethereum>
      <evm>
        <output> _ => #encodeArgs(#uint256(N)) </output>
        <statusCode> _ => EVMC_SUCCESS </statusCode>
        <endPC> _ => ?_ </endPC>
        <callStack> _ </callStack>
        <interimStates> _ </interimStates>
        <touchedAccounts> _ => _ </touchedAccounts>
        <callState>
          <program> #parseByteStack("0x608060405260043610603f576000357c0100000000000000000000000000000000000000000000000000000000900463ffffffff16806361461954146044575b600080fd5b348015604f57600080fd5b506056606c565b6040518082815260200191505060405180910390f35b6000805490509056fea165627a7a7230582042a42ab720fca3a1db0ba7ac19c662cf1a6fb8fdb252593eb42de55a510e09470029") </program>
          <jumpDests> #computeValidJumpDests(#parseByteStack("0x608060405260043610603f576000357c0100000000000000000000000000000000000000000000000000000000900463ffffffff16806361461954146044575b600080fd5b348015604f57600080fd5b506056606c565b6040518082815260200191505060405180910390f35b6000805490509056fea165627a7a7230582042a42ab720fca3a1db0ba7ac19c662cf1a6fb8fdb252593eb42de55a510e09470029")) </jumpDests>
          <id> #CONTRACT_ID </id> // this
          <caller> MSG_SENDER </caller> // msg.sender
          <callData> #abiCallData("execute", .TypedArgs) </callData> // msg.data
          <callValue> 0 </callValue> // msg.value
          <wordStack> .WordStack => _ </wordStack>
          <localMem> .Memory => _ </localMem>
          <pc> 0 => _ </pc>
          <gas> #gas(INITGAS, 0, 0) => _ </gas>
          <memoryUsed> 0 => _ </memoryUsed>
          <callGas> _ => _ </callGas>
          <static> false </static> // NOTE: non-static call
          <callDepth> CD </callDepth>
        </callState>
        <substate>
          <selfDestruct> _ </selfDestruct>
          <log> _ </log>
          <refund> _ </refund>
        </substate>
        <gasPrice> _ </gasPrice>
        <origin> _ </origin> // tx.origin
        <blockhashes> BLOCK_HASHES </blockhashes> // block.blockhash
        <block>
          <previousHash> _ </previousHash>
          <ommersHash> _ </ommersHash>
          <coinbase> _ </coinbase> // block.coinbase
          <stateRoot> _ </stateRoot>
          <transactionsRoot> _ </transactionsRoot>
          <receiptsRoot> _ </receiptsRoot>
          <logsBloom> _ </logsBloom>
          <difficulty> _ </difficulty>
          <number> BLOCK_NUM </number> // block.number
          <gasLimit> _ </gasLimit>
          <gasUsed> _ </gasUsed>
          <timestamp> NOW </timestamp> // now = block.timestamp
          <extraData> _ </extraData>
          <mixHash> _ </mixHash>
          <blockNonce> _ </blockNonce>
          <ommerBlockHeaders> _ </ommerBlockHeaders>
        </block>
      </evm>
      <network>
        <chainID> _ </chainID>

        <activeAccounts> SetItem(#CONTRACT_ID) SetItem(#CALLEE_ID) SetItem(1) _:Set </activeAccounts>
        <accounts>
          <account>
            <acctID> #CONTRACT_ID </acctID>
            <balance> CONTRACT_BAL </balance>
            <code> #parseByteStack("0x608060405260043610603f576000357c0100000000000000000000000000000000000000000000000000000000900463ffffffff16806361461954146044575b600080fd5b348015604f57600080fd5b506056606c565b6040518082815260200191505060405180910390f35b6000805490509056fea165627a7a7230582042a42ab720fca3a1db0ba7ac19c662cf1a6fb8fdb252593eb42de55a510e09470029") </code>
            <storage>
S
            </storage>
            <origStorage>
_
            </origStorage>
            <nonce> _ </nonce>
          </account>

          <account>
            <acctID> #CALLEE_ID </acctID>
            <balance> CALLEE_BAL </balance>
            <code> _ </code>
            <storage>
                _
            </storage>
            <origStorage>
                _
            </origStorage>
            <nonce> _ </nonce>
          </account>

          <account>
            // precompiled account for ECCREC
            <acctID> 1 </acctID>
            <balance> 0 </balance>
            <code> .WordStack </code>
            <storage> .Map </storage>
            <origStorage> .Map </origStorage>
            <nonce> 0 </nonce>
          </account>


          ...
        </accounts>
        <txOrder> _ </txOrder>
        <txPending> _ </txPending>
        <messages> _ </messages>
      </network>
    </ethereum>
    requires
     #rangeAddress(#CONTRACT_ID)
     andBool #rangeAddress(#CALLEE_ID)
     andBool #rangeUInt(256, NOW)
     andBool #rangeUInt(128, BLOCK_NUM) // Solidity

     // Account address normality
     andBool #CONTRACT_ID  >Int 0 andBool (notBool #CONTRACT_ID  in #precompiledAccounts(BYZANTIUM))
     andBool #CALLEE_ID  >Int 0 andBool (notBool #CALLEE_ID  in #precompiledAccounts(BYZANTIUM))

andBool #rangeUInt(256, CONTRACT_BAL)
andBool #rangeUInt(256, CALLEE_BAL)andBool #range(0 <= CD < 1024)
andBool #rangeAddress(MSG_SENDER)andBool N ==Int select(S, #hashedLocation("Solidity", 0, .IntList))
andBool #rangeUInt(256, N)
    ensures true




endmodule

