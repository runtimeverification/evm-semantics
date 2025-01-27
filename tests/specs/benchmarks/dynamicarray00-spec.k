requires "verification.k"

module DYNAMICARRAY00-SPEC
  imports VERIFICATION

  // fn-execute
  claim
    <k> (#execute => #halt) ~> _ </k>
    <mode> NORMAL </mode>
    <schedule> ISTANBUL </schedule>
    <useGas> true </useGas>
    <ethereum>
      <evm>
        <output> _ => #encodeArgs(#uint256(3)) </output>
        <statusCode> _ => EVMC_SUCCESS </statusCode>
        <callStack> _ </callStack>
        <interimStates> _ </interimStates>
        <touchedAccounts> _ => ?_ </touchedAccounts>
        <callState>
          <program> #parseByteStack("0x60806040526004361060225760003560e01c63ffffffff1680638ef16cd9146027575b600080fd5b348015603257600080fd5b5060408051602060048035808201358381028086018501909652808552607995369593946024949385019291829185019084908082843750949750608b9650505050505050565b60408051918252519081900360200190f35b51905600a165627a7a72305820033b07c141d79055a0848aadceb745344b5e3a1fb5eff1292fc547e38d5bbe2a0029") </program>
          <jumpDests> #computeValidJumpDests(#parseByteStack("0x60806040526004361060225760003560e01c63ffffffff1680638ef16cd9146027575b600080fd5b348015603257600080fd5b5060408051602060048035808201358381028086018501909652808552607995369593946024949385019291829185019084908082843750949750608b9650505050505050565b60408051918252519081900360200190f35b51905600a165627a7a72305820033b07c141d79055a0848aadceb745344b5e3a1fb5eff1292fc547e38d5bbe2a0029")) </jumpDests>
          <id> CONTRACT_ID </id> // this
          <caller> MSG_SENDER </caller> // msg.sender
          <callData> #abiCallData2("execute(uint256[])", #array(#uint256(1), 3, #uint256(A0), #uint256(A1), #uint256(A2), .TypedArgs)) </callData> // msg.data
          <callValue> 0 </callValue> // msg.value
          <wordStack> .WordStack => ?_ </wordStack>
          <localMem> .Bytes => ?_ </localMem>
          <pc> 0 => ?_ </pc>
          <gas> #gas(_VGAS) => ?_ </gas>
          <memoryUsed> 0 => ?_ </memoryUsed>
          <callGas> _ => ?_ </callGas>
          <static> false </static> // NOTE: non-static call
          <callDepth> CD </callDepth>
        </callState>
        <versionedHashes> _ </versionedHashes>
        <substate>
          <selfDestruct> _ </selfDestruct>
          <log> _ </log>
          <refund> _ </refund>
          <accessedAccounts> _ => ?_ </accessedAccounts>
          <accessedStorage> _ => ?_ </accessedStorage>
          <createdAccounts> _ => ?_ </createdAccounts>
        </substate>
        <gasPrice> _ </gasPrice>
        <origin> _ </origin> // tx.origin
        <blockhashes> _BLOCK_HASHES </blockhashes> // block.blockhash
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
          <baseFee> _ </baseFee>
          <ommerBlockHeaders> _ </ommerBlockHeaders>
          <withdrawalsRoot> _ </withdrawalsRoot>
          <blobGasUsed> _ </blobGasUsed>
          <excessBlobGas> _ </excessBlobGas>
          <beaconRoot> _ </beaconRoot>
        </block>
      </evm>
      <network>
        <chainID> _ </chainID>

        <accounts>
          <account>
            <acctID> CONTRACT_ID </acctID>
            <balance> CONTRACT_BAL </balance>
            <code> #parseByteStack("0x60806040526004361060225760003560e01c63ffffffff1680638ef16cd9146027575b600080fd5b348015603257600080fd5b5060408051602060048035808201358381028086018501909652808552607995369593946024949385019291829185019084908082843750949750608b9650505050505050565b60408051918252519081900360200190f35b51905600a165627a7a72305820033b07c141d79055a0848aadceb745344b5e3a1fb5eff1292fc547e38d5bbe2a0029") </code>
            <storage>
_
            </storage>
            <origStorage>
_
            </origStorage>
            <nonce> CONTRACT_NONCE </nonce>
            <transientStorage>
                _
            </transientStorage>
          </account>

          <account>
            <acctID> CALLEE_ID </acctID>
            <balance> CALLEE_BAL </balance>
            <code> _ </code>
            <storage>
                _
            </storage>
            <origStorage>
                _
            </origStorage>
            <nonce> CALLEE_NONCE </nonce>
            <transientStorage>
                _
            </transientStorage>
          </account>

          <account>
            // precompiled account for ECCREC
            <acctID> 1 </acctID>
            <balance> 0 </balance>
            <code> .Bytes </code>
            <storage> .Map </storage>
            <origStorage> .Map </origStorage>
            <nonce> 0 </nonce>
            <transientStorage> .Map </transientStorage>
          </account>


          ...
        </accounts>
        <txOrder> _ </txOrder>
        <txPending> _ </txPending>
        <messages> _ </messages>
      </network>
    </ethereum>
    requires #rangeAddress(CONTRACT_ID)
     andBool #rangeAddress(CALLEE_ID)
     andBool #rangeUInt(256, NOW)
     andBool #rangeUInt(128, BLOCK_NUM) // Solidity
     andBool #rangeUInt(256, CONTRACT_BAL)
     andBool #rangeUInt(256, CALLEE_BAL)
     andBool #rangeNonce(CONTRACT_NONCE)
     andBool #rangeNonce(CALLEE_NONCE)
     andBool #range(0 <= CD < 1024)
     andBool #rangeAddress(MSG_SENDER)
     andBool #rangeUInt(256, A0)
     andBool #rangeUInt(256, A1)
     andBool #rangeUInt(256, A2)

endmodule
