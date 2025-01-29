requires "verification.k"

module STRUCTARG00-SPEC
  imports VERIFICATION

  // fn-execute
  claim
    <k> (#execute => #halt) ~> _ </k>
    <mode> NORMAL </mode>
    <schedule> ISTANBUL </schedule>
    <useGas> true </useGas>
    <ethereum>
      <evm>
        <output> _ => #encodeArgs(#uint256(A0)) </output>
        <statusCode> _ => EVMC_SUCCESS </statusCode>
        <callStack> _ </callStack>
        <interimStates> _ </interimStates>
        <touchedAccounts> _ => ?_ </touchedAccounts>
        <callState>
          <program> #parseByteStack("0x6080604052600436106100245760003560e01c63ffffffff168063dd77d08e14610029575b600080fd5b34801561003557600080fd5b506100496100443660046100c9565b61005f565b60405161005691906100fe565b60405180910390f35b5190565b60006040828403121561007557600080fd5b61007f6040610112565b9050600061008d84846100aa565b825250602061009e848483016100bd565b60208301525092915050565b60006100b68235610139565b9392505050565b60006100b6823561013c565b6000604082840312156100db57600080fd5b60006100e78484610063565b949350505050565b6100f881610139565b82525050565b6020810161010c82846100ef565b92915050565b60405181810167ffffffffffffffff8111828210171561013157600080fd5b604052919050565b90565b60ff16905600a265627a7a723058206cff7fc5f1eee5a02118c03209b136de08c05265f52541d16a578e6ff695a84b6c6578706572696d656e74616cf50037") </program>
          <jumpDests> #computeValidJumpDests(#parseByteStack("0x6080604052600436106100245760003560e01c63ffffffff168063dd77d08e14610029575b600080fd5b34801561003557600080fd5b506100496100443660046100c9565b61005f565b60405161005691906100fe565b60405180910390f35b5190565b60006040828403121561007557600080fd5b61007f6040610112565b9050600061008d84846100aa565b825250602061009e848483016100bd565b60208301525092915050565b60006100b68235610139565b9392505050565b60006100b6823561013c565b6000604082840312156100db57600080fd5b60006100e78484610063565b949350505050565b6100f881610139565b82525050565b6020810161010c82846100ef565b92915050565b60405181810167ffffffffffffffff8111828210171561013157600080fd5b604052919050565b90565b60ff16905600a265627a7a723058206cff7fc5f1eee5a02118c03209b136de08c05265f52541d16a578e6ff695a84b6c6578706572696d656e74616cf50037")) </jumpDests>
          <id> CONTRACT_ID </id> // this
          <caller> MSG_SENDER </caller> // msg.sender
          <callData> #abiCallData2("execute((uint256,uint8))", #tuple(#uint256(A0), #uint8(A1), .TypedArgs)) </callData> // msg.data
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
        ...
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
     andBool #rangeUInt(8, A1)

endmodule
