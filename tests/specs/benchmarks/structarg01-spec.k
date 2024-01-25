requires "verification.k"

module STRUCTARG01-SPEC
  imports VERIFICATION

  // fn-execute
  claim
    <k> (#execute => #halt) ~> _ </k>
    <exit-code> 1 </exit-code>
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
          <program> #parseByteStack("0x6080604052600436106100245760003560e01c63ffffffff1680638b78211314610029575b600080fd5b34801561003557600080fd5b50610049610044366004610129565b61005f565b6040516100569190610175565b60405180910390f35b5190565b6000601f8201831361007457600080fd5b8135610087610082826101b0565b610189565b915080825260208301602083018583830111156100a357600080fd5b6100ae8382846101db565b50505092915050565b6000604082840312156100c957600080fd5b6100d36040610189565b905060006100e18484610116565b825250602082013567ffffffffffffffff8111156100fe57600080fd5b61010a84828501610063565b60208301525092915050565b600061012282356101d8565b9392505050565b60006020828403121561013b57600080fd5b813567ffffffffffffffff81111561015257600080fd5b61015e848285016100b7565b949350505050565b61016f816101d8565b82525050565b602081016101838284610166565b92915050565b60405181810167ffffffffffffffff811182821017156101a857600080fd5b604052919050565b600067ffffffffffffffff8211156101c757600080fd5b506020601f91909101601f19160190565b90565b828183375060009101525600a265627a7a72305820a016ca8c690bbe7c22fea6278d20a3b882fe5d12e1e4a7507dcd7e01da59fb086c6578706572696d656e74616cf50037") </program>
          <jumpDests> #computeValidJumpDests(#parseByteStack("0x6080604052600436106100245760003560e01c63ffffffff1680638b78211314610029575b600080fd5b34801561003557600080fd5b50610049610044366004610129565b61005f565b6040516100569190610175565b60405180910390f35b5190565b6000601f8201831361007457600080fd5b8135610087610082826101b0565b610189565b915080825260208301602083018583830111156100a357600080fd5b6100ae8382846101db565b50505092915050565b6000604082840312156100c957600080fd5b6100d36040610189565b905060006100e18484610116565b825250602082013567ffffffffffffffff8111156100fe57600080fd5b61010a84828501610063565b60208301525092915050565b600061012282356101d8565b9392505050565b60006020828403121561013b57600080fd5b813567ffffffffffffffff81111561015257600080fd5b61015e848285016100b7565b949350505050565b61016f816101d8565b82525050565b602081016101838284610166565b92915050565b60405181810167ffffffffffffffff811182821017156101a857600080fd5b604052919050565b600067ffffffffffffffff8211156101c757600080fd5b506020601f91909101601f19160190565b90565b828183375060009101525600a265627a7a72305820a016ca8c690bbe7c22fea6278d20a3b882fe5d12e1e4a7507dcd7e01da59fb086c6578706572696d656e74616cf50037")) </jumpDests>
          <id> CONTRACT_ID </id> // this
          <caller> MSG_SENDER </caller> // msg.sender
          <callData> #abiCallData2("execute((uint256,bytes))", #tuple(#uint256(A0), #bytes(#parseByteStack("0x11221100FF")), .TypedArgs)) </callData> // msg.data
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
          </account>

          <account>
            // precompiled account for ECCREC
            <acctID> 1 </acctID>
            <balance> 0 </balance>
            <code> .Bytes </code>
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
