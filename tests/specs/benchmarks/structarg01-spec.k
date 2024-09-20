requires "verification.k"

module STRUCTARG01-SPEC
  imports VERIFICATION

  // fn-execute
  claim
    <k> (#execute => #halt) ~> _ </k>
    <mode> NORMAL </mode>
    <schedule> ISTANBUL </schedule>
    <useGas> true </useGas>
    <ethereum>
      <evm>
        <output> _ => #encodeArgs(#bytes(A0)) </output>
        <statusCode> _ => EVMC_SUCCESS </statusCode>
        <callStack> _ </callStack>
        <interimStates> _ </interimStates>
        <touchedAccounts> _ => ?_ </touchedAccounts>
        <callState>
          <program> #parseByteStack("0x6080604052600436106100245760003560e01c63ffffffff1680634a39f70214610029575b600080fd5b34801561003557600080fd5b5061004961004436600461013c565b61005f565b60405161005691906101ae565b60405180910390f35b5190565b6000601f8201831361007457600080fd5b8135610087610082826101e6565b6101bf565b915080825260208301602083018583830111156100a357600080fd5b6100ae838284610211565b50505092915050565b6000606082840312156100c957600080fd5b6100d360606101bf565b9050813567ffffffffffffffff8111156100ec57600080fd5b6100f884828501610063565b825250602061010984848301610129565b602083015250604061011d84828501610129565b60408301525092915050565b6000610135823561020e565b9392505050565b60006020828403121561014e57600080fd5b813567ffffffffffffffff81111561016557600080fd5b610171848285016100b7565b949350505050565b60006101848261005f565b80845261019881602086016020860161021d565b6101a18161024d565b9093016020019392505050565b602080825281016101358184610179565b60405181810167ffffffffffffffff811182821017156101de57600080fd5b604052919050565b600067ffffffffffffffff8211156101fd57600080fd5b506020601f91909101601f19160190565b90565b82818337506000910152565b60005b83811015610238578181015183820152602001610220565b83811115610247576000848401525b50505050565b601f01601f1916905600a265627a7a72305820e24054b606276c885165f6ec29d3a2833d528d07d72783ef5f0277b5a6906d196c6578706572696d656e74616cf50037") </program>
          <jumpDests> #computeValidJumpDests(#parseByteStack("0x6080604052600436106100245760003560e01c63ffffffff1680634a39f70214610029575b600080fd5b34801561003557600080fd5b5061004961004436600461013c565b61005f565b60405161005691906101ae565b60405180910390f35b5190565b6000601f8201831361007457600080fd5b8135610087610082826101e6565b6101bf565b915080825260208301602083018583830111156100a357600080fd5b6100ae838284610211565b50505092915050565b6000606082840312156100c957600080fd5b6100d360606101bf565b9050813567ffffffffffffffff8111156100ec57600080fd5b6100f884828501610063565b825250602061010984848301610129565b602083015250604061011d84828501610129565b60408301525092915050565b6000610135823561020e565b9392505050565b60006020828403121561014e57600080fd5b813567ffffffffffffffff81111561016557600080fd5b610171848285016100b7565b949350505050565b60006101848261005f565b80845261019881602086016020860161021d565b6101a18161024d565b9093016020019392505050565b602080825281016101358184610179565b60405181810167ffffffffffffffff811182821017156101de57600080fd5b604052919050565b600067ffffffffffffffff8211156101fd57600080fd5b506020601f91909101601f19160190565b90565b82818337506000910152565b60005b83811015610238578181015183820152602001610220565b83811115610247576000848401525b50505050565b601f01601f1916905600a265627a7a72305820e24054b606276c885165f6ec29d3a2833d528d07d72783ef5f0277b5a6906d196c6578706572696d656e74616cf50037")) </jumpDests>
          <id> CONTRACT_ID </id> // this
          <caller> CALLEE_ID </caller> // msg.sender
          <callData> #abiCallData2("execute((bytes,uint256,uint256))", #tuple(#bytes(A0), #uint256(A1), #uint256(A2), .TypedArgs)) </callData> // msg.data
          <callValue> 0 </callValue> // msg.value
          <wordStack> .WordStack => ?_ </wordStack>
          <wordStackSize> 0 => ?_ </wordStackSize>
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
        <origin> _ </origin>
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
            <code> #parseByteStack("0x6080604052600436106100245760003560e01c63ffffffff1680634a39f70214610029575b600080fd5b34801561003557600080fd5b5061004961004436600461013c565b61005f565b60405161005691906101ae565b60405180910390f35b5190565b6000601f8201831361007457600080fd5b8135610087610082826101e6565b6101bf565b915080825260208301602083018583830111156100a357600080fd5b6100ae838284610211565b50505092915050565b6000606082840312156100c957600080fd5b6100d360606101bf565b9050813567ffffffffffffffff8111156100ec57600080fd5b6100f884828501610063565b825250602061010984848301610129565b602083015250604061011d84828501610129565b60408301525092915050565b6000610135823561020e565b9392505050565b60006020828403121561014e57600080fd5b813567ffffffffffffffff81111561016557600080fd5b610171848285016100b7565b949350505050565b60006101848261005f565b80845261019881602086016020860161021d565b6101a18161024d565b9093016020019392505050565b602080825281016101358184610179565b60405181810167ffffffffffffffff811182821017156101de57600080fd5b604052919050565b600067ffffffffffffffff8211156101fd57600080fd5b506020601f91909101601f19160190565b90565b82818337506000910152565b60005b83811015610238578181015183820152602001610220565b83811115610247576000848401525b50505050565b601f01601f1916905600a265627a7a72305820e24054b606276c885165f6ec29d3a2833d528d07d72783ef5f0277b5a6906d196c6578706572696d656e74616cf50037") </code>
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
          ...
        </accounts>
        <txOrder> _ </txOrder>
        <txPending> _ </txPending>
        <messages> _ </messages>
      </network>
    </ethereum>
    requires #rangeAddress(CONTRACT_ID)
     andBool #rangeAddress(CALLEE_ID)
     andBool #rangeUInt(256, CONTRACT_BAL)
     andBool #rangeUInt(256, CALLEE_BAL)
     andBool #rangeNonce(CONTRACT_NONCE)
     andBool #rangeNonce(CALLEE_NONCE)
     andBool #range(0 <= CD < 1024)
     andBool #rangeUInt(256, A1)
     andBool #rangeUInt(256, A2)
     andBool lengthBytes(A0) ==Int 100

endmodule
