module TRANSFER-FROM-SPEC
  imports ETHEREUM-SIMULATION

  rule
    <k> #execute => (RETURN R:Int 32  ~> _) </k>
    <exit-code> 1 </exit-code>
    <mode> NORMAL </mode>
    <schedule> DEFAULT </schedule> // TODO: pick a right one
    <analysis> /* _ */ .Map </analysis>

    <ethereum>
      <evm>
        <output> /* _ */ .WordStack </output>
        <memoryUsed> 0 => _ </memoryUsed>
        <callDepth> /* CALL_DEPTH */ 0 </callDepth> // TODO: check if <= 1024
        <callStack> /* _ */ .List => _ </callStack>
        <interimStates> /* _ */ .List </interimStates>
        <substateStack> /* _ */ .List </substateStack>
        <callLog> /* _ */ .Set </callLog>

        <txExecState>
          <program>
            #asMapOpCodes(#dasmOpCodes(#parseByteStack(
              "0x600035601c52740100000000000000000000000000000000000000006020526f7fffffffffffffffffffffffffffffff6040527fffffffffffffffffffffffffffffffff8000000000000000000000000000000060605274012a05f1fffffffffffffffffffffffffdabf41c006080527ffffffffffffffffffffffffed5fa0e000000000000000000000000000000000060a05263d0e30db06000511415610168573460008112585761014052336101605261016051600060c052602060c02001546101405161016051600060c052602060c020015401116101405115176100e657600080fd5b6101405161016051600060c052602060c02001540161016051600060c052602060c020015560025461014051600254011161014051151761012657600080fd5b610140516002540160025561014051610180526101605160007fddf252ad1be2c89b69c2b068fc378daa952ba7f163c4a11628f55a4df523b3ef6020610180a3005b632e1a7d4d6000511415610260576020600461014037341561018957600080fd5b33610160526101405161016051600060c052602060c020015410156101ad57600080fd5b6101405161016051600060c052602060c02001540361016051600060c052602060c02001556101405160025410156101e457600080fd5b61014051600254036002556000600060006000600160605161014051806040519013585780919012585702610160516000f161021f57600080fd5b61014051610180526000610160517fddf252ad1be2c89b69c2b068fc378daa952ba7f163c4a11628f55a4df523b3ef6020610180a3600160005260206000f3005b6318160ddd600051141561028657341561027957600080fd5b60025460005260206000f3005b6370a0823160005114156102cd57602060046101403734156102a757600080fd5b60043560205181101558575061014051600060c052602060c020015460005260206000f3005b63a9059cbb60005114156103e057604060046101403734156102ee57600080fd5b60043560205181101558575033610180526101605161018051600060c052602060c0200154101561031e57600080fd5b6101605161018051600060c052602060c02001540361018051600060c052602060c020015561014051600060c052602060c02001546101605161014051600060c052602060c0200154011161016051151761037857600080fd5b6101605161014051600060c052602060c02001540161014051600060c052602060c0200155610160516101a05261014051610180517fddf252ad1be2c89b69c2b068fc378daa952ba7f163c4a11628f55a4df523b3ef60206101a0a3600160005260206000f3005b6323b872dd6000511415610559576060600461014037341561040157600080fd5b600435602051811015585750602435602051811015585750336101a0526101a05161014051600160c052602060c0200160c052602060c02001546101c0526101805161014051600060c052602060c0200154101561045e57600080fd5b6101805161014051600060c052602060c02001540361014051600060c052602060c020015561016051600060c052602060c02001546101805161016051600060c052602060c020015401116101805115176104b857600080fd5b6101805161016051600060c052602060c02001540161016051600060c052602060c0200155610180516101c05110156104f057600080fd5b610180516101c051036101a05161014051600160c052602060c0200160c052602060c0200155610180516101e05261016051610140517fddf252ad1be2c89b69c2b068fc378daa952ba7f163c4a11628f55a4df523b3ef60206101e0a3600160005260206000f3005b63095ea7b360005114156105ef576040600461014037341561057a57600080fd5b6004356020518110155857503361018052610160516101405161018051600160c052602060c0200160c052602060c0200155610160516101a05261014051610180517f8c5be1e5ebec7d5bd14f71427d1e84f3dd0314c0f7b2291e5b200ac8c7c3b92560206101a0a3600160005260206000f3005b63dd62ed3e600051141561064f576040600461014037341561061057600080fd5b6004356020518110155857506024356020518110155857506101605161014051600160c052602060c0200160c052602060c020015460005260206000f3005b"
            ),DEFAULT))
          </program>
          <programBytes>
            #parseByteStack(
              "0x600035601c52740100000000000000000000000000000000000000006020526f7fffffffffffffffffffffffffffffff6040527fffffffffffffffffffffffffffffffff8000000000000000000000000000000060605274012a05f1fffffffffffffffffffffffffdabf41c006080527ffffffffffffffffffffffffed5fa0e000000000000000000000000000000000060a05263d0e30db06000511415610168573460008112585761014052336101605261016051600060c052602060c02001546101405161016051600060c052602060c020015401116101405115176100e657600080fd5b6101405161016051600060c052602060c02001540161016051600060c052602060c020015560025461014051600254011161014051151761012657600080fd5b610140516002540160025561014051610180526101605160007fddf252ad1be2c89b69c2b068fc378daa952ba7f163c4a11628f55a4df523b3ef6020610180a3005b632e1a7d4d6000511415610260576020600461014037341561018957600080fd5b33610160526101405161016051600060c052602060c020015410156101ad57600080fd5b6101405161016051600060c052602060c02001540361016051600060c052602060c02001556101405160025410156101e457600080fd5b61014051600254036002556000600060006000600160605161014051806040519013585780919012585702610160516000f161021f57600080fd5b61014051610180526000610160517fddf252ad1be2c89b69c2b068fc378daa952ba7f163c4a11628f55a4df523b3ef6020610180a3600160005260206000f3005b6318160ddd600051141561028657341561027957600080fd5b60025460005260206000f3005b6370a0823160005114156102cd57602060046101403734156102a757600080fd5b60043560205181101558575061014051600060c052602060c020015460005260206000f3005b63a9059cbb60005114156103e057604060046101403734156102ee57600080fd5b60043560205181101558575033610180526101605161018051600060c052602060c0200154101561031e57600080fd5b6101605161018051600060c052602060c02001540361018051600060c052602060c020015561014051600060c052602060c02001546101605161014051600060c052602060c0200154011161016051151761037857600080fd5b6101605161014051600060c052602060c02001540161014051600060c052602060c0200155610160516101a05261014051610180517fddf252ad1be2c89b69c2b068fc378daa952ba7f163c4a11628f55a4df523b3ef60206101a0a3600160005260206000f3005b6323b872dd6000511415610559576060600461014037341561040157600080fd5b600435602051811015585750602435602051811015585750336101a0526101a05161014051600160c052602060c0200160c052602060c02001546101c0526101805161014051600060c052602060c0200154101561045e57600080fd5b6101805161014051600060c052602060c02001540361014051600060c052602060c020015561016051600060c052602060c02001546101805161016051600060c052602060c020015401116101805115176104b857600080fd5b6101805161016051600060c052602060c02001540161016051600060c052602060c0200155610180516101c05110156104f057600080fd5b610180516101c051036101a05161014051600160c052602060c0200160c052602060c0200155610180516101e05261016051610140517fddf252ad1be2c89b69c2b068fc378daa952ba7f163c4a11628f55a4df523b3ef60206101e0a3600160005260206000f3005b63095ea7b360005114156105ef576040600461014037341561057a57600080fd5b6004356020518110155857503361018052610160516101405161018051600160c052602060c0200160c052602060c0200155610160516101a05261014051610180517f8c5be1e5ebec7d5bd14f71427d1e84f3dd0314c0f7b2291e5b200ac8c7c3b92560206101a0a3600160005260206000f3005b63dd62ed3e600051141561064f576040600461014037341561061057600080fd5b6004356020518110155857506024356020518110155857506101605161014051600160c052602060c0200160c052602060c020015460005260206000f3005b"
            )
          </programBytes>

          <id> ACCT_ID </id> // contract owner
          <caller> CALLER_ID </caller> // who called this contract; in the begining, origin

          <callData> // TODO: auto gen
            int2wordstack(F, 4)
            ++
            int2wordstack(O, 32)
//             nthbyteof(F,  0,  4)
//           : nthbyteof(F,  1,  4)
//           : nthbyteof(F,  2,  4)
//           : nthbyteof(F,  3,  4)
//           : nthbyteof(O,  0, 32)
//           : nthbyteof(O,  1, 32)
//           : nthbyteof(O,  2, 32)
//           : nthbyteof(O,  3, 32)
//           : nthbyteof(O,  4, 32)
//           : nthbyteof(O,  5, 32)
//           : nthbyteof(O,  6, 32)
//           : nthbyteof(O,  7, 32)
//           : nthbyteof(O,  8, 32)
//           : nthbyteof(O,  9, 32)
//           : nthbyteof(O, 10, 32)
//           : nthbyteof(O, 11, 32)
//           : nthbyteof(O, 12, 32)
//           : nthbyteof(O, 13, 32)
//           : nthbyteof(O, 14, 32)
//           : nthbyteof(O, 15, 32)
//           : nthbyteof(O, 16, 32)
//           : nthbyteof(O, 17, 32)
//           : nthbyteof(O, 18, 32)
//           : nthbyteof(O, 19, 32)
//           : nthbyteof(O, 20, 32)
//           : nthbyteof(O, 21, 32)
//           : nthbyteof(O, 22, 32)
//           : nthbyteof(O, 23, 32)
//           : nthbyteof(O, 24, 32)
//           : nthbyteof(O, 25, 32)
//           : nthbyteof(O, 26, 32)
//           : nthbyteof(O, 27, 32)
//           : nthbyteof(O, 28, 32)
//           : nthbyteof(O, 29, 32)
//           : nthbyteof(O, 30, 32)
//           : nthbyteof(O, 31, 32)
//           : .WordStack
          </callData>

          <callValue> 0 </callValue>
          <wordStack> .WordStack => _ </wordStack>
          <localMem> // TODO: auto gen
            28 |-> nthbyteof(F, 0, 4)
            29 |-> nthbyteof(F, 1, 4)
            30 |-> nthbyteof(F, 2, 4)
            31 |-> nthbyteof(F, 3, 4)
          =>
          (
            int2wordmap(R, B, 32)
//           R          |-> nthbyteof(B,  0, 32)
//          (R +Int  1) |-> nthbyteof(B,  1, 32)
//          (R +Int  2) |-> nthbyteof(B,  2, 32)
//          (R +Int  3) |-> nthbyteof(B,  3, 32)
//          (R +Int  4) |-> nthbyteof(B,  4, 32)
//          (R +Int  5) |-> nthbyteof(B,  5, 32)
//          (R +Int  6) |-> nthbyteof(B,  6, 32)
//          (R +Int  7) |-> nthbyteof(B,  7, 32)
//          (R +Int  8) |-> nthbyteof(B,  8, 32)
//          (R +Int  9) |-> nthbyteof(B,  9, 32)
//          (R +Int 10) |-> nthbyteof(B, 10, 32)
//          (R +Int 11) |-> nthbyteof(B, 11, 32)
//          (R +Int 12) |-> nthbyteof(B, 12, 32)
//          (R +Int 13) |-> nthbyteof(B, 13, 32)
//          (R +Int 14) |-> nthbyteof(B, 14, 32)
//          (R +Int 15) |-> nthbyteof(B, 15, 32)
//          (R +Int 16) |-> nthbyteof(B, 16, 32)
//          (R +Int 17) |-> nthbyteof(B, 17, 32)
//          (R +Int 18) |-> nthbyteof(B, 18, 32)
//          (R +Int 19) |-> nthbyteof(B, 19, 32)
//          (R +Int 20) |-> nthbyteof(B, 20, 32)
//          (R +Int 21) |-> nthbyteof(B, 21, 32)
//          (R +Int 22) |-> nthbyteof(B, 22, 32)
//          (R +Int 23) |-> nthbyteof(B, 23, 32)
//          (R +Int 24) |-> nthbyteof(B, 24, 32)
//          (R +Int 25) |-> nthbyteof(B, 25, 32)
//          (R +Int 26) |-> nthbyteof(B, 26, 32)
//          (R +Int 27) |-> nthbyteof(B, 27, 32)
//          (R +Int 28) |-> nthbyteof(B, 28, 32)
//          (R +Int 29) |-> nthbyteof(B, 29, 32)
//          (R +Int 30) |-> nthbyteof(B, 30, 32)
//          (R +Int 31) |-> nthbyteof(B, 31, 32)
            _:Map
          )
          </localMem>
          <pc> 6 => _ </pc> // TODO: auto gen
          <gas> /* G */ 20000 => _ </gas>
          <previousGas> _ => _ </previousGas>
        </txExecState>

        <substate>
          <selfDestruct> /* _ */ .Set </selfDestruct>
          <log> /* _ */ .List </log>
          <refund> /* _ */ 0 </refund>
        </substate>

        <gasPrice> _ </gasPrice>
        <origin> ORIGIN_ID </origin> // who fires tx

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
        <blockhash> _ </blockhash>
      </evm>

      <network>
        <activeAccounts> ACCT_ID |-> false /* _ */ </activeAccounts>

        <accounts>
          <account>
            <acctID> ACCT_ID </acctID>
            <balance> _ </balance>
            <code>
              #parseByteStack(
              "0x600035601c52740100000000000000000000000000000000000000006020526f7fffffffffffffffffffffffffffffff6040527fffffffffffffffffffffffffffffffff8000000000000000000000000000000060605274012a05f1fffffffffffffffffffffffffdabf41c006080527ffffffffffffffffffffffffed5fa0e000000000000000000000000000000000060a05263d0e30db06000511415610168573460008112585761014052336101605261016051600060c052602060c02001546101405161016051600060c052602060c020015401116101405115176100e657600080fd5b6101405161016051600060c052602060c02001540161016051600060c052602060c020015560025461014051600254011161014051151761012657600080fd5b610140516002540160025561014051610180526101605160007fddf252ad1be2c89b69c2b068fc378daa952ba7f163c4a11628f55a4df523b3ef6020610180a3005b632e1a7d4d6000511415610260576020600461014037341561018957600080fd5b33610160526101405161016051600060c052602060c020015410156101ad57600080fd5b6101405161016051600060c052602060c02001540361016051600060c052602060c02001556101405160025410156101e457600080fd5b61014051600254036002556000600060006000600160605161014051806040519013585780919012585702610160516000f161021f57600080fd5b61014051610180526000610160517fddf252ad1be2c89b69c2b068fc378daa952ba7f163c4a11628f55a4df523b3ef6020610180a3600160005260206000f3005b6318160ddd600051141561028657341561027957600080fd5b60025460005260206000f3005b6370a0823160005114156102cd57602060046101403734156102a757600080fd5b60043560205181101558575061014051600060c052602060c020015460005260206000f3005b63a9059cbb60005114156103e057604060046101403734156102ee57600080fd5b60043560205181101558575033610180526101605161018051600060c052602060c0200154101561031e57600080fd5b6101605161018051600060c052602060c02001540361018051600060c052602060c020015561014051600060c052602060c02001546101605161014051600060c052602060c0200154011161016051151761037857600080fd5b6101605161014051600060c052602060c02001540161014051600060c052602060c0200155610160516101a05261014051610180517fddf252ad1be2c89b69c2b068fc378daa952ba7f163c4a11628f55a4df523b3ef60206101a0a3600160005260206000f3005b6323b872dd6000511415610559576060600461014037341561040157600080fd5b600435602051811015585750602435602051811015585750336101a0526101a05161014051600160c052602060c0200160c052602060c02001546101c0526101805161014051600060c052602060c0200154101561045e57600080fd5b6101805161014051600060c052602060c02001540361014051600060c052602060c020015561016051600060c052602060c02001546101805161016051600060c052602060c020015401116101805115176104b857600080fd5b6101805161016051600060c052602060c02001540161016051600060c052602060c0200155610180516101c05110156104f057600080fd5b610180516101c051036101a05161014051600160c052602060c0200160c052602060c0200155610180516101e05261016051610140517fddf252ad1be2c89b69c2b068fc378daa952ba7f163c4a11628f55a4df523b3ef60206101e0a3600160005260206000f3005b63095ea7b360005114156105ef576040600461014037341561057a57600080fd5b6004356020518110155857503361018052610160516101405161018051600160c052602060c0200160c052602060c0200155610160516101a05261014051610180517f8c5be1e5ebec7d5bd14f71427d1e84f3dd0314c0f7b2291e5b200ac8c7c3b92560206101a0a3600160005260206000f3005b63dd62ed3e600051141561064f576040600461014037341561061057600080fd5b6004356020518110155857506024356020518110155857506101605161014051600160c052602060c0200160c052602060c020015460005260206000f3005b"
              )
            </code>
            <storage>
            //chop(hash(0) +Int O) |-> B:Int
              chop(sha3(0) +Int O) |-> B:Int
              _:Map
            </storage>
            <nonce> _ </nonce>
          </account>
          /* _ */
        </accounts>

        <txOrder> _ </txOrder>
        <txPending> _ </txPending>
        <messages> /* _ */ .Bag </messages>
      </network>
    </ethereum>
    requires 0 <=Int ACCT_ID   andBool ACCT_ID   <Int (2 ^Int 160)
     andBool 0 <=Int CALLER_ID andBool CALLER_ID <Int (2 ^Int 160)
     andBool 0 <=Int ORIGIN_ID andBool ORIGIN_ID <Int (2 ^Int 160)
     andBool F ==Int 1889567281 // TODO: auto gen
     andBool 0 <=Int O andBool O <Int (2 ^Int 160)
     andBool 0 <=Int B andBool B <Int (2 ^Int 256)
   //andBool G >Int 20000


  // Abstraction

//rule
//  <k> SHA3 MEMSTART MEMWIDTH => $keccak(#range(LM, MEMSTART, MEMWIDTH)) ~> #push ... </k>
//  <localMem> LM </localMem>
//  [trusted]

//rule
//  <k> CALLDATALOAD DATASTART => $asWord(CD [ DATASTART .. 32 ]) ~> #push ... </k>
//  <callData> CD </callData>
//  [trusted]

//rule
//  <k> MLOAD INDEX => $asWord(#range(LM, INDEX, 32)) ~> #push ... </k>
//  <localMem> LM </localMem>
//  [trusted]

//rule
//  <k> #asWord(int2wordstack(V, 32)) => V ... </k>
//  requires 0 <=Int V andBool V <Int (2 ^Int 256)
//  [trusted]

//rule
//  <k> $asWord(int2wordstack(V, 32)) => V ... </k>
//  requires 0 <=Int V andBool V <Int (2 ^Int 256)
//  [trusted]

//rule
//  <k> $asWord( nthbyteof(V,  0, 32)
//             : nthbyteof(V,  1, 32)
//             : nthbyteof(V,  2, 32)
//             : nthbyteof(V,  3, 32)
//             : nthbyteof(V,  4, 32)
//             : nthbyteof(V,  5, 32)
//             : nthbyteof(V,  6, 32)
//             : nthbyteof(V,  7, 32)
//             : nthbyteof(V,  8, 32)
//             : nthbyteof(V,  9, 32)
//             : nthbyteof(V, 10, 32)
//             : nthbyteof(V, 11, 32)
//             : nthbyteof(V, 12, 32)
//             : nthbyteof(V, 13, 32)
//             : nthbyteof(V, 14, 32)
//             : nthbyteof(V, 15, 32)
//             : nthbyteof(V, 16, 32)
//             : nthbyteof(V, 17, 32)
//             : nthbyteof(V, 18, 32)
//             : nthbyteof(V, 19, 32)
//             : nthbyteof(V, 20, 32)
//             : nthbyteof(V, 21, 32)
//             : nthbyteof(V, 22, 32)
//             : nthbyteof(V, 23, 32)
//             : nthbyteof(V, 24, 32)
//             : nthbyteof(V, 25, 32)
//             : nthbyteof(V, 26, 32)
//             : nthbyteof(V, 27, 32)
//             : nthbyteof(V, 28, 32)
//             : nthbyteof(V, 29, 32)
//             : nthbyteof(V, 30, 32)
//             : nthbyteof(V, 31, 32)
//             : .WordStack ) => V ... </k>
//  requires 0 <=Int V andBool V <Int (2 ^Int 256)
//  [trusted]

//rule
//  <k> #asWord(#padToWidth(32, int2wordstack(V, 4))) => V ... </k>
//  requires 0 <=Int V andBool V <Int (2 ^Int 32)
//  [trusted]

//rule
//  <k> $asWord(#padToWidth(32, int2wordstack(V, 4))) => V ... </k>
//  requires 0 <=Int V andBool V <Int (2 ^Int 32)
//  [trusted]

//rule
//  <k> $asWord( 0
//             : 0
//             : 0
//             : 0
//             : 0
//             : 0
//             : 0
//             : 0
//             : 0
//             : 0
//             : 0
//             : 0
//             : 0
//             : 0
//             : 0
//             : 0
//             : 0
//             : 0
//             : 0
//             : 0
//             : 0
//             : 0
//             : 0
//             : 0
//             : 0
//             : 0
//             : 0
//             : 0
//             : nthbyteof(V, 0, 4)
//             : nthbyteof(V, 1, 4)
//             : nthbyteof(V, 2, 4)
//             : nthbyteof(V, 3, 4)
//             : .WordStack ) => V ... </k>
//  requires 0 <=Int V andBool V <Int (2 ^Int 32)
//  [trusted]

//rule
//  <k> $keccak(int2wordstack(V, 32)) => hash(V) ... </k>
//  requires 0 <=Int V andBool V <Int (2 ^Int 256)
//  [trusted]

//rule
//  <k> $keccak( nthbyteof(V,  0, 32)
//             : nthbyteof(V,  1, 32)
//             : nthbyteof(V,  2, 32)
//             : nthbyteof(V,  3, 32)
//             : nthbyteof(V,  4, 32)
//             : nthbyteof(V,  5, 32)
//             : nthbyteof(V,  6, 32)
//             : nthbyteof(V,  7, 32)
//             : nthbyteof(V,  8, 32)
//             : nthbyteof(V,  9, 32)
//             : nthbyteof(V, 10, 32)
//             : nthbyteof(V, 11, 32)
//             : nthbyteof(V, 12, 32)
//             : nthbyteof(V, 13, 32)
//             : nthbyteof(V, 14, 32)
//             : nthbyteof(V, 15, 32)
//             : nthbyteof(V, 16, 32)
//             : nthbyteof(V, 17, 32)
//             : nthbyteof(V, 18, 32)
//             : nthbyteof(V, 19, 32)
//             : nthbyteof(V, 20, 32)
//             : nthbyteof(V, 21, 32)
//             : nthbyteof(V, 22, 32)
//             : nthbyteof(V, 23, 32)
//             : nthbyteof(V, 24, 32)
//             : nthbyteof(V, 25, 32)
//             : nthbyteof(V, 26, 32)
//             : nthbyteof(V, 27, 32)
//             : nthbyteof(V, 28, 32)
//             : nthbyteof(V, 29, 32)
//             : nthbyteof(V, 30, 32)
//             : nthbyteof(V, 31, 32)
//             : .WordStack ) => hash(V) ... </k>
//  requires 0 <=Int V andBool V <Int (2 ^Int 256)
//  [trusted]

//rule
//  <k> MSTORE L:Int V:Int => . ... </k>
//  <localMem>
//    M:Map
//  =>
//    M [  L          <- nthbyteof(V,  0, 32) ]
//      [ (L +Int  1) <- nthbyteof(V,  1, 32) ]
//      [ (L +Int  2) <- nthbyteof(V,  2, 32) ]
//      [ (L +Int  3) <- nthbyteof(V,  3, 32) ]
//      [ (L +Int  4) <- nthbyteof(V,  4, 32) ]
//      [ (L +Int  5) <- nthbyteof(V,  5, 32) ]
//      [ (L +Int  6) <- nthbyteof(V,  6, 32) ]
//      [ (L +Int  7) <- nthbyteof(V,  7, 32) ]
//      [ (L +Int  8) <- nthbyteof(V,  8, 32) ]
//      [ (L +Int  9) <- nthbyteof(V,  9, 32) ]
//      [ (L +Int 10) <- nthbyteof(V, 10, 32) ]
//      [ (L +Int 11) <- nthbyteof(V, 11, 32) ]
//      [ (L +Int 12) <- nthbyteof(V, 12, 32) ]
//      [ (L +Int 13) <- nthbyteof(V, 13, 32) ]
//      [ (L +Int 14) <- nthbyteof(V, 14, 32) ]
//      [ (L +Int 15) <- nthbyteof(V, 15, 32) ]
//      [ (L +Int 16) <- nthbyteof(V, 16, 32) ]
//      [ (L +Int 17) <- nthbyteof(V, 17, 32) ]
//      [ (L +Int 18) <- nthbyteof(V, 18, 32) ]
//      [ (L +Int 19) <- nthbyteof(V, 19, 32) ]
//      [ (L +Int 20) <- nthbyteof(V, 20, 32) ]
//      [ (L +Int 21) <- nthbyteof(V, 21, 32) ]
//      [ (L +Int 22) <- nthbyteof(V, 22, 32) ]
//      [ (L +Int 23) <- nthbyteof(V, 23, 32) ]
//      [ (L +Int 24) <- nthbyteof(V, 24, 32) ]
//      [ (L +Int 25) <- nthbyteof(V, 25, 32) ]
//      [ (L +Int 26) <- nthbyteof(V, 26, 32) ]
//      [ (L +Int 27) <- nthbyteof(V, 27, 32) ]
//      [ (L +Int 28) <- nthbyteof(V, 28, 32) ]
//      [ (L +Int 29) <- nthbyteof(V, 29, 32) ]
//      [ (L +Int 30) <- nthbyteof(V, 30, 32) ]
//      [ (L +Int 31) <- nthbyteof(V, 31, 32) ]
//  </localMem>
//  requires 0 <=Int V andBool V <Int (2 ^Int 256)
//  [trusted]

endmodule
