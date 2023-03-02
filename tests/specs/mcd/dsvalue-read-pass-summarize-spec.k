requires "verification.k"

module DSVALUE-READ-PASS-SUMMARIZE-SPEC
    imports VERIFICATION

// Prove that all paths of execution for Dai.read fail
// 333s
//    claim [DSValue.read.pass]:
//      <k> #execute => #halt ... </k>
//      <schedule> ISTANBUL </schedule>
//      <evm>
//        <statusCode> _ => ?FAILURE:EndStatusCode </statusCode>
//        <callState>
//          <id> ACCT_ID </id>
//          <program> DSValue_bin_runtime </program>
//          <jumpDests> #computeValidJumpDests(DSValue_bin_runtime) </jumpDests>
//          <callData> #abiCallData("read", .TypedArgs) +Bytes CD => ?_ </callData>
//          <gas> #gas(VGas) => ?_ </gas>
//          <pc> 0 => ?_ </pc>
//          <wordStack> .WordStack => ?_ </wordStack>
//          <localMem> .Bytes => ?_ </localMem>
//          <memoryUsed> 0 => ?_ </memoryUsed>
//          (_ => ?_)
//        </callState>
//        (_ => ?_)
//      </evm>
//      <account>
//        <acctID> ACCT_ID </acctID>
//        <storage> ACCT_STORAGE => ?_ </storage>
//        (_ => ?_)
//      </account>
//      ensures ?FAILURE =/=K EVMC_SUCCESS

// Counter-example provided by prover
// #Not( { 255 &Int #lookup( ACCT_STORAGE , 1 ) /Int 1461501637330902918203684832716283019655932542976 #Equals 0 } )
// #And <generatedTop>
//   <kevm>
//     <k>
//           #halt
//       ~> _DotVar2
//     </k>
//     <schedule>
//       ISTANBUL
//     </schedule>
//     <ethereum>
//       <evm>
//         <output>
//           #buf( 32 , #lookup( ACCT_STORAGE , 2 ) )
//         </output>
//         <statusCode>
//           EVMC SUCCESS
//         </statusCode>
//           284
//         <callState>
//           <program> DSValue_bin_runtime </program>
//           <jumpDests> #computeValidJumpDests(DSValue_bin_runtime) </jumpDests>
//           <id>
//             ACCT_ID
//           </id>
//           <callData>
//             b"W\xde&\xa4" +Bytes CD
//           </callData>
//           <callValue>
//             0
//           </callValue>
//           <wordStack>
//             1474176676 : .WordStack
//           </wordStack>
//           <localMem>
//             b"\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x80" [ 128 := #buf( 32 , #lookup( ACCT_STORAGE , 2 ) ) ]
//           </localMem>
//           <pc>
//             284
//           </pc>
//           <gas>
//             #gas( VGas +Int -2043 )
//           </gas>
//           <memoryUsed>
//             5
//           </memoryUsed>
//           ...
//         </callState>
//         ...
//       </evm>
//       <network>
//         <accounts>
//           AccountCellMapItem( <acctID>
//             ACCT_ID
//           </acctID> , <account>
//             <acctID>
//               ACCT_ID
//             </acctID>
//             <storage>
//               ACCT_STORAGE
//             </storage>
//             ...
//           </account> ) _DotVar5
//         </accounts>
//         ...
//       </network>
//     </ethereum>
//     ...
//   </kevm>
//   ...
// </generatedTop>
// #And { false #Equals <acctID>
//   ACCT_ID
// </acctID> in _DotVar5 keys( ) }

// Converted to summary
// 313s
    claim [DSValue.read.pass]:
      <k> #execute => #halt ... </k>
      <schedule> ISTANBUL </schedule>
      <evm>
        <output> _ => #buf(32, #lookup(ACCT_STORAGE, 2)) </output>              // from counterexample
        <statusCode> _ => EVMC_SUCCESS </statusCode>
        <callState>
          <id> ACCT_ID </id>
          <program> DSValue_bin_runtime </program>
          <jumpDests> #computeValidJumpDests(DSValue_bin_runtime) </jumpDests>
          <callData> #abiCallData("read", .TypedArgs) +Bytes _CD => ?_ </callData>
          <callValue> 0 </callValue>                                            // from counterexample
          <gas> #gas(VGas) => #gas(VGas +Int -2043) </gas>                      // from counterexample
          <pc> 0 => ?_ </pc>
          <wordStack> .WordStack => ?_ </wordStack>
          <localMem> .Bytes => ?_ </localMem>
          <memoryUsed> 0 => ?_ </memoryUsed>
          (_ => ?_)
        </callState>
        (_ => ?_)
      </evm>
      <account>
        <acctID> ACCT_ID </acctID>
        <storage> ACCT_STORAGE => ?_ </storage>
        (_ => ?_)
      </account>
      requires notBool (255 &Int (#lookup( ACCT_STORAGE , 1 ) /Int 1461501637330902918203684832716283019655932542976)) ==Int 0 // from counterexample

endmodule
