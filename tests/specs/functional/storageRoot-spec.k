requires "evm.k"
requires "edsl.k"

module VERIFICATION
    imports EVM
    imports EDSL

    syntax StepSort ::= MerkleTree | String
    syntax    KItem ::= runMerkle ( StepSort )
                      | doneMerkle( StepSort )
 // ------------------------------------------
    rule runMerkle( T ) => doneMerkle( T )

endmodule

module STORAGEROOT-SPEC
    imports VERIFICATION

    rule <k> runMerkle( #storageRoot( .Map ) )
          => doneMerkle( .MerkleTree )
         </k>

    // uint                                     pos0;
    // mapping (uint => uint)                   pos1;
    // uint                                     pos2;
    // mapping (uint => mapping (uint => uint)) pos3;
    //
    // pos0       = 1234;
    // pos1[0]    = 0;
    // pos1[1]    = 1;
    // pos2       = 100;
    // pos3[0][0] = 42;
    // pos3[2][1] = 2019;
    rule <k> runMerkle( Keccak256( #rlpEncodeMerkleTree( #storageRoot(
              #hashedLocation( "Solidity", 0, .IntList ) |-> 1234
              #hashedLocation( "Solidity", 1, 0 )        |-> 0
              #hashedLocation( "Solidity", 1, 1 )        |-> 1
              #hashedLocation( "Solidity", 2, .IntList ) |-> 100
              #hashedLocation( "Solidity", 3, 0 0 )      |-> 42
              #hashedLocation( "Solidity", 3, 2 1 )      |-> 2019
                                                                     )
                                                       )
                                 )
                      )
          => doneMerkle( "6786e17b1f185ba3b51ec15f28526a1d47d74052ca98c1b8edf7cdc6243eebba" )
         </k>
endmodule
