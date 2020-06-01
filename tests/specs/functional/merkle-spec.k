requires "evm.md"

module VERIFICATION
    imports EVM

    syntax StepSort ::= MerkleTree | String
    syntax    KItem ::= runMerkle ( StepSort )
                      | doneMerkle( StepSort )
 // ------------------------------------------
    rule runMerkle( T ) => doneMerkle( T )

endmodule

module MERKLE-SPEC
    imports VERIFICATION

    rule <k> runMerkle ( MerkleUpdate( .MerkleTree, .ByteArray, VALUE ) )
          => doneMerkle( MerkleLeaf( .ByteArray, VALUE ) ) </k>

    // Update on MerkleLeaf
    rule <k> runMerkle ( MerkleUpdate( MerkleLeaf( #parseByteStack("0x0607"), _ ), #parseByteStack("0x0607"), V ) )
          => doneMerkle( MerkleLeaf ( #parseByteStack("0x0607"), V ) ) </k>

    rule <k> runMerkle ( MerkleUpdate( MerkleLeaf( #parseByteStack("0x0607"), _ ), #parseByteStack("0x0608"), _ ) )
          => doneMerkle( MerkleExtension( #parseByteStack("0x06"), ?_ ) ) </k>

    rule <k> runMerkle ( MerkleUpdate( MerkleLeaf( #parseByteStack("0x05"), _ ), #parseByteStack("0x06"), _ ) )
          => doneMerkle( MerkleBranch( ?_, ?_ ) ) </k>

    // Update on MerkleExtension
    rule <k> runMerkle ( MerkleUpdate( MerkleExtension( #parseByteStack("0x06"), .MerkleTree ), #parseByteStack("0x06"), V ) )
          => doneMerkle( MerkleExtension( #parseByteStack("0x06"), MerkleLeaf( .ByteArray, V ) ) ) </k>

    rule <k> runMerkle ( MerkleUpdate( MerkleExtension( #parseByteStack("0x07"), _ ), #parseByteStack("0x06"), _ ) )
          => doneMerkle( MerkleBranch( ?_, ?_ ) ) </k>

    rule <k> runMerkle ( MerkleUpdate( MerkleExtension( #parseByteStack("0x0708"), _ ), #parseByteStack("0x0709"), _ ) )
          => doneMerkle( MerkleExtension( #parseByteStack("0x07"), MerkleBranch( ?_, ?_ ) ) ) </k>

    // Update on MerkleBranch
    rule <k> runMerkle ( MerkleUpdate( MerkleBranch( M, _ ), .ByteArray, V ) )
          => doneMerkle( MerkleBranch( M, V ) ) </k>
endmodule
