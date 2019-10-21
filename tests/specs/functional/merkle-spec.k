requires "evm.k"

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

    rule <k> runMerkle ( MerkleUpdate( .MerkleTree, .WordStack, VALUE ) )
          => doneMerkle( MerkleLeaf( .WordStack, VALUE ) ) </k>

    // Update on MerkleLeaf
    rule <k> runMerkle ( MerkleUpdate( MerkleLeaf( 6 : 7 : .WordStack, _ ), 6 : 7 : .WordStack, V ) )
          => doneMerkle( MerkleLeaf ( 6 : 7 : .WordStack, V ) ) </k>

    rule <k> runMerkle ( MerkleUpdate( MerkleLeaf( 6 : 7 : .WordStack, _ ), 6 : 8 : .WordStack, _ ) )
          => doneMerkle( MerkleExtension( 6 : .WordStack, _ ) ) </k>

    rule <k> runMerkle ( MerkleUpdate( MerkleLeaf( 5 : .WordStack, _ ), 6 : .WordStack, _ ) )
          => doneMerkle( MerkleBranch( _, _ ) ) </k>

    // Update on MerkleExtension
    rule <k> runMerkle ( MerkleUpdate( MerkleExtension( 6 : .WordStack, .MerkleTree ), 6 : .WordStack, V ) )
          => doneMerkle( MerkleExtension( 6 : .WordStack, MerkleLeaf( .WordStack, V ) ) ) </k>

    rule <k> runMerkle ( MerkleUpdate( MerkleExtension( 7 : .WordStack, _ ), 6 : .WordStack, _ ) )
          => doneMerkle( MerkleBranch( _, _ ) ) </k>

    rule <k> runMerkle ( MerkleUpdate( MerkleExtension( 7 : 8 : .WordStack, _ ), 7 : 9 : .WordStack, _ ) )
          => doneMerkle( MerkleExtension( 7 : .WordStack, MerkleBranch( _, _ ) ) ) </k>

    // Update on MerkleBranch
    rule <k> runMerkle ( MerkleUpdate( MerkleBranch( M, _ ), .WordStack, V ) )
          => doneMerkle( MerkleBranch( M, V ) ) </k>

    rule <k> runMerkle ( .MerkleBranch )
          => doneMerkle( MerkleBranch (  0 |-> .MerkleTree  1 |-> .MerkleTree  2 |-> .MerkleTree  3 |-> .MerkleTree
                                         4 |-> .MerkleTree  5 |-> .MerkleTree  6 |-> .MerkleTree  7 |-> .MerkleTree
                                         8 |-> .MerkleTree  9 |-> .MerkleTree 10 |-> .MerkleTree 11 |-> .MerkleTree
                                        12 |-> .MerkleTree 13 |-> .MerkleTree 14 |-> .MerkleTree 15 |-> .MerkleTree
                                      , ""
                                      )
                       )
         </k>

    // Concrete Test
    rule <k> runMerkle ( Keccak256( #rlpEncodeMerkleTree( MerkleUpdate( MerkleUpdate( MerkleUpdate( MerkleUpdate( .MerkleTree, "do", "verb" ), "horse", "stallion" ), "doge", "coin" ), "dog", "puppy" ) ) ) )
          => doneMerkle( "5991bb8c6514148a29db676a14ac506cd2cd5775ace63c30a4fe457715e9ac84" ) </k>

endmodule
