requires "evm.md"

module VERIFICATION
    imports EVM

    syntax StepSort ::= MerkleTree | String | Int
    syntax    KItem ::= runMerkle ( StepSort )
                      | doneMerkle( StepSort )
 // ------------------------------------------
    rule <k> runMerkle( T ) => doneMerkle( T ) ... </k>

    syntax MerkleTree ::= "#initTree" [macro]
 // -----------------------------------------
    rule #initTree => MerkleUpdateMap( .MerkleTree,
                                       .Map [ #parseByteStack( "de" )    <- "verb"     ]
                                            [ #parseByteStack( "def" )   <- "puppy"    ]
                                            [ #parseByteStack( "defe" )  <- "coin"     ]
                                            [ #parseByteStack( "becfe" ) <- "stallion" ]
                                     )
endmodule

module MERKLE-SPEC
    imports VERIFICATION

    ////////////////////
    // Symbolic Tests //
    ////////////////////
    claim <k> runMerkle ( MerkleUpdate( .MerkleTree, .Bytes, V ) )
           => doneMerkle( MerkleLeaf( .Bytes, V ) ) </k>
      requires V =/=String ""

    // Update on MerkleLeaf
    claim <k> runMerkle ( MerkleUpdate( MerkleLeaf( #parseByteStack("0x0607"), _ ), #parseByteStack("0x0607"), V ) )
           => doneMerkle( MerkleLeaf ( #parseByteStack("0x0607"), V ) ) </k>
      requires V =/=String ""

    claim <k> runMerkle ( MerkleUpdate( MerkleLeaf( #parseByteStack("0x0607"), _ ), #parseByteStack("0x0608"), V ) )
           => doneMerkle( MerkleExtension( #parseByteStack("0x06"), ?_ ) ) </k>
      requires V =/=String ""

    claim <k> runMerkle ( MerkleUpdate( MerkleLeaf( #parseByteStack("0x05"), _ ), #parseByteStack("0x06"), V ) )
           => doneMerkle( MerkleBranch( ?_, ?_ ) ) </k>
      requires V =/=String ""

    // Update on MerkleExtension
    claim <k> runMerkle ( MerkleUpdate( MerkleExtension( #parseByteStack("0x06"), .MerkleTree ), #parseByteStack("0x06"), V ) )
           => doneMerkle( MerkleExtension( #parseByteStack("0x06"), MerkleLeaf( .Bytes, V ) ) ) </k>
      requires V =/=String ""

    claim <k> runMerkle ( MerkleUpdate( MerkleExtension( #parseByteStack("0x07"), _ ), #parseByteStack("0x06"), V ) )
           => doneMerkle( MerkleBranch( ?_, ?_ ) ) </k>
      requires V =/=String ""

    claim <k> runMerkle ( MerkleUpdate( MerkleExtension( #parseByteStack("0x0708"), _ ), #parseByteStack("0x0709"), V ) )
           => doneMerkle( MerkleExtension( #parseByteStack("0x07"), MerkleBranch( ?_, ?_ ) ) ) </k>
      requires V =/=String ""

    // Update on MerkleBranch
    claim <k> runMerkle ( MerkleUpdate( MerkleBranch( M, _ ), .Bytes, V ) )
           => doneMerkle( MerkleBranch( M, V ) ) </k>
      requires V =/=String ""

    claim <k> runMerkle  ( #merkleExtensionBuilder ( #parseByteStack("0e") , #parseByteStack("") , "verb" , #parseByteStack("0f0e") , "coin" ) )
           => doneMerkle ( MerkleExtension ( #parseByteStack("0e") , MerkleBranch ( 15 |-> MerkleLeaf ( #parseByteStack("0e") , "coin" ) , "verb" ) ) ) </k>

    ////////////////////////
    // MerkleDelete Tests //
    ////////////////////////

    claim <k> runMerkle ( Keccak256( #rlpEncodeMerkleTree( MerkleUpdate( #initTree, "de", "" ) ) ) )
           => doneMerkle( "4ba393b447e1c78b2f647e10ae687de132f01f49d67e396bcdea4da2de05370f" ) </k>

    claim <k> runMerkle ( Keccak256( #rlpEncodeMerkleTree( MerkleUpdate( #initTree, "becfe", "" ) ) ) )
           => doneMerkle( "4ba393b447e1c78b2f647e10ae687de132f01f49d67e396bcdea4da2de05370f" ) </k>

    claim <k> runMerkle ( Keccak256( #rlpEncodeMerkleTree( MerkleUpdate( #initTree, "def", "" ) ) ) )
           => doneMerkle( "4ba393b447e1c78b2f647e10ae687de132f01f49d67e396bcdea4da2de05370f" ) </k>

    claim <k> runMerkle ( Keccak256( #rlpEncodeMerkleTree( MerkleUpdate( #initTree, "defe", "" ) ) ) )
           => doneMerkle( "4ba393b447e1c78b2f647e10ae687de132f01f49d67e396bcdea4da2de05370f" ) </k>

    claim <k> runMerkle ( Keccak256( #rlpEncodeMerkleTree( MerkleUpdate( MerkleUpdate( #initTree, "defe", "" ), "becfe", "" ) ) ) )
           => doneMerkle( "4ba393b447e1c78b2f647e10ae687de132f01f49d67e396bcdea4da2de05370f" ) </k>

endmodule
