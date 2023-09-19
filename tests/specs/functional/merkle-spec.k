requires "evm.md"

module VERIFICATION
    imports EVM

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
    claim MerkleUpdate( .MerkleTree, .Bytes, V ) => MerkleLeaf( .Bytes, V ) requires V =/=String ""

    // Update on MerkleLeaf
    claim MerkleUpdate( MerkleLeaf( #parseByteStack("0x0607"), _ ), #parseByteStack("0x0607"), V ) => MerkleLeaf ( #parseByteStack("0x0607"), V )
      requires V =/=String ""

    claim MerkleUpdate( MerkleLeaf( #parseByteStack("0x0607"), _ ), #parseByteStack("0x0608"), V )
       => MerkleExtension( #parseByteStack("0x06"), ?_ )
      requires V =/=String ""

    claim MerkleUpdate( MerkleLeaf( #parseByteStack("0x05"), _ ), #parseByteStack("0x06"), V )
       => MerkleBranch( ?_, ?_ )
      requires V =/=String ""

    // Update on MerkleExtension
    claim MerkleUpdate( MerkleExtension( #parseByteStack("0x06"), .MerkleTree ), #parseByteStack("0x06"), V )
       => MerkleExtension( #parseByteStack("0x06"), MerkleLeaf( .Bytes, V ) )
      requires V =/=String ""

    claim MerkleUpdate( MerkleExtension( #parseByteStack("0x07"), _ ), #parseByteStack("0x06"), V )
       => MerkleBranch( ?_, ?_ )
      requires V =/=String ""

    claim MerkleUpdate( MerkleExtension( #parseByteStack("0x0708"), _ ), #parseByteStack("0x0709"), V )
       => MerkleExtension( #parseByteStack("0x07"), MerkleBranch( ?_, ?_ ) )
      requires V =/=String ""

    // Update on MerkleBranch
    claim MerkleUpdate( MerkleBranch( M, _ ), .Bytes, V ) => MerkleBranch( M, V ) requires V =/=String ""

    claim #merkleExtensionBuilder ( #parseByteStack("0e") , #parseByteStack("") , "verb" , #parseByteStack("0f0e") , "coin" )
       => MerkleExtension ( #parseByteStack("0e") , MerkleBranch ( 15 |-> MerkleLeaf ( #parseByteStack("0e") , "coin" ) , "verb" ) )

    ////////////////////////
    // MerkleDelete Tests //
    ////////////////////////

    claim Keccak256( #rlpEncodeMerkleTree( MerkleUpdate( #initTree, "de", "" ) ) )
       => "4ba393b447e1c78b2f647e10ae687de132f01f49d67e396bcdea4da2de05370f"

    claim Keccak256( #rlpEncodeMerkleTree( MerkleUpdate( #initTree, "becfe", "" ) ) )
       => "4ba393b447e1c78b2f647e10ae687de132f01f49d67e396bcdea4da2de05370f"

    claim Keccak256( #rlpEncodeMerkleTree( MerkleUpdate( #initTree, "def", "" ) ) )
       => "4ba393b447e1c78b2f647e10ae687de132f01f49d67e396bcdea4da2de05370f"

    claim Keccak256( #rlpEncodeMerkleTree( MerkleUpdate( #initTree, "defe", "" ) ) )
       => "4ba393b447e1c78b2f647e10ae687de132f01f49d67e396bcdea4da2de05370f"

    claim Keccak256( #rlpEncodeMerkleTree( MerkleUpdate( MerkleUpdate( #initTree, "defe", "" ), "becfe", "" ) ) )
       => "4ba393b447e1c78b2f647e10ae687de132f01f49d67e396bcdea4da2de05370f"

endmodule
