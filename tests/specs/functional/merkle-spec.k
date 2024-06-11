requires "evm.md"

module VERIFICATION
    imports EVM

    syntax StepSort ::= MerkleTree | String | Int
    syntax    KItem ::= runLemma ( StepSort ) [symbol(runLemma)]
                      | doneLemma( StepSort )
 // -----------------------------------------
    rule <k> runLemma( T ) => doneLemma( T ) ... </k>

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
    claim <k> runLemma ( MerkleUpdate( .MerkleTree, .Bytes, V ) )
           => doneLemma( MerkleLeaf( .Bytes, V ) ) ... </k>
      requires V =/=String ""

    // Update on MerkleLeaf
    claim <k> runLemma ( MerkleUpdate( MerkleLeaf( #parseByteStack("0x0607"), _ ), #parseByteStack("0x0607"), V ) )
           => doneLemma( MerkleLeaf ( #parseByteStack("0x0607"), V ) ) ... </k>
      requires V =/=String ""

    claim <k> runLemma ( MerkleUpdate( MerkleLeaf( #parseByteStack("0x0607"), _ ), #parseByteStack("0x0608"), V ) )
           => doneLemma( MerkleExtension( #parseByteStack("0x06"), ?_ ) ) ... </k>
      requires V =/=String ""

    claim <k> runLemma ( MerkleUpdate( MerkleLeaf( #parseByteStack("0x05"), _ ), #parseByteStack("0x06"), V ) )
           => doneLemma( MerkleBranch( ?_, ?_ ) ) ... </k>
      requires V =/=String ""

    // Update on MerkleExtension
    claim <k> runLemma ( MerkleUpdate( MerkleExtension( #parseByteStack("0x06"), .MerkleTree ), #parseByteStack("0x06"), V ) )
           => doneLemma( MerkleExtension( #parseByteStack("0x06"), MerkleLeaf( .Bytes, V ) ) ) ... </k>
      requires V =/=String ""

    claim <k> runLemma ( MerkleUpdate( MerkleExtension( #parseByteStack("0x07"), _ ), #parseByteStack("0x06"), V ) )
           => doneLemma( MerkleBranch( ?_, ?_ ) ) ... </k>
      requires V =/=String ""

    claim <k> runLemma ( MerkleUpdate( MerkleExtension( #parseByteStack("0x0708"), _ ), #parseByteStack("0x0709"), V ) )
           => doneLemma( MerkleExtension( #parseByteStack("0x07"), MerkleBranch( ?_, ?_ ) ) ) ... </k>
      requires V =/=String ""

    // Update on MerkleBranch
    claim <k> runLemma ( MerkleUpdate( MerkleBranch( M, _ ), .Bytes, V ) )
           => doneLemma( MerkleBranch( M, V ) ) ... </k>
      requires V =/=String ""

    claim <k> runLemma  ( #merkleExtensionBuilder ( #parseByteStack("0e") , #parseByteStack("") , "verb" , #parseByteStack("0f0e") , "coin" ) )
           => doneLemma ( MerkleExtension ( #parseByteStack("0e") , MerkleBranch ( 15 |-> MerkleLeaf ( #parseByteStack("0e") , "coin" ) , "verb" ) ) ) ... </k>

    ////////////////////////
    // MerkleDelete Tests //
    ////////////////////////

    claim <k> runLemma ( Keccak256( #rlpEncodeMerkleTree( MerkleUpdate( #initTree, "de", "" ) ) ) )
           => doneLemma( "4ba393b447e1c78b2f647e10ae687de132f01f49d67e396bcdea4da2de05370f" ) ... </k>

    claim <k> runLemma ( Keccak256( #rlpEncodeMerkleTree( MerkleUpdate( #initTree, "becfe", "" ) ) ) )
           => doneLemma( "4ba393b447e1c78b2f647e10ae687de132f01f49d67e396bcdea4da2de05370f" ) ... </k>

    claim <k> runLemma ( Keccak256( #rlpEncodeMerkleTree( MerkleUpdate( #initTree, "def", "" ) ) ) )
           => doneLemma( "4ba393b447e1c78b2f647e10ae687de132f01f49d67e396bcdea4da2de05370f" ) ... </k>

    claim <k> runLemma ( Keccak256( #rlpEncodeMerkleTree( MerkleUpdate( #initTree, "defe", "" ) ) ) )
           => doneLemma( "4ba393b447e1c78b2f647e10ae687de132f01f49d67e396bcdea4da2de05370f" ) ... </k>

    claim <k> runLemma ( Keccak256( #rlpEncodeMerkleTree( MerkleUpdate( MerkleUpdate( #initTree, "defe", "" ), "becfe", "" ) ) ) )
           => doneLemma( "4ba393b447e1c78b2f647e10ae687de132f01f49d67e396bcdea4da2de05370f" ) ... </k>

endmodule
