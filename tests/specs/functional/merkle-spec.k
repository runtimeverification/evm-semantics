requires "evm.md"

module VERIFICATION
    imports EVM

    syntax StepSort ::= MerkleTree | String
    syntax    KItem ::= runMerkle ( StepSort )
                      | doneMerkle( StepSort )
 // ------------------------------------------
    rule runMerkle( T ) => doneMerkle( T )

    syntax MerkleTree ::= "#initTree" [function]
 // --------------------------------------------
    rule #initTree => MerkleUpdateMap( .MerkleTree,
                                       #parseByteStack( "do" )    |-> "verb"
                                       #parseByteStack( "dog" )   |-> "puppy"
                                       #parseByteStack( "doge" )  |-> "coin"
                                       #parseByteStack( "horse" ) |-> "stallion"
                                     )
endmodule

module MERKLE-SPEC
    imports VERIFICATION

    ////////////////////
    // Symbolic Tests //
    ////////////////////
    rule <k> runMerkle ( MerkleUpdate( .MerkleTree, .ByteArray, V ) )
          => doneMerkle( MerkleLeaf( .ByteArray, V ) ) </k>
      requires V =/=String ""

    // Update on MerkleLeaf
    rule <k> runMerkle ( MerkleUpdate( MerkleLeaf( #parseByteStack("0x0607"), _ ), #parseByteStack("0x0607"), V ) )
          => doneMerkle( MerkleLeaf ( #parseByteStack("0x0607"), V ) ) </k>
      requires V =/=String ""

    rule <k> runMerkle ( MerkleUpdate( MerkleLeaf( #parseByteStack("0x0607"), _ ), #parseByteStack("0x0608"), V ) )
          => doneMerkle( MerkleExtension( #parseByteStack("0x06"), ?_ ) ) </k>
      requires V =/=String ""

    rule <k> runMerkle ( MerkleUpdate( MerkleLeaf( #parseByteStack("0x05"), _ ), #parseByteStack("0x06"), V ) )
          => doneMerkle( MerkleBranch( ?_, ?_ ) ) </k>
      requires V =/=String ""

    // Update on MerkleExtension
    rule <k> runMerkle ( MerkleUpdate( MerkleExtension( #parseByteStack("0x06"), .MerkleTree ), #parseByteStack("0x06"), V ) )
          => doneMerkle( MerkleExtension( #parseByteStack("0x06"), MerkleLeaf( .ByteArray, V ) ) ) </k>
      requires V =/=String ""

    rule <k> runMerkle ( MerkleUpdate( MerkleExtension( #parseByteStack("0x07"), _ ), #parseByteStack("0x06"), V ) )
          => doneMerkle( MerkleBranch( ?_, ?_ ) ) </k>
      requires V =/=String ""

    rule <k> runMerkle ( MerkleUpdate( MerkleExtension( #parseByteStack("0x0708"), _ ), #parseByteStack("0x0709"), V ) )
          => doneMerkle( MerkleExtension( #parseByteStack("0x07"), MerkleBranch( ?_, ?_ ) ) ) </k>
      requires V =/=String ""

    // Update on MerkleBranch
    rule <k> runMerkle ( MerkleUpdate( MerkleBranch( M, _ ), .ByteArray, V ) )
          => doneMerkle( MerkleBranch( M, V ) ) </k>
      requires V =/=String ""

    ////////////////////
    // Concrete Tests //
    ////////////////////
    rule <k> runMerkle( Keccak256( #rlpEncodeMerkleTree( MerkleUpdateMap( .MerkleTree,
               #parseByteStack( "do" )    |-> "verb"
               #parseByteStack( "dog" )   |-> "puppy"
               #parseByteStack( "doge" )  |-> "coin"
               #parseByteStack( "horse" ) |-> "stallion"
                                                                        )
                                                       )
                                 )
                      )
          => doneMerkle( "5991bb8c6514148a29db676a14ac506cd2cd5775ace63c30a4fe457715e9ac84" )
         </k>

    ////////////////////////
    // MerkleDelete Tests //
    ////////////////////////
    rule <k> runMerkle ( Keccak256( #rlpEncodeMerkleTree( MerkleUpdate( #initTree, "do", "" ) ) ) )
          => doneMerkle( "72543939c0b0dbc3bb86f81f14b9b7e7ea80eac1613ad59820b6d692ce1764d3" ) </k>

    rule <k> runMerkle ( Keccak256( #rlpEncodeMerkleTree( MerkleUpdate( #initTree, "horse", "" ) ) ) )
          => doneMerkle( "ef7b2fe20f5d2c30c46ad4d83c39811bcbf1721aef2e805c0e107947320888b6" ) </k>

    rule <k> runMerkle ( Keccak256( #rlpEncodeMerkleTree( MerkleUpdate( #initTree, "dog", "" ) ) ) )
          => doneMerkle( "2d09ab2a260088a5558f754511c9060bd6cd62ab5d3c10a15a9c0fced52add40" ) </k>

    rule <k> runMerkle ( Keccak256( #rlpEncodeMerkleTree( MerkleUpdate( #initTree, "doge", "" ) ) ) )
          => doneMerkle( "40b4a841a5ed78d2beb33a3dbba6dd38f5b1566db97ae643e073ded3aa77dceb" ) </k>

    rule <k> runMerkle ( Keccak256( #rlpEncodeMerkleTree( MerkleUpdate( MerkleUpdate( #initTree, "doge", "" ), "horse", "" ) ) ) )
          => doneMerkle( "779db3986dd4f38416bfde49750ef7b13c6ecb3e2221620bcad9267e94604d36" ) </k>
endmodule
