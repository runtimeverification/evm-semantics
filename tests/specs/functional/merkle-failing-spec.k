requires "evm.md"

module VERIFICATION
    imports EVM

    syntax StepSort ::= MerkleTree | String
    syntax    KItem ::= runMerkle ( StepSort )
                      | doneMerkle( StepSort )
 // ------------------------------------------
    rule runMerkle( T ) => doneMerkle( T )

endmodule

module MERKLE-FAILING-SPEC
    imports VERIFICATION

    // Concrete Test
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
endmodule
