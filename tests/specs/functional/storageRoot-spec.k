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

    rule <k> runMerkle( Keccak256( #rlpEncodeMerkleTree( #storageRoot(
              #hashedLocation( "Vyper", 0, 0 )                                                  |-> 1234
              #hashedLocation( "Solidity", 1, 325916061853536256927665635852894456676216705688) |-> 5678
                                                                     )
                                                       )
                                 )
                      )
          => doneMerkle( "9a92147e80919ad37d3f96943fd8f613be1381ce140251216ea566b080ac81f0" )
         </k>
endmodule
