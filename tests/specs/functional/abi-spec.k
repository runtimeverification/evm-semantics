requires "abi.md"

module VERIFICATION
    imports EVM-ABI

    syntax Step ::= Bool | Bytes
 // ------------------------------

    syntax KItem ::= runLemma ( Step ) [symbol(runLemma)]
                   | doneLemma( Step )
 // --------------------------------------
    rule <k> runLemma( T ) => doneLemma( T ) ... </k>

endmodule

module ABI-SPEC
    imports VERIFICATION

 // EVM Type helper
 // ---------------

    // checking the function evaluation that went wrong in LLVM (issue booster-558)
    claim [isStaticType-fix-2371]:
      <k> runLemma ( #isStaticType( #bytes(b"\xe6\xe5/\xdd") ) ) => doneLemma ( false ) ... </k>

    claim [isStaticType-bytes-false]:
      <k> runLemma ( #isStaticType( #bytes(_) ) ) => doneLemma ( false ) ... </k>

    // checking the resulting #encodeArgs behaviour
    claim [encodeArgs-2371]:
      <k> runLemma ( #encodeArgs(#bytes(b"test")) )
            =>
          doneLemma (
                     b"\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00 "    // 32 (ASCII ' ', padded to 32 bytes)
              +Bytes b"\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x04" // 4 (length "test") padded to 32 bytes
              +Bytes b"test"                                                                                                                             // the actual byte payload
              +Bytes b"\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00"                 // ...padded to 32 bytes
          )
          ...
      </k>

    claim [sizeOfDynamicType-2455]:
      <k> runLemma(
        #sizeOfDynamicType(
          #array(
            #bytes(b"\x00"), 
            3, 
            #bytes(b"\xaa"), #bytes(b"\xbb\xbb"), #bytes(b"\xcc\xcc\xcc")
          )
        )
        ==Int
        lengthBytes(#enc(
          #array(
            #bytes(b"\x00"), 
            3, 
            #bytes(b"\xaa"), #bytes(b"\xbb\xbb"), #bytes(b"\xcc\xcc\xcc")
          )
        ))
      ) 
      => doneLemma(true) 
      ... 
      </k>

endmodule
