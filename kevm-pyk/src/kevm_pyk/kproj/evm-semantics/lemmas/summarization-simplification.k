requires "../serialization.md"

module SUMMARIZATION-SIMPLIFICATION
    imports INT
    imports BOOL
    imports SERIALIZATION

  // ###########################################################################
  // log2Int
  // ###########################################################################

    rule #Ceil ( log2Int ( X:Int ) ) => { true #Equals X >Int 0 } [simplification]

  // ###########################################################################
  // newAddr
  // ###########################################################################

    rule [#newAddr-definedness]: #Ceil(#newAddr(@ACCT, @NONCE)) => #Ceil(@ACCT) #And #Ceil(@NONCE) [simplification]

endmodule
