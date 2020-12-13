requires "verification.k"

module FUNCTIONAL-SPEC-SYNTAX
    imports VERIFICATION

    syntax KItem ::= runLemma ( Step ) | doneLemma ( Step )
 // -------------------------------------------------------
    rule <k> runLemma(S) => doneLemma(S) ... </k>

    syntax Step ::= Bool | Int | ByteArray | Memory
 // -----------------------------------------------

endmodule

module FUNCTIONAL-SPEC
    imports FUNCTIONAL-SPEC-SYNTAX

    // WordPack

    claim <k> runLemma((GAL |Int (notAddrMask &Int GUY_TIC_END)) modInt pow256) => doneLemma(GAL |Int (notAddrMask &Int GUY_TIC_END)) ... </k>
      requires #rangeUInt(256, GUY_TIC_END)
       andBool #rangeAddress(GAL)

    claim <k> runLemma(TIME +Int (TTL_TAU /Int pow48)) => doneLemma(TIME +Int TAU) ... </k>
      requires TTL_TAU ==Int #WordPackUInt48UInt48(TTL, TAU)
       andBool #rangeUInt(48, TIME +Int TAU)

    claim <k> runLemma(maxUInt48 &Int ((GAL |Int (notAddrMask &Int GUY_TIC_END)) /Int pow160)) => doneLemma(TIC) ... </k>
      requires GUY_TIC_END ==Int #WordPackAddrUInt48UInt48(GUY, TIC, END)
       andBool #rangeAddress(GAL)

    claim <k> runLemma(maxUInt160 &Int (GAL |Int (notAddrMask &Int GUY_TIC_END))) => doneLemma(GAL) ... </k>
      requires GUY_TIC_END ==Int #WordPackAddrUInt48UInt48(GUY, TIC, END)
       andBool #rangeAddress(GAL)

    claim <k> runLemma((((TIME +Int (maxUInt48 &Int (TTL_TAU /Int pow48))) *Int pow208) |Int (maxUInt208 &Int (GAL |Int (notAddrMask &Int GUY_TIC_END)))))
           => doneLemma(#WordPackAddrUInt48UInt48(GAL, TIC, TIME +Int TAU))
          ...
          </k>
      requires TTL_TAU     ==Int #WordPackUInt48UInt48(TTL, TAU)
       andBool GUY_TIC_END ==Int #WordPackAddrUInt48UInt48(GUY, TIC, END)
       andBool #rangeAddress(GAL)
       andBool #rangeUInt(48, TIME +Int TAU)

    // Memory operations

    claim <k> runLemma(#range(M:Memory [ 0 := #buf(4, X) ] [ 0 <- 10 ] [ 1 <- 11 ] [ 2 <- 12 ] [ 3 <- 13 ], 0, 4)) => doneLemma(10 : 11 : 12 : 13 : .ByteArray) ... </k>

    claim <k> runLemma(M:Memory [ 128 := (B1 : B2 : B3 : B4 : _     : .ByteArray) ] [ 132 := BA':ByteArray ]) => doneLemma(M [ 128 := (B1 : B2 : B3 : B4 : .ByteArray) ] [ 132 := BA' ]) ... </k> requires #sizeByteArray(BA') ==Int 32
    claim <k> runLemma(M:Memory [ 128 := (B1 : B2 : B3 : B4 : _ : _ : .ByteArray) ] [ 132 := BA':ByteArray ]) => doneLemma(M [ 128 := (B1 : B2 : B3 : B4 : .ByteArray) ] [ 132 := BA' ]) ... </k> requires #sizeByteArray(BA') ==Int 32

endmodule
