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

    // Arithmetic

    claim <k> runLemma((X +Int pow256) -Int chop(Y)) => doneLemma(X -Int Y) ... </k>
      requires #rangeUInt(256, X)
       andBool #rangeSInt(256, Y)
       andBool Y <Int 0

    claim <k> runLemma(chop(Art_i *Int (ABI_rate +Int pow256))) => doneLemma(chop(Art_i *Int ABI_rate)) ... </k>
      requires #rangeUInt(256, Art_i)
       andBool Art_i <=Int maxSInt256
       andBool #rangeSInt(256, Art_i *Int ABI_rate)

    // WordPack

    claim <k> runLemma((GAL |Int (maskWordPackAddrUInt48UInt48_1 &Int GUY_TIC_END)) modInt pow256) => doneLemma(GAL |Int (maskWordPackAddrUInt48UInt48_1 &Int GUY_TIC_END)) ... </k>
      requires #rangeUInt(256, GUY_TIC_END)
       andBool #rangeAddress(GAL)

    claim <k> runLemma(TIME +Int (TTL_TAU /Int pow48)) => doneLemma(TIME +Int TAU) ... </k>
      requires TTL_TAU ==Int #WordPackUInt48UInt48(TTL, TAU)
       andBool #rangeUInt(48, TIME +Int TAU)

    claim <k> runLemma(maxUInt48 &Int ((GAL |Int (maskWordPackAddrUInt48UInt48_1 &Int GUY_TIC_END)) /Int pow160)) => doneLemma(TIC) ... </k>
      requires GUY_TIC_END ==Int #WordPackAddrUInt48UInt48(GUY, TIC, END)
       andBool #rangeAddress(GAL)

    claim <k> runLemma(maxUInt160 &Int (GAL |Int (maskWordPackAddrUInt48UInt48_1 &Int GUY_TIC_END))) => doneLemma(GAL) ... </k>
      requires GUY_TIC_END ==Int #WordPackAddrUInt48UInt48(GUY, TIC, END)
       andBool #rangeAddress(GAL)

    claim <k> runLemma((((TIME +Int (maxUInt48 &Int (TTL_TAU /Int pow48))) *Int pow208) |Int (maxUInt208 &Int (GAL |Int (maskWordPackAddrUInt48UInt48_1 &Int GUY_TIC_END))))) => doneLemma(#WordPackAddrUInt48UInt48(GAL, TIC, TIME +Int TAU)) ... </k>
      requires TTL_TAU     ==Int #WordPackUInt48UInt48(TTL, TAU)
       andBool GUY_TIC_END ==Int #WordPackAddrUInt48UInt48(GUY, TIC, END)
       andBool #rangeAddress(GAL)
       andBool #rangeUInt(48, TIME +Int TAU)

    claim <k> runLemma((((TIME +Int (maxUInt48 &Int TTL_TAU)) *Int pow160) |Int (maskWordPackAddrUInt48UInt48_2 &Int GUY_TIC_END))) => doneLemma(#WordPackAddrUInt48UInt48(GUY, TIME +Int TTL, END)) ... </k>
      requires TTL_TAU     ==Int #WordPackUInt48UInt48(TTL, TAU)
       andBool GUY_TIC_END ==Int #WordPackAddrUInt48UInt48(GUY, TIC, END)
       andBool #rangeUInt(48, TIME +Int TTL)

    claim <k> runLemma(maxUInt48 &Int ((CALLER_ID |Int (maskWordPackAddrUInt48UInt48_1 &Int #lookup(M, KX))) /Int pow208)) => doneLemma(maxUInt48 &Int (#lookup(M, KX) /Int pow208)) ... </k>
      requires #rangeAddress(CALLER_ID)

    // Memory operations

    claim <k> runLemma(#range(M:Memory [ 0 := #buf(4, X) ] [ 0 <- 10 ] [ 1 <- 11 ] [ 2 <- 12 ] [ 3 <- 13 ], 0, 4)) => doneLemma(10 : 11 : 12 : 13 : .ByteArray) ... </k>

    claim <k> runLemma( M:Memory [ 132 := #buf(32, B11) ] [ 128 := (#buf(32, B21) ++ #buf(32, B22)) ] ) => doneLemma( M [ 128 := (#buf(32, B21) ++ #buf(32, B22)) ] ) ... </k>
      requires #rangeUInt(256, B11) andBool #rangeUInt(256, B21) andBool #rangeUInt(256, B22)

    claim <k> runLemma( M:Memory [ 128 := (#buf(32, B31) ++ #buf(32, B32)) ] [ 128 := #buf(32, B41) ] ) => doneLemma( M [ 128 := #buf(32, B41) ] [ 160 := #buf(32, B32) ] ) ... </k>
      requires #rangeUInt(256, B31) andBool #rangeUInt(256, B32) andBool #rangeUInt(256, B41)

    claim <k> runLemma(M:Memory [ 128 := (217 : 99 : 141 : 54 : .ByteArray) ]
                                [ 132 := #buf(32, B11) ]
                                [ 128 := (#buf(32, B21) ++ #buf(32, B22) ++ #buf(32, B23) ++ #buf(32, B24) ++ #buf(32, B25)) ]
                                [ 128 := (217 : 99 : 141 : 54 : .ByteArray) ]
                                [ 132 := #buf(32, B11) ]
                                [ 128 := (#buf(32, B31) ++ #buf(32, B32)) ]
                                [ 128 := #buf(32, B41) ]
                      )
           => doneLemma(M [ 128 := #buf(32, B41) ]
                          [ 160 := #buf(32, B32) ]
                          [ 192 := (#buf(32, B23) ++ #buf(32, B24) ++ #buf(32, B25)) ]
                       )
          ...
          </k>
     requires #rangeUInt(256, B11)
      andBool #rangeUInt(256, B21) andBool #rangeUInt(256, B22) andBool #rangeUInt(256, B23) andBool #rangeUInt(256, B24) andBool #rangeUInt(256, B25)
      andBool #rangeUInt(256, B31) andBool #rangeUInt(256, B32)
      andBool #rangeUInt(256, B41)

endmodule
