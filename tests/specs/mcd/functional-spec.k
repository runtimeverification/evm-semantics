requires "verification.k"

module FUNCTIONAL-SPEC-SYNTAX
    imports VERIFICATION

    syntax KItem ::= runLemma ( Step ) | doneLemma ( Step )
 // -------------------------------------------------------
    rule <k> runLemma(S) => doneLemma(S) ... </k>

    syntax Step ::= Bool | Int
 // --------------------------

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

endmodule
