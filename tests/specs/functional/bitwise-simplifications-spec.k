requires "verification.k"

module BITWISE-SIMPLIFICATIONS-SPEC
    imports VERIFICATION

 // Address masking
 // ---------------

    claim [address-reprojection]: <k> runLemma(((maxUInt160 &Int ((368263281805664599098893944405654396525700029268 |Int (notMaxUInt160 &Int X:Int)) modInt pow256)) modInt pow160))
                                   => doneLemma(368263281805664599098893944405654396525700029268) ... </k>
                                requires #rangeUInt(256, X)

    claim [address-reprojection-1]: <k> runLemma(0 <=Int (368263281805664599098893944405654396525700029268 |Int (notMaxUInt160 &Int X:Int)))
                                     => doneLemma(true) ... </k>
                                  requires #rangeUInt(256, X)

    claim [address-reprojection-2]: <k> runLemma(0 <=Int (notMaxUInt160 &Int X:Int))
                                     => doneLemma(true) ... </k>
                                  requires #rangeUInt(256, X)

    claim [address-reprojection-4]: <k> runLemma((368263281805664599098893944405654396525700029268 |Int (notMaxUInt160 &Int X:Int)) <Int pow256)
                                     => doneLemma(true) ... </k>
                                  requires #rangeUInt(256, X)

    claim [address-reprojection-5]: <k> runLemma((notMaxUInt160 &Int X:Int) <Int pow256)
                                     => doneLemma(true) ... </k>
                                  requires #rangeUInt(256, X)

    claim [address-reprojection-6]: <k> runLemma(maxUInt160 &Int (368263281805664599098893944405654396525700029268 |Int (notMaxUInt160 &Int X:Int)))
                                     => doneLemma(368263281805664599098893944405654396525700029268) ... </k>
                                  requires #rangeUInt(256, X)

    claim [address-insertion-1]: <k> runLemma(368263281805664599098893944405654396525700029268 |Int (notMaxUInt160 &Int #lookup(ACCT_STORAGE:Map, 8)))
                                  => doneLemma(368263281805664599098893944405654396525700029268) ... </k>
                               requires #lookup(ACCT_STORAGE, 8) <Int pow160

 // bitwise-and identity
 // --------------------

    claim <k> runLemma ( N &Int maxUInt256 ) => doneLemma ( N ) ... </k> requires #rangeUInt(256, N)
    claim <k> runLemma ( maxUInt256 &Int N ) => doneLemma ( N ) ... </k> requires #rangeUInt(256, N)
    claim <k> runLemma ( N &Int maxUInt248 ) => doneLemma ( N ) ... </k> requires #rangeUInt(248, N)
    claim <k> runLemma ( maxUInt248 &Int N ) => doneLemma ( N ) ... </k> requires #rangeUInt(248, N)
    claim <k> runLemma ( N &Int maxUInt240 ) => doneLemma ( N ) ... </k> requires #rangeUInt(240, N)
    claim <k> runLemma ( maxUInt240 &Int N ) => doneLemma ( N ) ... </k> requires #rangeUInt(240, N)
    claim <k> runLemma ( N &Int maxUInt232 ) => doneLemma ( N ) ... </k> requires #rangeUInt(232, N)
    claim <k> runLemma ( maxUInt232 &Int N ) => doneLemma ( N ) ... </k> requires #rangeUInt(232, N)
    claim <k> runLemma ( N &Int maxUInt224 ) => doneLemma ( N ) ... </k> requires #rangeUInt(224, N)
    claim <k> runLemma ( maxUInt224 &Int N ) => doneLemma ( N ) ... </k> requires #rangeUInt(224, N)
    claim <k> runLemma ( N &Int maxUInt216 ) => doneLemma ( N ) ... </k> requires #rangeUInt(216, N)
    claim <k> runLemma ( maxUInt216 &Int N ) => doneLemma ( N ) ... </k> requires #rangeUInt(216, N)
    claim <k> runLemma ( N &Int maxUInt208 ) => doneLemma ( N ) ... </k> requires #rangeUInt(208, N)
    claim <k> runLemma ( maxUInt208 &Int N ) => doneLemma ( N ) ... </k> requires #rangeUInt(208, N)
    claim <k> runLemma ( N &Int maxUInt200 ) => doneLemma ( N ) ... </k> requires #rangeUInt(200, N)
    claim <k> runLemma ( maxUInt200 &Int N ) => doneLemma ( N ) ... </k> requires #rangeUInt(200, N)
    claim <k> runLemma ( N &Int maxUInt192 ) => doneLemma ( N ) ... </k> requires #rangeUInt(192, N)
    claim <k> runLemma ( maxUInt192 &Int N ) => doneLemma ( N ) ... </k> requires #rangeUInt(192, N)
    claim <k> runLemma ( N &Int maxUInt184 ) => doneLemma ( N ) ... </k> requires #rangeUInt(184, N)
    claim <k> runLemma ( maxUInt184 &Int N ) => doneLemma ( N ) ... </k> requires #rangeUInt(184, N)
    claim <k> runLemma ( N &Int maxUInt176 ) => doneLemma ( N ) ... </k> requires #rangeUInt(176, N)
    claim <k> runLemma ( maxUInt176 &Int N ) => doneLemma ( N ) ... </k> requires #rangeUInt(176, N)
    claim <k> runLemma ( N &Int maxUInt168 ) => doneLemma ( N ) ... </k> requires #rangeUInt(168, N)
    claim <k> runLemma ( maxUInt168 &Int N ) => doneLemma ( N ) ... </k> requires #rangeUInt(168, N)
    claim <k> runLemma ( N &Int maxUInt160 ) => doneLemma ( N ) ... </k> requires #rangeUInt(160, N)
    claim <k> runLemma ( maxUInt160 &Int N ) => doneLemma ( N ) ... </k> requires #rangeUInt(160, N)
    claim <k> runLemma ( N &Int maxUInt152 ) => doneLemma ( N ) ... </k> requires #rangeUInt(152, N)
    claim <k> runLemma ( maxUInt152 &Int N ) => doneLemma ( N ) ... </k> requires #rangeUInt(152, N)
    claim <k> runLemma ( N &Int maxUInt144 ) => doneLemma ( N ) ... </k> requires #rangeUInt(144, N)
    claim <k> runLemma ( maxUInt144 &Int N ) => doneLemma ( N ) ... </k> requires #rangeUInt(144, N)
    claim <k> runLemma ( N &Int maxUInt136 ) => doneLemma ( N ) ... </k> requires #rangeUInt(136, N)
    claim <k> runLemma ( maxUInt136 &Int N ) => doneLemma ( N ) ... </k> requires #rangeUInt(136, N)
    claim <k> runLemma ( N &Int maxUInt128 ) => doneLemma ( N ) ... </k> requires #rangeUInt(128, N)
    claim <k> runLemma ( maxUInt128 &Int N ) => doneLemma ( N ) ... </k> requires #rangeUInt(128, N)
    claim <k> runLemma ( N &Int maxUInt120 ) => doneLemma ( N ) ... </k> requires #rangeUInt(120, N)
    claim <k> runLemma ( maxUInt120 &Int N ) => doneLemma ( N ) ... </k> requires #rangeUInt(120, N)
    claim <k> runLemma ( N &Int maxUInt112 ) => doneLemma ( N ) ... </k> requires #rangeUInt(112, N)
    claim <k> runLemma ( maxUInt112 &Int N ) => doneLemma ( N ) ... </k> requires #rangeUInt(112, N)
    claim <k> runLemma ( N &Int maxUInt104 ) => doneLemma ( N ) ... </k> requires #rangeUInt(104, N)
    claim <k> runLemma ( maxUInt104 &Int N ) => doneLemma ( N ) ... </k> requires #rangeUInt(104, N)
    claim <k> runLemma ( N &Int maxUInt96  ) => doneLemma ( N ) ... </k> requires #rangeUInt(96,  N)
    claim <k> runLemma ( maxUInt96 &Int N  ) => doneLemma ( N ) ... </k> requires #rangeUInt(96,  N)
    claim <k> runLemma ( N &Int maxUInt88  ) => doneLemma ( N ) ... </k> requires #rangeUInt(88,  N)
    claim <k> runLemma ( maxUInt88 &Int N  ) => doneLemma ( N ) ... </k> requires #rangeUInt(88,  N)
    claim <k> runLemma ( N &Int maxUInt80  ) => doneLemma ( N ) ... </k> requires #rangeUInt(80,  N)
    claim <k> runLemma ( maxUInt80 &Int N  ) => doneLemma ( N ) ... </k> requires #rangeUInt(80,  N)
    claim <k> runLemma ( N &Int maxUInt72  ) => doneLemma ( N ) ... </k> requires #rangeUInt(72,  N)
    claim <k> runLemma ( maxUInt72 &Int N  ) => doneLemma ( N ) ... </k> requires #rangeUInt(72,  N)
    claim <k> runLemma ( N &Int maxUInt64  ) => doneLemma ( N ) ... </k> requires #rangeUInt(64,  N)
    claim <k> runLemma ( maxUInt64 &Int N  ) => doneLemma ( N ) ... </k> requires #rangeUInt(64,  N)
    claim <k> runLemma ( N &Int maxUInt56  ) => doneLemma ( N ) ... </k> requires #rangeUInt(56,  N)
    claim <k> runLemma ( maxUInt56 &Int N  ) => doneLemma ( N ) ... </k> requires #rangeUInt(56,  N)
    claim <k> runLemma ( N &Int maxUInt48  ) => doneLemma ( N ) ... </k> requires #rangeUInt(48,  N)
    claim <k> runLemma ( maxUInt48 &Int N  ) => doneLemma ( N ) ... </k> requires #rangeUInt(48,  N)
    claim <k> runLemma ( N &Int maxUInt40  ) => doneLemma ( N ) ... </k> requires #rangeUInt(40,  N)
    claim <k> runLemma ( maxUInt40 &Int N  ) => doneLemma ( N ) ... </k> requires #rangeUInt(40,  N)
    claim <k> runLemma ( N &Int maxUInt32  ) => doneLemma ( N ) ... </k> requires #rangeUInt(32,  N)
    claim <k> runLemma ( maxUInt32 &Int N  ) => doneLemma ( N ) ... </k> requires #rangeUInt(32,  N)
    claim <k> runLemma ( N &Int maxUInt24  ) => doneLemma ( N ) ... </k> requires #rangeUInt(24,  N)
    claim <k> runLemma ( maxUInt24 &Int N  ) => doneLemma ( N ) ... </k> requires #rangeUInt(24,  N)
    claim <k> runLemma ( N &Int maxUInt16  ) => doneLemma ( N ) ... </k> requires #rangeUInt(16,  N)
    claim <k> runLemma ( maxUInt16 &Int N  ) => doneLemma ( N ) ... </k> requires #rangeUInt(16,  N)
    claim <k> runLemma ( N &Int maxUInt8   ) => doneLemma ( N ) ... </k> requires #rangeUInt(8,   N)
    claim <k> runLemma ( maxUInt8 &Int N   ) => doneLemma ( N ) ... </k> requires #rangeUInt(8,   N)

endmodule
