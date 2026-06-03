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

 // bitwise
 // -------

    claim [bit-n008-0]: <k> runLemma ( notMaxUInt8   &Int X ) => doneLemma( 0 ) ... </k> requires #rangeUInt (   8 , X )
    claim [bit-n016-0]: <k> runLemma ( notMaxUInt16  &Int X ) => doneLemma( 0 ) ... </k> requires #rangeUInt (  16 , X )
    claim [bit-n032-0]: <k> runLemma ( notMaxUInt32  &Int X ) => doneLemma( 0 ) ... </k> requires #rangeUInt (  32 , X )
    claim [bit-n064-0]: <k> runLemma ( notMaxUInt64  &Int X ) => doneLemma( 0 ) ... </k> requires #rangeUInt (  64 , X )
    claim [bit-n096-0]: <k> runLemma ( notMaxUInt96  &Int X ) => doneLemma( 0 ) ... </k> requires #rangeUInt (  96 , X )
    claim [bit-n128-0]: <k> runLemma ( notMaxUInt128 &Int X ) => doneLemma( 0 ) ... </k> requires #rangeUInt ( 128 , X )
    claim [bit-n160-0]: <k> runLemma ( notMaxUInt160 &Int X ) => doneLemma( 0 ) ... </k> requires #rangeUInt ( 160 , X )
    claim [bit-n192-0]: <k> runLemma ( notMaxUInt192 &Int X ) => doneLemma( 0 ) ... </k> requires #rangeUInt ( 192 , X )
    claim [bit-n208-0]: <k> runLemma ( notMaxUInt208 &Int X ) => doneLemma( 0 ) ... </k> requires #rangeUInt ( 208 , X )
    claim [bit-n224-0]: <k> runLemma ( notMaxUInt224 &Int X ) => doneLemma( 0 ) ... </k> requires #rangeUInt ( 224 , X )
    claim [bit-n240-0]: <k> runLemma ( notMaxUInt240 &Int X ) => doneLemma( 0 ) ... </k> requires #rangeUInt ( 240 , X )
    claim [bit-n248-0]: <k> runLemma ( notMaxUInt248 &Int X ) => doneLemma( 0 ) ... </k> requires #rangeUInt ( 248 , X )

    claim [bit-n008-shl]: <k> runLemma ( notMaxUInt8   &Int ( X <<Int   8 ) ) => doneLemma( X <<Int   8 ) ... </k> requires #rangeUInt ( 248 , X )
    claim [bit-n016-shl]: <k> runLemma ( notMaxUInt16  &Int ( X <<Int  16 ) ) => doneLemma( X <<Int  16 ) ... </k> requires #rangeUInt ( 240 , X )
    claim [bit-n032-shl]: <k> runLemma ( notMaxUInt32  &Int ( X <<Int  32 ) ) => doneLemma( X <<Int  32 ) ... </k> requires #rangeUInt ( 224 , X )
    claim [bit-n064-shl]: <k> runLemma ( notMaxUInt64  &Int ( X <<Int  64 ) ) => doneLemma( X <<Int  64 ) ... </k> requires #rangeUInt ( 192 , X )
    claim [bit-n096-shl]: <k> runLemma ( notMaxUInt96  &Int ( X <<Int  96 ) ) => doneLemma( X <<Int  96 ) ... </k> requires #rangeUInt ( 160 , X )
    claim [bit-n128-shl]: <k> runLemma ( notMaxUInt128 &Int ( X <<Int 128 ) ) => doneLemma( X <<Int 128 ) ... </k> requires #rangeUInt ( 128 , X )
    claim [bit-n160-shl]: <k> runLemma ( notMaxUInt160 &Int ( X <<Int 160 ) ) => doneLemma( X <<Int 160 ) ... </k> requires #rangeUInt (  96 , X )
    claim [bit-n192-shl]: <k> runLemma ( notMaxUInt192 &Int ( X <<Int 192 ) ) => doneLemma( X <<Int 192 ) ... </k> requires #rangeUInt (  64 , X )
    claim [bit-n208-shl]: <k> runLemma ( notMaxUInt208 &Int ( X <<Int 208 ) ) => doneLemma( X <<Int 208 ) ... </k> requires #rangeUInt (  48 , X )
    claim [bit-n224-shl]: <k> runLemma ( notMaxUInt224 &Int ( X <<Int 224 ) ) => doneLemma( X <<Int 224 ) ... </k> requires #rangeUInt (  32 , X )
    claim [bit-n240-shl]: <k> runLemma ( notMaxUInt240 &Int ( X <<Int 240 ) ) => doneLemma( X <<Int 240 ) ... </k> requires #rangeUInt (  16 , X )
    claim [bit-n248-shl]: <k> runLemma ( notMaxUInt248 &Int ( X <<Int 248 ) ) => doneLemma( X <<Int 248 ) ... </k> requires #rangeUInt (   8 , X )

    claim [bit-008-m-or-nm]: <k> runLemma ( maxUInt8   &Int ( X |Int ( notMaxUInt8   &Int T ) ) ) => doneLemma( X ) ... </k> requires #rangeUInt (   8 , X ) andBool #rangeUInt(256, T)
    claim [bit-016-m-or-nm]: <k> runLemma ( maxUInt16  &Int ( X |Int ( notMaxUInt16  &Int T ) ) ) => doneLemma( X ) ... </k> requires #rangeUInt (  16 , X ) andBool #rangeUInt(256, T)
    claim [bit-032-m-or-nm]: <k> runLemma ( maxUInt32  &Int ( X |Int ( notMaxUInt32  &Int T ) ) ) => doneLemma( X ) ... </k> requires #rangeUInt (  32 , X ) andBool #rangeUInt(256, T)
    claim [bit-064-m-or-nm]: <k> runLemma ( maxUInt64  &Int ( X |Int ( notMaxUInt64  &Int T ) ) ) => doneLemma( X ) ... </k> requires #rangeUInt (  64 , X ) andBool #rangeUInt(256, T)
    claim [bit-096-m-or-nm]: <k> runLemma ( maxUInt96  &Int ( X |Int ( notMaxUInt96  &Int T ) ) ) => doneLemma( X ) ... </k> requires #rangeUInt (  96 , X ) andBool #rangeUInt(256, T)
    claim [bit-128-m-or-nm]: <k> runLemma ( maxUInt128 &Int ( X |Int ( notMaxUInt128 &Int T ) ) ) => doneLemma( X ) ... </k> requires #rangeUInt ( 128 , X ) andBool #rangeUInt(256, T)
    claim [bit-160-m-or-nm]: <k> runLemma ( maxUInt160 &Int ( X |Int ( notMaxUInt160 &Int T ) ) ) => doneLemma( X ) ... </k> requires #rangeUInt ( 160 , X ) andBool #rangeUInt(256, T)
    claim [bit-192-m-or-nm]: <k> runLemma ( maxUInt192 &Int ( X |Int ( notMaxUInt192 &Int T ) ) ) => doneLemma( X ) ... </k> requires #rangeUInt ( 192 , X ) andBool #rangeUInt(256, T)
    claim [bit-208-m-or-nm]: <k> runLemma ( maxUInt208 &Int ( X |Int ( notMaxUInt208 &Int T ) ) ) => doneLemma( X ) ... </k> requires #rangeUInt ( 208 , X ) andBool #rangeUInt(256, T)
    claim [bit-224-m-or-nm]: <k> runLemma ( maxUInt224 &Int ( X |Int ( notMaxUInt224 &Int T ) ) ) => doneLemma( X ) ... </k> requires #rangeUInt ( 224 , X ) andBool #rangeUInt(256, T)
    claim [bit-240-m-or-nm]: <k> runLemma ( maxUInt240 &Int ( X |Int ( notMaxUInt240 &Int T ) ) ) => doneLemma( X ) ... </k> requires #rangeUInt ( 240 , X ) andBool #rangeUInt(256, T)
    claim [bit-248-m-or-nm]: <k> runLemma ( maxUInt248 &Int ( X |Int ( notMaxUInt248 &Int T ) ) ) => doneLemma( X ) ... </k> requires #rangeUInt ( 248 , X ) andBool #rangeUInt(256, T)

    claim [bit-008-nm-or-m]: <k> runLemma ( notMaxUInt8   &Int ( X |Int ( maxUInt8   &Int T ) ) ) => doneLemma( 0 ) ... </k> requires #rangeUInt (   8 , X ) andBool #rangeUInt(256, T)
    claim [bit-016-nm-or-m]: <k> runLemma ( notMaxUInt16  &Int ( X |Int ( maxUInt16  &Int T ) ) ) => doneLemma( 0 ) ... </k> requires #rangeUInt (  16 , X ) andBool #rangeUInt(256, T)
    claim [bit-032-nm-or-m]: <k> runLemma ( notMaxUInt32  &Int ( X |Int ( maxUInt32  &Int T ) ) ) => doneLemma( 0 ) ... </k> requires #rangeUInt (  32 , X ) andBool #rangeUInt(256, T)
    claim [bit-064-nm-or-m]: <k> runLemma ( notMaxUInt64  &Int ( X |Int ( maxUInt64  &Int T ) ) ) => doneLemma( 0 ) ... </k> requires #rangeUInt (  64 , X ) andBool #rangeUInt(256, T)
    claim [bit-096-nm-or-m]: <k> runLemma ( notMaxUInt96  &Int ( X |Int ( maxUInt96  &Int T ) ) ) => doneLemma( 0 ) ... </k> requires #rangeUInt (  96 , X ) andBool #rangeUInt(256, T)
    claim [bit-128-nm-or-m]: <k> runLemma ( notMaxUInt128 &Int ( X |Int ( maxUInt128 &Int T ) ) ) => doneLemma( 0 ) ... </k> requires #rangeUInt ( 128 , X ) andBool #rangeUInt(256, T)
    claim [bit-160-nm-or-m]: <k> runLemma ( notMaxUInt160 &Int ( X |Int ( maxUInt160 &Int T ) ) ) => doneLemma( 0 ) ... </k> requires #rangeUInt ( 160 , X ) andBool #rangeUInt(256, T)
    claim [bit-192-nm-or-m]: <k> runLemma ( notMaxUInt192 &Int ( X |Int ( maxUInt192 &Int T ) ) ) => doneLemma( 0 ) ... </k> requires #rangeUInt ( 192 , X ) andBool #rangeUInt(256, T)
    claim [bit-208-nm-or-m]: <k> runLemma ( notMaxUInt208 &Int ( X |Int ( maxUInt208 &Int T ) ) ) => doneLemma( 0 ) ... </k> requires #rangeUInt ( 208 , X ) andBool #rangeUInt(256, T)
    claim [bit-224-nm-or-m]: <k> runLemma ( notMaxUInt224 &Int ( X |Int ( maxUInt224 &Int T ) ) ) => doneLemma( 0 ) ... </k> requires #rangeUInt ( 224 , X ) andBool #rangeUInt(256, T)
    claim [bit-240-nm-or-m]: <k> runLemma ( notMaxUInt240 &Int ( X |Int ( maxUInt240 &Int T ) ) ) => doneLemma( 0 ) ... </k> requires #rangeUInt ( 240 , X ) andBool #rangeUInt(256, T)
    claim [bit-248-nm-or-m]: <k> runLemma ( notMaxUInt248 &Int ( X |Int ( maxUInt248 &Int T ) ) ) => doneLemma( 0 ) ... </k> requires #rangeUInt ( 248 , X ) andBool #rangeUInt(256, T)

    claim [bit-008-m-aW]: <k> runLemma ( maxUInt8   &Int #asWord ( BA ) ) => doneLemma ( #asWord ( #range(BA, 31,  1) ) ) ... </k> requires lengthBytes(BA) ==Int 32
    claim [bit-016-m-aW]: <k> runLemma ( maxUInt16  &Int #asWord ( BA ) ) => doneLemma ( #asWord ( #range(BA, 30,  2) ) ) ... </k> requires lengthBytes(BA) ==Int 32
    claim [bit-024-m-aW]: <k> runLemma ( maxUInt24  &Int #asWord ( BA ) ) => doneLemma ( #asWord ( #range(BA, 29,  3) ) ) ... </k> requires lengthBytes(BA) ==Int 32
    claim [bit-032-m-aW]: <k> runLemma ( maxUInt32  &Int #asWord ( BA ) ) => doneLemma ( #asWord ( #range(BA, 28,  4) ) ) ... </k> requires lengthBytes(BA) ==Int 32
    claim [bit-040-m-aW]: <k> runLemma ( maxUInt40  &Int #asWord ( BA ) ) => doneLemma ( #asWord ( #range(BA, 27,  5) ) ) ... </k> requires lengthBytes(BA) ==Int 32
    claim [bit-048-m-aW]: <k> runLemma ( maxUInt48  &Int #asWord ( BA ) ) => doneLemma ( #asWord ( #range(BA, 26,  6) ) ) ... </k> requires lengthBytes(BA) ==Int 32
    claim [bit-056-m-aW]: <k> runLemma ( maxUInt56  &Int #asWord ( BA ) ) => doneLemma ( #asWord ( #range(BA, 25,  7) ) ) ... </k> requires lengthBytes(BA) ==Int 32
    claim [bit-064-m-aW]: <k> runLemma ( maxUInt64  &Int #asWord ( BA ) ) => doneLemma ( #asWord ( #range(BA, 24,  8) ) ) ... </k> requires lengthBytes(BA) ==Int 32
    claim [bit-072-m-aW]: <k> runLemma ( maxUInt72  &Int #asWord ( BA ) ) => doneLemma ( #asWord ( #range(BA, 23,  9) ) ) ... </k> requires lengthBytes(BA) ==Int 32
    claim [bit-080-m-aW]: <k> runLemma ( maxUInt80  &Int #asWord ( BA ) ) => doneLemma ( #asWord ( #range(BA, 22, 10) ) ) ... </k> requires lengthBytes(BA) ==Int 32
    claim [bit-088-m-aW]: <k> runLemma ( maxUInt88  &Int #asWord ( BA ) ) => doneLemma ( #asWord ( #range(BA, 21, 11) ) ) ... </k> requires lengthBytes(BA) ==Int 32
    claim [bit-096-m-aW]: <k> runLemma ( maxUInt96  &Int #asWord ( BA ) ) => doneLemma ( #asWord ( #range(BA, 20, 12) ) ) ... </k> requires lengthBytes(BA) ==Int 32
    claim [bit-104-m-aW]: <k> runLemma ( maxUInt104 &Int #asWord ( BA ) ) => doneLemma ( #asWord ( #range(BA, 19, 13) ) ) ... </k> requires lengthBytes(BA) ==Int 32
    claim [bit-112-m-aW]: <k> runLemma ( maxUInt112 &Int #asWord ( BA ) ) => doneLemma ( #asWord ( #range(BA, 18, 14) ) ) ... </k> requires lengthBytes(BA) ==Int 32
    claim [bit-120-m-aW]: <k> runLemma ( maxUInt120 &Int #asWord ( BA ) ) => doneLemma ( #asWord ( #range(BA, 17, 15) ) ) ... </k> requires lengthBytes(BA) ==Int 32
    claim [bit-128-m-aW]: <k> runLemma ( maxUInt128 &Int #asWord ( BA ) ) => doneLemma ( #asWord ( #range(BA, 16, 16) ) ) ... </k> requires lengthBytes(BA) ==Int 32
    claim [bit-136-m-aW]: <k> runLemma ( maxUInt136 &Int #asWord ( BA ) ) => doneLemma ( #asWord ( #range(BA, 15, 17) ) ) ... </k> requires lengthBytes(BA) ==Int 32
    claim [bit-144-m-aW]: <k> runLemma ( maxUInt144 &Int #asWord ( BA ) ) => doneLemma ( #asWord ( #range(BA, 14, 18) ) ) ... </k> requires lengthBytes(BA) ==Int 32
    claim [bit-152-m-aW]: <k> runLemma ( maxUInt152 &Int #asWord ( BA ) ) => doneLemma ( #asWord ( #range(BA, 13, 19) ) ) ... </k> requires lengthBytes(BA) ==Int 32
    claim [bit-160-m-aW]: <k> runLemma ( maxUInt160 &Int #asWord ( BA ) ) => doneLemma ( #asWord ( #range(BA, 12, 20) ) ) ... </k> requires lengthBytes(BA) ==Int 32
    claim [bit-168-m-aW]: <k> runLemma ( maxUInt168 &Int #asWord ( BA ) ) => doneLemma ( #asWord ( #range(BA, 11, 21) ) ) ... </k> requires lengthBytes(BA) ==Int 32
    claim [bit-176-m-aW]: <k> runLemma ( maxUInt176 &Int #asWord ( BA ) ) => doneLemma ( #asWord ( #range(BA, 10, 22) ) ) ... </k> requires lengthBytes(BA) ==Int 32
    claim [bit-184-m-aW]: <k> runLemma ( maxUInt184 &Int #asWord ( BA ) ) => doneLemma ( #asWord ( #range(BA,  9, 23) ) ) ... </k> requires lengthBytes(BA) ==Int 32
    claim [bit-192-m-aW]: <k> runLemma ( maxUInt192 &Int #asWord ( BA ) ) => doneLemma ( #asWord ( #range(BA,  8, 24) ) ) ... </k> requires lengthBytes(BA) ==Int 32
    claim [bit-200-m-aW]: <k> runLemma ( maxUInt200 &Int #asWord ( BA ) ) => doneLemma ( #asWord ( #range(BA,  7, 25) ) ) ... </k> requires lengthBytes(BA) ==Int 32
    claim [bit-208-m-aW]: <k> runLemma ( maxUInt208 &Int #asWord ( BA ) ) => doneLemma ( #asWord ( #range(BA,  6, 26) ) ) ... </k> requires lengthBytes(BA) ==Int 32
    claim [bit-216-m-aW]: <k> runLemma ( maxUInt216 &Int #asWord ( BA ) ) => doneLemma ( #asWord ( #range(BA,  5, 27) ) ) ... </k> requires lengthBytes(BA) ==Int 32
    claim [bit-224-m-aW]: <k> runLemma ( maxUInt224 &Int #asWord ( BA ) ) => doneLemma ( #asWord ( #range(BA,  4, 28) ) ) ... </k> requires lengthBytes(BA) ==Int 32
    claim [bit-232-m-aW]: <k> runLemma ( maxUInt232 &Int #asWord ( BA ) ) => doneLemma ( #asWord ( #range(BA,  3, 29) ) ) ... </k> requires lengthBytes(BA) ==Int 32
    claim [bit-240-m-aW]: <k> runLemma ( maxUInt240 &Int #asWord ( BA ) ) => doneLemma ( #asWord ( #range(BA,  2, 30) ) ) ... </k> requires lengthBytes(BA) ==Int 32
    claim [bit-248-m-aW]: <k> runLemma ( maxUInt248 &Int #asWord ( BA ) ) => doneLemma ( #asWord ( #range(BA,  1, 31) ) ) ... </k> requires lengthBytes(BA) ==Int 32
    claim [bit-256-m-aW]: <k> runLemma ( maxUInt256 &Int #asWord ( BA ) ) => doneLemma ( #asWord ( #range(BA,  0, 32) ) ) ... </k> requires lengthBytes(BA) ==Int 32

    claim [bit-008-nm-aW]: <k> runLemma ( notMaxUInt8   &Int #asWord ( BA ) ) => doneLemma ( #asWord ( #range(BA, 0, 31) +Bytes #buf (  1, 0 ) ) ) ... </k> requires lengthBytes(BA) ==Int 32
    claim [bit-016-nm-aW]: <k> runLemma ( notMaxUInt16  &Int #asWord ( BA ) ) => doneLemma ( #asWord ( #range(BA, 0, 30) +Bytes #buf (  2, 0 ) ) ) ... </k> requires lengthBytes(BA) ==Int 32
    claim [bit-032-nm-aW]: <k> runLemma ( notMaxUInt32  &Int #asWord ( BA ) ) => doneLemma ( #asWord ( #range(BA, 0, 28) +Bytes #buf (  4, 0 ) ) ) ... </k> requires lengthBytes(BA) ==Int 32
    claim [bit-064-nm-aW]: <k> runLemma ( notMaxUInt64  &Int #asWord ( BA ) ) => doneLemma ( #asWord ( #range(BA, 0, 24) +Bytes #buf (  8, 0 ) ) ) ... </k> requires lengthBytes(BA) ==Int 32
    claim [bit-096-nm-aW]: <k> runLemma ( notMaxUInt96  &Int #asWord ( BA ) ) => doneLemma ( #asWord ( #range(BA, 0, 20) +Bytes #buf ( 12, 0 ) ) ) ... </k> requires lengthBytes(BA) ==Int 32
    claim [bit-128-nm-aW]: <k> runLemma ( notMaxUInt128 &Int #asWord ( BA ) ) => doneLemma ( #asWord ( #range(BA, 0, 16) +Bytes #buf ( 16, 0 ) ) ) ... </k> requires lengthBytes(BA) ==Int 32
    claim [bit-160-nm-aW]: <k> runLemma ( notMaxUInt160 &Int #asWord ( BA ) ) => doneLemma ( #asWord ( #range(BA, 0, 12) +Bytes #buf ( 20, 0 ) ) ) ... </k> requires lengthBytes(BA) ==Int 32
    claim [bit-192-nm-aW]: <k> runLemma ( notMaxUInt192 &Int #asWord ( BA ) ) => doneLemma ( #asWord ( #range(BA, 0, 8)  +Bytes #buf ( 24, 0 ) ) ) ... </k> requires lengthBytes(BA) ==Int 32
    claim [bit-208-nm-aW]: <k> runLemma ( notMaxUInt208 &Int #asWord ( BA ) ) => doneLemma ( #asWord ( #range(BA, 0, 6)  +Bytes #buf ( 26, 0 ) ) ) ... </k> requires lengthBytes(BA) ==Int 32
    claim [bit-224-nm-aW]: <k> runLemma ( notMaxUInt224 &Int #asWord ( BA ) ) => doneLemma ( #asWord ( #range(BA, 0, 4)  +Bytes #buf ( 28, 0 ) ) ) ... </k> requires lengthBytes(BA) ==Int 32
    claim [bit-240-nm-aW]: <k> runLemma ( notMaxUInt240 &Int #asWord ( BA ) ) => doneLemma ( #asWord ( #range(BA, 0, 2)  +Bytes #buf ( 30, 0 ) ) ) ... </k> requires lengthBytes(BA) ==Int 32
    claim [bit-248-nm-aW]: <k> runLemma ( notMaxUInt248 &Int #asWord ( BA ) ) => doneLemma ( #asWord ( #range(BA, 0, 1)  +Bytes #buf ( 31, 0 ) ) ) ... </k> requires lengthBytes(BA) ==Int 32

    claim <k> runLemma ( #buf ( 32 , #asWord ( X ) ) ) => doneLemma( X ) </k> requires lengthBytes(X) ==Int 32
    claim <k> runLemma ( #buf ( 32 , X <<Int 248 ) ) => doneLemma( #buf ( 1 , X ) +Bytes #buf ( 31 , 0 ) ) ... </k> requires #rangeUInt (  8 , X )
    claim <k> runLemma ( #buf ( 32 , X <<Int 240 ) ) => doneLemma( #buf ( 2 , X ) +Bytes #buf ( 30 , 0 ) ) ... </k> requires #rangeUInt ( 16 , X )

    claim [band-maxUInt-lt-01]: <k> runLemma ( maxUInt8   &Int X <Int    256 ) => doneLemma ( true ) ... </k> requires 0 <=Int X
    claim [band-maxUInt-lt-02]: <k> runLemma ( maxUInt48  &Int X <Int  pow48 ) => doneLemma ( true ) ... </k> requires 0 <=Int X
    claim [band-maxUInt-lt-03]: <k> runLemma ( maxUInt160 &Int X <Int pow160 ) => doneLemma ( true ) ... </k> requires 0 <=Int X

 // shift
 // -----

    claim [shift-16] : <k> runLemma ( ( X <<Int  16 ) <Int pow256 ) => doneLemma ( true ) ... </k> requires #rangeUInt ( 240 , X )
    claim [shift-240]: <k> runLemma ( ( X <<Int 240 ) <Int pow256 ) => doneLemma ( true ) ... </k> requires #rangeUInt (  16 , X )
    claim [shift-248]: <k> runLemma ( ( X <<Int 248 ) <Int pow256 ) => doneLemma ( true ) ... </k> requires #rangeUInt (   8 , X )

    claim [shift-range]: <k> runLemma ( #rangeUInt ( 256 , X <<Int 16 ) ) => doneLemma ( true ) ... </k> requires #rangeUInt ( 16 , X )
    claim [shift-mod]: <k> runLemma ( ( X <<Int 16 ) modInt pow256 ) => doneLemma ( X <<Int 16 ) ... </k> requires #rangeUInt ( 16 , X )

 // xor
 // -----

    claim [xorInt-range]: <k> runLemma ( #rangeUInt ( 256 , X xorInt Y ) ) => doneLemma ( true ) ... </k> requires #rangeUInt ( 256 , X ) andBool #rangeUInt ( 256 , Y )
    claim [xorInt-to-if]: <k> runLemma ( A xorInt ( bool2Word ( A <=Int B ) *Int ( A xorInt B )  ) ) => doneLemma ( #if ( A <=Int B ) #then B #else A #fi ) ... </k>

endmodule
