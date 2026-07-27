requires "verification.k"

module BITWISE-MASK-SHIFT-SPEC
    imports VERIFICATION

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
