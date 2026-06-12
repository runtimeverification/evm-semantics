requires "verification.k"

module BITWISE-ASWORD-SPEC
    imports VERIFICATION

 // bitwise &Int #asWord
 // ---------------------

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

endmodule
