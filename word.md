Core definitions for `Word`
===========================

In this file are defined the basic components for EVM words.

```k
module WORD
    imports INT
    imports BOOL
```

```{.k .bytes}
    imports BYTES
```

Important Powers
----------------

Some important numbers that are referred to often during execution.
These can be used for pattern-matching on the LHS of rules as well (`alias` attribute expands all occurances of these in rules).

```k
    syntax Int ::= "pow256" [alias] /* 2 ^Int 256 */
                 | "pow255" [alias] /* 2 ^Int 255 */
                 | "pow248" [alias] /* 2 ^Int 248" */
                 | "pow240" [alias] /* 2 ^Int 240" */
                 | "pow232" [alias] /* 2 ^Int 232" */
                 | "pow224" [alias] /* 2 ^Int 224" */
                 | "pow216" [alias] /* 2 ^Int 216" */
                 | "pow208" [alias] /* 2 ^Int 208" */
                 | "pow200" [alias] /* 2 ^Int 200" */
                 | "pow192" [alias] /* 2 ^Int 192" */
                 | "pow184" [alias] /* 2 ^Int 184" */
                 | "pow176" [alias] /* 2 ^Int 176" */
                 | "pow168" [alias] /* 2 ^Int 168" */
                 | "pow160" [alias] /* 2 ^Int 160" */
                 | "pow152" [alias] /* 2 ^Int 152" */
                 | "pow144" [alias] /* 2 ^Int 144" */
                 | "pow136" [alias] /* 2 ^Int 136" */
                 | "pow128" [alias] /* 2 ^Int 128" */
                 | "pow120" [alias] /* 2 ^Int 120" */
                 | "pow112" [alias] /* 2 ^Int 112" */
                 | "pow104" [alias] /* 2 ^Int 104" */
                 | "pow96"  [alias] /* 2 ^Int 96"  */
                 | "pow88"  [alias] /* 2 ^Int 88"  */
                 | "pow80"  [alias] /* 2 ^Int 80"  */
                 | "pow72"  [alias] /* 2 ^Int 72"  */
                 | "pow64"  [alias] /* 2 ^Int 64"  */
                 | "pow56"  [alias] /* 2 ^Int 56"  */
                 | "pow48"  [alias] /* 2 ^Int 48"  */
                 | "pow40"  [alias] /* 2 ^Int 40"  */
                 | "pow32"  [alias] /* 2 ^Int 32"  */
                 | "pow24"  [alias] /* 2 ^Int 24"  */
                 | "pow16"  [alias] /* 2 ^Int 16"  */
                 | "pow8"   [alias] /* 2 ^Int 8"   */
 // ------------------------------------------------
    rule pow256 => 115792089237316195423570985008687907853269984665640564039457584007913129639936
    rule pow255 => 57896044618658097711785492504343953926634992332820282019728792003956564819968
    rule pow248 => 452312848583266388373324160190187140051835877600158453279131187530910662656
    rule pow240 => 1766847064778384329583297500742918515827483896875618958121606201292619776
    rule pow232 => 6901746346790563787434755862277025452451108972170386555162524223799296
    rule pow224 => 26959946667150639794667015087019630673637144422540572481103610249216
    rule pow216 => 105312291668557186697918027683670432318895095400549111254310977536
    rule pow208 => 411376139330301510538742295639337626245683966408394965837152256
    rule pow200 => 1606938044258990275541962092341162602522202993782792835301376
    rule pow192 => 6277101735386680763835789423207666416102355444464034512896
    rule pow184 => 24519928653854221733733552434404946937899825954937634816
    rule pow176 => 95780971304118053647396689196894323976171195136475136
    rule pow168 => 374144419156711147060143317175368453031918731001856
    rule pow160 => 1461501637330902918203684832716283019655932542976
    rule pow152 => 5708990770823839524233143877797980545530986496
    rule pow144 => 22300745198530623141535718272648361505980416
    rule pow136 => 87112285931760246646623899502532662132736
    rule pow128 => 340282366920938463463374607431768211456
    rule pow120 => 1329227995784915872903807060280344576
    rule pow112 => 5192296858534827628530496329220096
    rule pow104 => 20282409603651670423947251286016
    rule pow96  => 79228162514264337593543950336
    rule pow88  => 309485009821345068724781056
    rule pow80  => 1208925819614629174706176
    rule pow72  => 4722366482869645213696
    rule pow64  => 18446744073709551616
    rule pow56  => 72057594037927936
    rule pow48  => 281474976710656
    rule pow40  => 1099511627776
    rule pow32  => 4294967296
    rule pow24  => 16777216
    rule pow16  => 65536
    rule pow8   => 256
```

Maximums and minimums
---------------------

The maximum and minimum values of each type are defined below.

```k
    syntax Int ::= "minSInt128"      [alias]
                 | "maxSInt128"      [alias]
                 | "minSInt256"      [alias]
                 | "maxSInt256"      [alias]
                 | "minUInt8"        [macro]
                 | "maxUInt8"        [alias]
                 | "minUInt16"       [macro]
                 | "maxUInt16"       [alias]
                 | "minUInt24"       [macro]
                 | "maxUInt24"       [alias]
                 | "minUInt32"       [macro]
                 | "maxUInt32"       [alias]
                 | "minUInt40"       [macro]
                 | "maxUInt40"       [alias]
                 | "minUInt48"       [macro]
                 | "maxUInt48"       [alias]
                 | "minUInt56"       [macro]
                 | "maxUInt56"       [alias]
                 | "minUInt64"       [macro]
                 | "maxUInt64"       [alias]
                 | "minUInt72"       [macro]
                 | "maxUInt72"       [alias]
                 | "minUInt80"       [macro]
                 | "maxUInt80"       [alias]
                 | "minUInt88"       [macro]
                 | "maxUInt88"       [alias]
                 | "minUInt96"       [macro]
                 | "maxUInt96"       [alias]
                 | "minUInt104"      [macro]
                 | "maxUInt104"      [alias]
                 | "minUInt112"      [macro]
                 | "maxUInt112"      [alias]
                 | "minUInt120"      [macro]
                 | "maxUInt120"      [alias]
                 | "minUInt128"      [macro]
                 | "maxUInt128"      [alias]
                 | "minUInt136"      [macro]
                 | "maxUInt136"      [alias]
                 | "minUInt144"      [macro]
                 | "maxUInt144"      [alias]
                 | "minUInt152"      [macro]
                 | "maxUInt152"      [alias]
                 | "minUInt160"      [macro]
                 | "maxUInt160"      [alias]
                 | "minUInt168"      [macro]
                 | "maxUInt168"      [alias]
                 | "minUInt176"      [macro]
                 | "maxUInt176"      [alias]
                 | "minUInt184"      [macro]
                 | "maxUInt184"      [alias]
                 | "minUInt192"      [macro]
                 | "maxUInt192"      [alias]
                 | "minUInt200"      [macro]
                 | "maxUInt200"      [alias]
                 | "minUInt208"      [macro]
                 | "maxUInt208"      [alias]
                 | "minUInt216"      [macro]
                 | "maxUInt216"      [alias]
                 | "minUInt224"      [macro]
                 | "maxUInt224"      [alias]
                 | "minUInt232"      [macro]
                 | "maxUInt232"      [alias]
                 | "minUInt240"      [macro]
                 | "maxUInt240"      [alias]
                 | "minUInt248"      [macro]
                 | "maxUInt248"      [alias]
                 | "minUInt256"      [macro]
                 | "maxUInt256"      [alias]
                 | "minSFixed128x10" [alias]
                 | "maxSFixed128x10" [alias]
                 | "minUFixed128x10" [macro]
                 | "maxUFixed128x10" [alias]
 // ----------------------------------------
    rule minSInt128      => -170141183460469231731687303715884105728                                        /*  -2^127      */
    rule maxSInt128      =>  170141183460469231731687303715884105727                                        /*   2^127 - 1  */
    rule minSFixed128x10 => -1701411834604692317316873037158841057280000000000                              /* (-2^127    ) * 10^10 */
    rule maxSFixed128x10 =>  1701411834604692317316873037158841057270000000000                              /* ( 2^127 - 1) * 10^10 */
    rule minSInt256      => -57896044618658097711785492504343953926634992332820282019728792003956564819968  /*  -2^255      */
    rule maxSInt256      =>  57896044618658097711785492504343953926634992332820282019728792003956564819967  /*   2^255 - 1  */

    rule minUInt8        =>  0
    rule maxUInt8        =>  255                                                                            /*   2^8 - 1  */
    rule minUInt16       =>  0
    rule maxUInt16       =>  65535                                                                          /*   2^16 - 1  */
    rule minUInt24       =>  0
    rule maxUInt24       =>  16777215                                                                       /*   2^24 - 1  */
    rule minUInt32       =>  0
    rule maxUInt32       =>  4294967295                                                                     /*   2^32 - 1  */
    rule minUInt40       =>  0
    rule maxUInt40       =>  1099511627775                                                                  /*   2^40 - 1  */
    rule minUInt48       =>  0
    rule maxUInt48       =>  281474976710655                                                                /*   2^48 - 1  */
    rule minUInt56       =>  0
    rule maxUInt56       =>  72057594037927935                                                              /*   2^56 - 1  */
    rule minUInt64       =>  0
    rule maxUInt64       =>  18446744073709551615                                                           /*   2^64 - 1  */
    rule minUInt72       =>  0
    rule maxUInt72       =>  4722366482869645213695                                                         /*   2^72 - 1  */
    rule minUInt80       =>  0
    rule maxUInt80       =>  1208925819614629174706175                                                      /*   2^80 - 1  */
    rule minUInt88       =>  0
    rule maxUInt88       =>  309485009821345068724781055                                                    /*   2^88 - 1  */
    rule minUInt96       =>  0
    rule maxUInt96       =>  79228162514264337593543950335                                                  /*   2^96 - 1  */
    rule minUInt104      =>  0
    rule maxUInt104      =>  20282409603651670423947251286015                                               /*   2^104 - 1  */
    rule minUInt112      =>  0
    rule maxUInt112      =>  5192296858534827628530496329220095                                             /*   2^112 - 1  */
    rule minUInt120      =>  0
    rule maxUInt120      =>  1329227995784915872903807060280344575                                          /*   2^120 - 1  */
    rule minUInt128      =>  0
    rule maxUInt128      =>  340282366920938463463374607431768211455                                        /*   2^128 - 1  */
    rule minUInt136      =>  0
    rule maxUInt136      =>  87112285931760246646623899502532662132735                                      /*   2^136 - 1  */
    rule minUInt144      =>  0
    rule maxUInt144      =>  22300745198530623141535718272648361505980415                                   /*   2^144 - 1  */
    rule minUInt152      =>  0
    rule maxUInt152      =>  5708990770823839524233143877797980545530986495                                 /*   2^152 - 1  */
    rule minUInt160      =>  0
    rule maxUInt160      =>  1461501637330902918203684832716283019655932542975                              /*   2^160 - 1  */
    rule minUInt168      =>  0
    rule maxUInt168      =>  374144419156711147060143317175368453031918731001855                            /*   2^168 - 1  */
    rule minUInt176      =>  0
    rule maxUInt176      =>  95780971304118053647396689196894323976171195136475135                          /*   2^176 - 1  */
    rule minUInt184      =>  0
    rule maxUInt184      =>  24519928653854221733733552434404946937899825954937634815                       /*   2^184 - 1  */
    rule minUInt192      =>  0
    rule maxUInt192      =>  6277101735386680763835789423207666416102355444464034512895                     /*   2^192 - 1  */
    rule minUInt200      =>  0
    rule maxUInt200      =>  1606938044258990275541962092341162602522202993782792835301375                  /*   2^200 - 1  */
    rule minUInt208      =>  0
    rule maxUInt208      =>  411376139330301510538742295639337626245683966408394965837152255                /*   2^208 - 1  */
    rule minUInt216      =>  0
    rule maxUInt216      =>  105312291668557186697918027683670432318895095400549111254310977535             /*   2^216 - 1  */
    rule minUInt224      =>  0
    rule maxUInt224      =>  26959946667150639794667015087019630673637144422540572481103610249215           /*   2^224 - 1  */
    rule minUInt232      =>  0
    rule maxUInt232      =>  6901746346790563787434755862277025452451108972170386555162524223799295         /*   2^232 - 1  */
    rule minUInt240      =>  0
    rule maxUInt240      =>  1766847064778384329583297500742918515827483896875618958121606201292619775      /*   2^240 - 1  */
    rule minUInt248      =>  0
    rule maxUInt248      =>  452312848583266388373324160190187140051835877600158453279131187530910662655    /*   2^248 - 1  */
    rule minUInt256      =>  0
    rule maxUInt256      =>  115792089237316195423570985008687907853269984665640564039457584007913129639935 /*   2^256 - 1  */

    rule minUFixed128x10 =>  0
    rule maxUFixed128x10 =>  3402823669209384634633746074317682114550000000000                              /* ( 2^128 - 1) * 10^10 */

    syntax Int ::= "notMaxUInt160" [alias] /* FFFFFFFFFFFFFFFFFFFFFFFF0000000000000000000000000000000000000000 */
 // -------------------------------------------------------------------------------------------------------------
    rule notMaxUInt160 => 115792089237316195423570985007226406215939081747436879206741300988257197096960

    syntax Int ::= "eth" [macro]
 // ----------------------------
    rule eth => 1000000000000000000
```

Range of types
--------------

```k
    syntax Bool ::= #rangeBool    ( Int )             [alias]
                  | #rangeSInt    ( Int , Int )       [alias]
                  | #rangeUInt    ( Int , Int )       [alias]
                  | #rangeSFixed  ( Int , Int , Int ) [alias]
                  | #rangeUFixed  ( Int , Int , Int ) [alias]
                  | #rangeAddress ( Int )             [alias]
                  | #rangeBytes   ( Int , Int )       [alias]
                  | #rangeNonce   ( Int )             [alias]
                  | #rangeSmall   ( Int )             [alias]
 // ---------------------------------------------------------
    rule #rangeBool    (            X ) => X ==Int 0 orBool X ==Int 1

    rule #rangeSInt    ( 128 ,      X ) => #range ( minSInt128      <= X <= maxSInt128      )
    rule #rangeSInt    ( 256 ,      X ) => #range ( minSInt256      <= X <= maxSInt256      )

    rule #rangeUInt    (   8 ,      X ) => #range ( minUInt8        <= X <  pow8            )
    rule #rangeUInt    (  16 ,      X ) => #range ( minUInt16       <= X <  pow16           )
    rule #rangeUInt    (  24 ,      X ) => #range ( minUInt24       <= X <  pow24           )
    rule #rangeUInt    (  32 ,      X ) => #range ( minUInt32       <= X <  pow32           )
    rule #rangeUInt    (  40 ,      X ) => #range ( minUInt40       <= X <  pow40           )
    rule #rangeUInt    (  48 ,      X ) => #range ( minUInt48       <= X <  pow48           )
    rule #rangeUInt    (  56 ,      X ) => #range ( minUInt56       <= X <  pow56           )
    rule #rangeUInt    (  64 ,      X ) => #range ( minUInt64       <= X <  pow64           )
    rule #rangeUInt    (  72 ,      X ) => #range ( minUInt72       <= X <  pow72           )
    rule #rangeUInt    (  80 ,      X ) => #range ( minUInt80       <= X <  pow80           )
    rule #rangeUInt    (  88 ,      X ) => #range ( minUInt88       <= X <  pow88           )
    rule #rangeUInt    (  96 ,      X ) => #range ( minUInt96       <= X <  pow96           )
    rule #rangeUInt    ( 104 ,      X ) => #range ( minUInt104      <= X <  pow104          )
    rule #rangeUInt    ( 112 ,      X ) => #range ( minUInt112      <= X <  pow112          )
    rule #rangeUInt    ( 120 ,      X ) => #range ( minUInt120      <= X <  pow120          )
    rule #rangeUInt    ( 128 ,      X ) => #range ( minUInt128      <= X <  pow128          )
    rule #rangeUInt    ( 136 ,      X ) => #range ( minUInt136      <= X <  pow136          )
    rule #rangeUInt    ( 144 ,      X ) => #range ( minUInt144      <= X <  pow144          )
    rule #rangeUInt    ( 152 ,      X ) => #range ( minUInt152      <= X <  pow152          )
    rule #rangeUInt    ( 160 ,      X ) => #range ( minUInt160      <= X <  pow160          )
    rule #rangeUInt    ( 168 ,      X ) => #range ( minUInt168      <= X <  pow168          )
    rule #rangeUInt    ( 176 ,      X ) => #range ( minUInt176      <= X <  pow176          )
    rule #rangeUInt    ( 184 ,      X ) => #range ( minUInt184      <= X <  pow184          )
    rule #rangeUInt    ( 192 ,      X ) => #range ( minUInt192      <= X <  pow192          )
    rule #rangeUInt    ( 200 ,      X ) => #range ( minUInt200      <= X <  pow200          )
    rule #rangeUInt    ( 208 ,      X ) => #range ( minUInt208      <= X <  pow208          )
    rule #rangeUInt    ( 216 ,      X ) => #range ( minUInt216      <= X <  pow216          )
    rule #rangeUInt    ( 224 ,      X ) => #range ( minUInt224      <= X <  pow224          )
    rule #rangeUInt    ( 232 ,      X ) => #range ( minUInt232      <= X <  pow232          )
    rule #rangeUInt    ( 240 ,      X ) => #range ( minUInt240      <= X <  pow240          )
    rule #rangeUInt    ( 248 ,      X ) => #range ( minUInt248      <= X <  pow248          )
    rule #rangeUInt    ( 256 ,      X ) => #range ( minUInt256      <= X <  pow256          )

    rule #rangeSFixed  ( 128 , 10 , X ) => #range ( minSFixed128x10 <= X <= maxSFixed128x10 )
    rule #rangeUFixed  ( 128 , 10 , X ) => #range ( minUFixed128x10 <= X <= maxUFixed128x10 )
    rule #rangeAddress (            X ) => #range ( minUInt160      <= X <  pow160          )
    rule #rangeBytes   (   N ,      X ) => #range ( 0               <= X <  1 <<Byte N      )
    rule #rangeNonce   (   X          ) => #range ( 0               <= X < maxUInt64        )
    rule #rangeSmall   (   X          ) => #range ( 0               <= X < 10               )

    syntax Bool ::= "#range" "(" Int "<"  Int "<"  Int ")" [macro]
                  | "#range" "(" Int "<"  Int "<=" Int ")" [macro]
                  | "#range" "(" Int "<=" Int "<"  Int ")" [macro]
                  | "#range" "(" Int "<=" Int "<=" Int ")" [macro]
 // --------------------------------------------------------------
    rule #range ( LB <  X <  UB ) => LB  <Int X andBool X  <Int UB
    rule #range ( LB <  X <= UB ) => LB  <Int X andBool X <=Int UB
    rule #range ( LB <= X <  UB ) => LB <=Int X andBool X  <Int UB
    rule #range ( LB <= X <= UB ) => LB <=Int X andBool X <=Int UB
```

-   `chop` interprets an integer modulo `2^256`.

```k
    syntax Int ::= chop ( Int ) [function, functional, smtlib(chop)]
 // ----------------------------------------------------------------
    rule chop ( I:Int ) => I modInt pow256 [concrete, smt-lemma]
```
-   `_<<Byte_` shifts an integer 8 bits to the left.
-   `_>>Byte_` shifts an integer 8 bits to the right.

```k
    syntax Int ::= Int "<<Byte" Int [function]
                 | Int ">>Byte" Int [function]
 // ------------------------------------------
    rule N <<Byte M => N <<Int (8 *Int M)
    rule N >>Byte M => N >>Int (8 *Int M)

endmodule
```
