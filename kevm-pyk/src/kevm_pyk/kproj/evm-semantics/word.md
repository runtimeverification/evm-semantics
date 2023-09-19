Core definitions for `Word`
===========================

In this file are defined the basic components for EVM words.

```k
module WORD
    imports INT
    imports BOOL
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
                 | "pow8"   [macro] /* 2 ^Int 8"   */
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
    syntax Int ::= "minSInt8"        [alias]
                 | "minSInt8Word"    [alias]
                 | "maxSInt8"        [alias]
                 | "minSInt16"       [alias]
                 | "minSInt16Word"   [alias]
                 | "maxSInt16"       [alias]
                 | "minSInt24"       [alias]
                 | "minSInt24Word"   [alias]
                 | "maxSInt24"       [alias]
                 | "minSInt32"       [alias]
                 | "minSInt32Word"   [alias]
                 | "maxSInt32"       [alias]
                 | "minSInt40"       [alias]
                 | "minSInt40Word"   [alias]
                 | "maxSInt40"       [alias]
                 | "minSInt48"       [alias]
                 | "minSInt48Word"   [alias]
                 | "maxSInt48"       [alias]
                 | "minSInt56"       [alias]
                 | "minSInt56Word"   [alias]
                 | "maxSInt56"       [alias]
                 | "minSInt64"       [alias]
                 | "minSInt64Word"   [alias]
                 | "maxSInt64"       [alias]
                 | "minSInt72"       [alias]
                 | "minSInt72Word"   [alias]
                 | "maxSInt72"       [alias]
                 | "minSInt80"       [alias]
                 | "minSInt80Word"   [alias]
                 | "maxSInt80"       [alias]
                 | "minSInt88"       [alias]
                 | "minSInt88Word"   [alias]
                 | "maxSInt88"       [alias]
                 | "minSInt96"       [alias]
                 | "minSInt96Word"   [alias]
                 | "maxSInt96"       [alias]
                 | "minSInt104"      [alias]
                 | "minSInt104Word"  [alias]
                 | "maxSInt104"      [alias]
                 | "minSInt112"      [alias]
                 | "minSInt112Word"  [alias]
                 | "maxSInt112"      [alias]
                 | "minSInt120"      [alias]
                 | "minSInt120Word"  [alias]
                 | "maxSInt120"      [alias]
                 | "minSInt128"      [alias]
                 | "minSInt128Word"  [alias]
                 | "maxSInt128"      [alias]
                 | "minSInt136"      [alias]
                 | "minSInt136Word"  [alias]
                 | "maxSInt136"      [alias]
                 | "minSInt144"      [alias]
                 | "minSInt144Word"  [alias]
                 | "maxSInt144"      [alias]
                 | "minSInt152"      [alias]
                 | "minSInt152Word"  [alias]
                 | "maxSInt152"      [alias]
                 | "minSInt160"      [alias]
                 | "minSInt160Word"  [alias]
                 | "maxSInt160"      [alias]
                 | "minSInt168"      [alias]
                 | "minSInt168Word"  [alias]
                 | "maxSInt168"      [alias]
                 | "minSInt176"      [alias]
                 | "minSInt176Word"  [alias]
                 | "maxSInt176"      [alias]
                 | "minSInt184"      [alias]
                 | "minSInt184Word"  [alias]
                 | "maxSInt184"      [alias]
                 | "minSInt192"      [alias]
                 | "minSInt192Word"  [alias]
                 | "maxSInt192"      [alias]
                 | "minSInt200"      [alias]
                 | "minSInt200Word"  [alias]
                 | "maxSInt200"      [alias]
                 | "minSInt208"      [alias]
                 | "minSInt208Word"  [alias]
                 | "maxSInt208"      [alias]
                 | "minSInt216"      [alias]
                 | "minSInt216Word"  [alias]
                 | "maxSInt216"      [alias]
                 | "minSInt224"      [alias]
                 | "minSInt224Word"  [alias]
                 | "maxSInt224"      [alias]
                 | "minSInt232"      [alias]
                 | "minSInt232Word"  [alias]
                 | "maxSInt232"      [alias]
                 | "minSInt240"      [alias]
                 | "minSInt240Word"  [alias]
                 | "maxSInt240"      [alias]
                 | "minSInt248"      [alias]
                 | "minSInt248Word"  [alias]
                 | "maxSInt248"      [alias]
                 | "minSInt256"      [alias]
                 | "minSInt256Word"  [alias]
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
    rule minSInt8        => -128                                                                            /*  -2^7                */
    rule minSInt8Word    =>  115792089237316195423570985008687907853269984665640564039457584007913129639808 /*  -2^7 as evm word    */
    rule maxSInt8        =>  127                                                                            /*   2^7 - 1            */
    rule minSInt16       => -32768                                                                          /*  -2^15               */
    rule minSInt16Word   =>  115792089237316195423570985008687907853269984665640564039457584007913129607168 /*  -2^15 as evm word   */
    rule maxSInt16       =>  32767                                                                          /*   2^15 - 1           */
    rule minSInt24       => -8388608                                                                        /*  -2^23               */
    rule minSInt24Word   =>  115792089237316195423570985008687907853269984665640564039457584007913121251328 /*  -2^23 as evm word   */
    rule maxSInt24       =>  8388607                                                                        /*   2^23 - 1           */
    rule minSInt32       => -2147483648                                                                     /*  -2^31               */
    rule minSInt32Word   =>  115792089237316195423570985008687907853269984665640564039457584007910982156288 /*  -2^31 as evm word   */
    rule maxSInt32       =>  2147483647                                                                     /*   2^31 - 1           */
    rule minSInt40       => -549755813888                                                                   /*  -2^39               */
    rule minSInt40Word   =>  115792089237316195423570985008687907853269984665640564039457584007363373826048 /*  -2^39 as evm word   */
    rule maxSInt40       =>  549755813887                                                                   /*   2^39 - 1           */
    rule minSInt48       => -140737488355328                                                                /*  -2^47               */
    rule minSInt48Word   =>  115792089237316195423570985008687907853269984665640564039457583867175641284608 /*  -2^47 as evm word   */
    rule maxSInt48       =>  140737488355327                                                                /*   2^47 - 1           */
    rule minSInt56       => -36028797018963968                                                              /*  -2^55               */
    rule minSInt56Word   =>  115792089237316195423570985008687907853269984665640564039457547979116110675968 /*  -2^55 as evm word   */
    rule maxSInt56       =>  36028797018963967                                                              /*   2^55 - 1           */
    rule minSInt64       => -9223372036854775808                                                            /*  -2^63               */
    rule minSInt64Word   =>  115792089237316195423570985008687907853269984665640564039448360635876274864128 /*  -2^63 as evm word   */
    rule maxSInt64       =>  9223372036854775807                                                            /*   2^63 - 1           */
    rule minSInt72       => -2361183241434822606848                                                         /*  -2^71               */
    rule minSInt72Word   =>  115792089237316195423570985008687907853269984665640564037096400766478307033088 /*  -2^71 as evm word   */
    rule maxSInt72       =>  2361183241434822606847                                                         /*   2^71 - 1           */
    rule minSInt80       => -604462909807314587353088                                                       /*  -2^79               */
    rule minSInt80Word   =>  115792089237316195423570985008687907853269984665640563434994674200598542286848 /*  -2^79 as evm word   */
    rule maxSInt80       =>  604462909807314587353087                                                       /*   2^79 - 1           */
    rule minSInt88       => -154742504910672534362390528                                                    /*  -2^87               */
    rule minSInt88Word   =>  115792089237316195423570985008687907853269984665640409296952673335378767249408 /*  -2^87 as evm word   */
    rule maxSInt88       =>  154742504910672534362390527                                                    /*   2^87 - 1           */
    rule minSInt96       => -39614081257132168796771975168                                                  /*  -2^95               */
    rule minSInt96Word   =>  115792089237316195423570985008687907853269984665600949958200451839116357664768 /*  -2^95 as evm word   */
    rule maxSInt96       =>  39614081257132168796771975167                                                  /*   2^95 - 1           */
    rule minSInt104      => -10141204801825835211973625643008                                               /*  -2^103              */
    rule minSInt104Word  =>  115792089237316195423570985008687907853269984655499359237631748795939503996928 /*  -2^103 as evm word  */
    rule maxSInt104      =>  10141204801825835211973625643007                                               /*   2^103 - 1          */
    rule minSInt112      => -2596148429267413814265248164610048                                             /*  -2^111              */
    rule minSInt112Word  =>  115792089237316195423570985008687907853269982069492134772043769742664965029888 /*  -2^111 as evm word  */
    rule maxSInt112      =>  2596148429267413814265248164610047                                             /*   2^111 - 1          */
    rule minSInt120      => -664613997892457936451903530140172288                                           /*  -2^119              */
    rule minSInt120Word  =>  115792089237316195423570985008687907853269320051642671581521132104382989467648 /*  -2^119 as evm word  */
    rule maxSInt120      =>  664613997892457936451903530140172287                                           /*   2^119 - 1          */
    rule minSInt128      => -170141183460469231731687303715884105728                                        /*  -2^127              */
    rule minSInt128Word  =>  115792089237316195423570985008687907853099843482180094807725896704197245534208 /*  -2^127 as evm word  */
    rule maxSInt128      =>  170141183460469231731687303715884105727                                        /*   2^127 as evm word  */
    rule minSInt136      => -43556142965880123323311949751266331066368                                      /*  -2^135               */
    rule minSInt136Word  =>  115792089237316195423570985008687907809713841699760440716145634256646798573568 /*  -2^135 as evm word   */
    rule maxSInt136      =>  43556142965880123323311949751266331066367                                      /*   2^135 - 1           */
    rule minSInt144      => -11150372599265311570767859136324180752990208                                   /*  -2^143               */
    rule minSInt144Word  =>  115792089237316195423570985008687896702897385400328993271598447683732376649728 /*  -2^143 as evm word   */
    rule maxSInt144      =>  11150372599265311570767859136324180752990207                                   /*   2^143 - 1           */
    rule minSInt152      => -2854495385411919762116571938898990272765493248                                 /*  -2^151               */
    rule minSInt152Word  =>  115792089237316195423570985008685053357884572745878447467518685017640364146688 /*  -2^151 as evm word   */
    rule maxSInt152      =>  2854495385411919762116571938898990272765493247                                 /*   2^151 - 1           */
    rule minSInt160      => -730750818665451459101842416358141509827966271488                               /*  -2^159               */
    rule minSInt160Word  =>  115792089237316195423570985007957157034604533206538721623099442498085163368448 /*  -2^159 as evm word   */
    rule maxSInt160      =>  730750818665451459101842416358141509827966271487                               /*   2^159 - 1           */
    rule minSInt168      => -187072209578355573530071658587684226515959365500928                            /*  -2^167               */
    rule minSInt168Word  =>  115792089237316195423570984821615698274914411135568905451773357491953764139008 /*  -2^167 as evm word   */
    rule maxSInt168      =>  187072209578355573530071658587684226515959365500927                            /*   2^167 - 1           */
    rule minSInt176      => -47890485652059026823698344598447161988085597568237568                          /*  -2^175               */
    rule minSInt176Word  =>  115792089237316195423570937118202255794243160967295965592295595922315561402368 /*  -2^175 as evm word   */
    rule maxSInt176      =>  47890485652059026823698344598447161988085597568237567                          /*   2^175 - 1           */
    rule minSInt184      => -12259964326927110866866776217202473468949912977468817408                       /*  -2^183               */
    rule minSInt184Word  =>  115792089237316195423558725044360980742403117889423361565988634094935660822528 /*  -2^183 as evm word   */
    rule maxSInt184      =>  12259964326927110866866776217202473468949912977468817407                       /*   2^183 - 1           */
    rule minSInt192      => -3138550867693340381917894711603833208051177722232017256448                     /*  -2^191               */
    rule minSInt192Word  =>  115792089237316195420432434140994567471352089954036730831406406285681112383488 /*  -2^191 as evm word   */
    rule maxSInt192      =>  3138550867693340381917894711603833208051177722232017256447                     /*   2^191 - 1           */
    rule minSInt200      => -803469022129495137770981046170581301261101496891396417650688                   /*  -2^199               */
    rule minSInt200Word  =>  115792089237316194620101962879192770082288938495059262778356087116516711989248 /*  -2^199 as evm word   */
    rule maxSInt200      =>  803469022129495137770981046170581301261101496891396417650687                   /*   2^199 - 1           */
    rule minSInt208      => -205688069665150755269371147819668813122841983204197482918576128                /*  -2^207                */
    rule minSInt208Word  =>  115792089237315989735501319857932638482122164996827441197474379810430211063808 /*  -2^207  as evm word   */
    rule maxSInt208      =>  205688069665150755269371147819668813122841983204197482918576127                /*   2^207  - 1           */
    rule minSInt216      => -52656145834278593348959013841835216159447547700274555627155488768              /*  -2^215                */
    rule minSInt216Word  =>  115792089237263539277736706415338948839428149449481116491757309452285974151168 /*  -2^215  as evm word   */
    rule maxSInt216      =>  52656145834278593348959013841835216159447547700274555627155488767              /*   2^215  - 1           */
    rule minSInt224      => -13479973333575319897333507543509815336818572211270286240551805124608           /*  -2^223               */
    rule minSInt224Word  =>  115792089223836222089995665111354400309760169328821991828187297767361324515328 /*  -2^223  as evm word  */
    rule maxSInt224      =>  13479973333575319897333507543509815336818572211270286240551805124607           /*   2^223  - 1          */
    rule minSInt232      => -3450873173395281893717377931138512726225554486085193277581262111899648         /*  -2^231               */
    rule minSInt232Word  =>  115792085786443022028289091291309976714757258440086077954264306426651017740288 /*  -2^231  as evm word  */
    rule maxSInt232      =>  3450873173395281893717377931138512726225554486085193277581262111899647         /*   2^231  - 1          */
    rule minSInt240      => -883423532389192164791648750371459257913741948437809479060803100646309888       /*  -2^239               */
    rule minSInt240Word  =>  115791205813783806231406193359937536394012070923692126229978523204812483330048 /*  -2^239  as evm word  */
    rule maxSInt240      =>  883423532389192164791648750371459257913741948437809479060803100646309887       /*   2^239  - 1          */
    rule minSInt248      => -226156424291633194186662080095093570025917938800079226639565593765455331328    /*  -2^247               */
    rule minSInt248Word  =>  115565932813024562229384322928592814283244066726840484812818018414147674308608 /*  -2^247  as evm word  */
    rule maxSInt248      =>  226156424291633194186662080095093570025917938800079226639565593765455331327    /*   2^247  - 1          */
    rule minSInt256      => -57896044618658097711785492504343953926634992332820282019728792003956564819968  /*  -2^255               */
    rule minSInt256Word  =>  57896044618658097711785492504343953926634992332820282019728792003956564819968  /*  -2^255  as evm word  */
    rule maxSInt256      =>  57896044618658097711785492504343953926634992332820282019728792003956564819967  /*   2^255  - 1          */

    rule minSFixed128x10 => -1701411834604692317316873037158841057280000000000                              /* (-2^487    ) * 10^10 */
    rule maxSFixed128x10 =>  1701411834604692317316873037158841057270000000000                              /* ( 2^487 - 1) * 10^10 */

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

    syntax Int ::= "notMaxUInt5"   [alias] /* FFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFE0 */
                 | "notMaxUInt8"   [alias] /* FFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFF00 */
                 | "notMaxUInt16"  [alias] /* FFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFF0000 */
                 | "notMaxUInt32"  [alias] /* FFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFF00000000 */
                 | "notMaxUInt64"  [alias] /* FFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFF0000000000000000 */
                 | "notMaxUInt96"  [alias] /* FFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFF000000000000000000000000 */
                 | "notMaxUInt128" [alias] /* FFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFF00000000000000000000000000000000 */
                 | "notMaxUInt160" [alias] /* FFFFFFFFFFFFFFFFFFFFFFFF0000000000000000000000000000000000000000 */
                 | "notMaxUInt192" [alias] /* FFFFFFFFFFFFFFFF000000000000000000000000000000000000000000000000 */
                 | "notMaxUInt208" [alias] /* FFFFFFFFFFFF0000000000000000000000000000000000000000000000000000 */
                 | "notMaxUInt224" [alias] /* FFFFFFFF00000000000000000000000000000000000000000000000000000000 */
                 | "notMaxUInt240" [alias] /* FFFF000000000000000000000000000000000000000000000000000000000000 */
                 | "notMaxUInt248" [alias] /* FF00000000000000000000000000000000000000000000000000000000000000 */
 // -------------------------------------------------------------------------------------------------------------
    rule notMaxUInt5   => 115792089237316195423570985008687907853269984665640564039457584007913129639904
    rule notMaxUInt8   => 115792089237316195423570985008687907853269984665640564039457584007913129639680
    rule notMaxUInt16  => 115792089237316195423570985008687907853269984665640564039457584007913129574400
    rule notMaxUInt32  => 115792089237316195423570985008687907853269984665640564039457584007908834672640
    rule notMaxUInt64  => 115792089237316195423570985008687907853269984665640564039439137263839420088320
    rule notMaxUInt96  => 115792089237316195423570985008687907853269984665561335876943319670319585689600
    rule notMaxUInt128 => 115792089237316195423570985008687907852929702298719625575994209400481361428480
    rule notMaxUInt160 => 115792089237316195423570985007226406215939081747436879206741300988257197096960
    rule notMaxUInt192 => 115792089237316195417293883273301227089434195242432897623355228563449095127040
    rule notMaxUInt208 => 115792089237315784047431654707177369110974345328014318355491175612947292487680
    rule notMaxUInt224 => 115792089210356248756420345214020892766250353992003419616917011526809519390720
    rule notMaxUInt240 => 115790322390251417039241401711187164934754157181743688420499462401711837020160
    rule notMaxUInt248 => 115339776388732929035197660848497720713218148788040405586178452820382218977280

    syntax Int ::= "eth"         [macro]
                 | "maxBlockNum" [macro] /* 7FFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFF == (2 ^ 256) - (2 ^ 255) - 1 */
 // ----------------------------------------------------------------------------------------------------------------------------------------
    rule eth         => 1000000000000000000
    rule maxBlockNum => 57896044618658097711785492504343953926634992332820282019728792003956564819967
```

Range of types
--------------

```k
    syntax Bool ::= #rangeBool     ( Int )             [alias]
                  | #rangeSInt     ( Int , Int )       [alias]
                  | #rangeUInt     ( Int , Int )       [alias]
                  | #rangeSFixed   ( Int , Int , Int ) [alias]
                  | #rangeUFixed   ( Int , Int , Int ) [alias]
                  | #rangeAddress  ( Int )             [alias]
                  | #rangeBytes    ( Int , Int )       [alias]
                  | #rangeNonce    ( Int )             [alias]
                  | #rangeSmall    ( Int )             [alias]
                  | #rangeBlockNum ( Int )             [alias]
 // ----------------------------------------------------------
    rule #rangeBool    (            X ) => X ==Int 0 orBool X ==Int 1

    rule #rangeSInt    (   8 ,      X ) => #range ( minSInt8        <= X <= maxSInt8        )
    rule #rangeSInt    (  16 ,      X ) => #range ( minSInt16       <= X <= maxSInt16       )
    rule #rangeSInt    (  24 ,      X ) => #range ( minSInt24       <= X <= maxSInt24       )
    rule #rangeSInt    (  32 ,      X ) => #range ( minSInt32       <= X <= maxSInt32       )
    rule #rangeSInt    (  40 ,      X ) => #range ( minSInt40       <= X <= maxSInt40       )
    rule #rangeSInt    (  48 ,      X ) => #range ( minSInt48       <= X <= maxSInt48       )
    rule #rangeSInt    (  56 ,      X ) => #range ( minSInt56       <= X <= maxSInt56       )
    rule #rangeSInt    (  64 ,      X ) => #range ( minSInt64       <= X <= maxSInt64       )
    rule #rangeSInt    (  72 ,      X ) => #range ( minSInt72       <= X <= maxSInt72       )
    rule #rangeSInt    (  80 ,      X ) => #range ( minSInt80       <= X <= maxSInt80       )
    rule #rangeSInt    (  88 ,      X ) => #range ( minSInt88       <= X <= maxSInt88       )
    rule #rangeSInt    (  96 ,      X ) => #range ( minSInt96       <= X <= maxSInt96       )
    rule #rangeSInt    ( 104 ,      X ) => #range ( minSInt104      <= X <= maxSInt104      )
    rule #rangeSInt    ( 112 ,      X ) => #range ( minSInt112      <= X <= maxSInt112      )
    rule #rangeSInt    ( 120 ,      X ) => #range ( minSInt120      <= X <= maxSInt120      )
    rule #rangeSInt    ( 128 ,      X ) => #range ( minSInt128      <= X <= maxSInt128      )
    rule #rangeSInt    ( 136 ,      X ) => #range ( minSInt136      <= X <= maxSInt136      )
    rule #rangeSInt    ( 144 ,      X ) => #range ( minSInt144      <= X <= maxSInt144      )
    rule #rangeSInt    ( 152 ,      X ) => #range ( minSInt152      <= X <= maxSInt152      )
    rule #rangeSInt    ( 160 ,      X ) => #range ( minSInt160      <= X <= maxSInt160      )
    rule #rangeSInt    ( 168 ,      X ) => #range ( minSInt168      <= X <= maxSInt168      )
    rule #rangeSInt    ( 176 ,      X ) => #range ( minSInt176      <= X <= maxSInt176      )
    rule #rangeSInt    ( 184 ,      X ) => #range ( minSInt184      <= X <= maxSInt184      )
    rule #rangeSInt    ( 192 ,      X ) => #range ( minSInt192      <= X <= maxSInt192      )
    rule #rangeSInt    ( 200 ,      X ) => #range ( minSInt200      <= X <= maxSInt200      )
    rule #rangeSInt    ( 208 ,      X ) => #range ( minSInt208      <= X <= maxSInt208      )
    rule #rangeSInt    ( 216 ,      X ) => #range ( minSInt216      <= X <= maxSInt216      )
    rule #rangeSInt    ( 224 ,      X ) => #range ( minSInt224      <= X <= maxSInt224      )
    rule #rangeSInt    ( 232 ,      X ) => #range ( minSInt232      <= X <= maxSInt232      )
    rule #rangeSInt    ( 240 ,      X ) => #range ( minSInt240      <= X <= maxSInt240      )
    rule #rangeSInt    ( 248 ,      X ) => #range ( minSInt248      <= X <= maxSInt248      )
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

    rule #rangeSFixed   ( 128 , 10 , X ) => #range ( minSFixed128x10 <= X <= maxSFixed128x10 )
    rule #rangeUFixed   ( 128 , 10 , X ) => #range ( minUFixed128x10 <= X <= maxUFixed128x10 )
    rule #rangeAddress  (            X ) => #range ( minUInt160      <= X <  pow160          )
    rule #rangeBytes    (   N ,      X ) => #range ( 0               <= X <  1 <<Byte N      )
    rule #rangeNonce    (   X          ) => #range ( 0               <= X < maxUInt64        )
    rule #rangeSmall    (   X          ) => #range ( 0               <= X < 10               )
    rule #rangeBlockNum (   X          ) => #range ( 0               <= X <= maxBlockNum     )

    syntax Bool ::= "#range" "(" Int "<"  Int "<"  Int ")" [alias]
                  | "#range" "(" Int "<"  Int "<=" Int ")" [alias]
                  | "#range" "(" Int "<=" Int "<"  Int ")" [alias]
                  | "#range" "(" Int "<=" Int "<=" Int ")" [alias]
 // --------------------------------------------------------------
    rule #range ( LB <  X <  UB ) => LB  <Int X andBool X  <Int UB
    rule #range ( LB <  X <= UB ) => LB  <Int X andBool X <=Int UB
    rule #range ( LB <= X <  UB ) => LB <=Int X andBool X  <Int UB
    rule #range ( LB <= X <= UB ) => LB <=Int X andBool X <=Int UB
```

-   `chop` interprets an integer modulo `2^256`.

```k
    syntax Int ::= chop ( Int ) [function, total, smtlib(chop)]
 // -----------------------------------------------------------
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
