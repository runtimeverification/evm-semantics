KEVM Gas
========

Here is a representation of `Gas`. This sort is used by `<gas>`, `<callGas>`, and `<gasUsed>` cells of the EVM configuration. As is in this file, `Gas` is a super-sort of `Int` with no differing behaviour. However the distinction at this level allows for an extension of infinite gas later, see `infinite-gas.md`.

```k
requires "schedule.md"

module GAS-SYNTAX
    imports INT-SYNTAX

    syntax Gas ::= Int
    syntax Int ::= "gas2Int" "(" Gas ")" [function, total]

    syntax Gas ::= "minGas" "(" Gas "," Gas ")" [function, total]
                 > left:
                   Gas "*Gas" Gas [function, total]
                 | Gas "/Gas" Gas [function]
                 > left:
                   Gas "+Gas" Gas [function, total]
                 | Gas "-Gas" Gas [function, total]

    syntax Bool ::= Gas  "<Gas" Gas [function, total]
                  | Gas "<=Gas" Gas [function, total]
endmodule

module GAS
    imports INT
    imports BOOL
    imports GAS-SYNTAX
    imports GAS-SIMPLIFICATION
    imports GAS-FEES

    rule I1:Int *Gas I2:Int => I1 *Int I2
    rule I1:Int /Gas I2:Int => I1 /Int I2
    rule I1:Int +Gas I2:Int => I1 +Int I2
    rule I1:Int -Gas I2:Int => I1 -Int I2

    rule I1:Int  <Gas I2:Int => I1  <Int I2
    rule I1:Int <=Gas I2:Int => I1 <=Int I2

    rule minGas(I1:Int, I2:Int) => minInt(I1, I2)
    rule gas2Int(G:Int) => G
endmodule
```

KEVM Infinite Gas
=================

Here we use the construct `#gas` to represent positive infinity, while tracking the gas formula through execution.
This allows (i) computing final gas used, and (ii) never stopping because of out-of-gas.
Note that the argument to `#gas(_)` is just metadata tracking the current gas usage, and is not meant to be compared to other values.
As such, any `#gas(G)` and `#gas(G')` are the _same_ positive infinite, regardless of the values `G` and `G'`.
In particular, this means that `#gas(_) <Gas #gas(_) => false`, and `#gas(_) <=Gas #gas(_) => true`, regardless of the values contained in the `#gas(_)`.

```k
module INFINITE-GAS
    imports GAS

    syntax Gas ::= #gas(Int) [symbol(infGas), smtlib(infGas)]
 // ---------------------------------------------------------

    rule #gas(G) +Gas G'       => #gas(G +Int G')
    rule #gas(G) -Gas G'       => #gas(G -Int G')
    rule #gas(G) *Gas G'       => #gas(G *Int G')
    rule #gas(G) /Gas G'       => #gas(G /Int G')  requires G' =/=Int 0
    rule      G  +Gas #gas(G') => #gas(G +Int G')
    rule      G  -Gas #gas(G') => #gas(G -Int G')
    rule      G  *Gas #gas(G') => #gas(G *Int G')
    rule      G  /Gas #gas(G') => #gas(G /Int G')  requires G' =/=Int 0
    rule #gas(G) +Gas #gas(G') => #gas(G +Int G')
    rule #gas(G) -Gas #gas(G') => #gas(G -Int G')
    rule #gas(G) *Gas #gas(G') => #gas(G *Int G')
    rule #gas(G) /Gas #gas(G') => #gas(G /Int G')  requires G' =/=Int 0

    rule _:Int    <Gas #gas(_) => true
    rule #gas(_)  <Gas _       => false [simplification]
    rule #gas(_) <=Gas _:Int   => false
    rule _       <=Gas #gas(_) => true  [simplification]

    rule minGas(#gas(G), #gas(G')) => #gas(minInt(G, G'))
    rule minGas(G:Int  , #gas(G')) => #gas(minInt(G, G'))
    rule minGas(#gas(G), G':Int)   => #gas(minInt(G, G'))

    rule gas2Int(#gas(G)) => G

    rule #allBut64th(#gas(G)) => #gas(#allBut64th(G))
    rule Cgascap(SCHED, #gas(GCAP), #gas(GAVAIL), GEXTRA) => #gas(Cgascap(SCHED, GCAP, GAVAIL, GEXTRA)) [simplification]
    rule Cgascap(SCHED, #gas(GCAP), GAVAIL:Int, GEXTRA)   => #gas(Cgascap(SCHED, GCAP, GAVAIL, GEXTRA)) [simplification]
    rule Cgascap(SCHED, GCAP:Int, #gas(GAVAIL), GEXTRA)   => #gas(Cgascap(SCHED, GCAP, GAVAIL, GEXTRA)) [simplification]

    rule #if B #then #gas(G) #else #gas(G') #fi => #gas(#if B #then G #else G' #fi) [simplification]
endmodule
```

KEVM Gas Fees
=============

Here are some internal helper functions for calculating gas. Most of these functions are specified in the YellowPaper.

```k
module GAS-FEES
    imports GAS-SYNTAX
    imports SCHEDULE

    syntax Gas ::= Cgascap           ( Schedule , Gas , Gas , Int ) [symbol(Cgascap_Gas), overload(Cgascap), function, total, smtlib(gas_Cgascap_Gas)]
    syntax Int ::= Cgascap           ( Schedule , Int , Int , Int ) [symbol(Cgascap_Int), overload(Cgascap), function, total, smtlib(gas_Cgascap_Int)]

    syntax Int ::= Csstore            ( Schedule , Int , Int , Int )         [symbol(Csstore),             function, total, smtlib(gas_Csstore)            ]
                 | Rsstore            ( Schedule , Int , Int , Int )         [symbol(Rsstore),             function, total, smtlib(gas_Rsstore)            ]
                 | Cextra             ( Schedule , Bool , Int , Bool, Bool, Bool ) [symbol(Cextra),            function, total, smtlib(gas_Cextra)           ]
                 | Cnew               ( Schedule , Bool , Int )              [symbol(Cnew),                function, total, smtlib(gas_Cnew)               ]
                 | Cxfer              ( Schedule , Int )                     [symbol(Cxfer),               function, total, smtlib(gas_Cxfer)              ]
                 | Cmem               ( Schedule , Int )                     [symbol(Cmem),                function, total, smtlib(gas_Cmem), memo         ]
                 | Caddraccess        ( Schedule , Bool )                    [symbol(Caddraccess),         function, total, smtlib(gas_Caddraccess)        ]
                 | Cstorageaccess     ( Schedule , Bool )                    [symbol(Cstorageaccess),      function, total, smtlib(gas_Cstorageaccess)     ]
                 | Csload             ( Schedule , Bool )                    [symbol(Csload),              function, total, smtlib(gas_Csload)             ]
                 | Cextcodesize       ( Schedule )                           [symbol(Cextcodesize),        function, total, smtlib(gas_Cextcodesize)       ]
                 | Cextcodecopy       ( Schedule , Int )                     [symbol(Cextcodecopy),        function, total, smtlib(gas_Cextcodecopy)       ]
                 | Cextcodehash       ( Schedule )                           [symbol(Cextcodehash),        function, total, smtlib(gas_Cextcodehash)       ]
                 | Cbalance           ( Schedule )                           [symbol(Cbalance),            function, total, smtlib(gas_Cbalance)           ]
                 | Cmodexp            ( Schedule , Bytes , Int , Int , Int ) [symbol(Cmodexp),             function, total, smtlib(gas_Cmodexp)            ]
                 | Cinitcode          ( Schedule , Int )                     [symbol(Cinitcode),           function, total, smtlib(gas_Cinitcode)          ]
                 | Cbls12g1MsmDiscount( Schedule , Int )                     [symbol(Cbls12g1MsmDiscount), function, total, smtlib(gas_Cbls12g1MsmDiscount)]
                 | Cbls12g2MsmDiscount( Schedule , Int )                     [symbol(Cbls12g2MsmDiscount), function, total, smtlib(gas_Cbls12g2MsmDiscount)]
                 | Cdelegationaccess  ( Schedule, Bool, Bool )               [symbol(Cdelegationaccess), function, total, smtlib(gas_Cdelegationaccess)]

 // ------------------------------------------------------------------------------------------------------------------------------------------
    rule [Cgascap]:
         Cgascap(SCHED, GCAP:Int, GAVAIL:Int, GEXTRA)
      => #if GAVAIL <Int GEXTRA orBool Gstaticcalldepth << SCHED >> #then GCAP #else minInt(#allBut64th(GAVAIL -Int GEXTRA), GCAP) #fi
      requires 0 <=Int GCAP
      [concrete]

    rule Cgascap(_, GCAP, _, _) => 0 requires GCAP <Gas 0 [concrete]

    rule [Csstore.new]:
         Csstore(SCHED, NEW, CURR, ORIG)
      => #if CURR ==Int NEW orBool ORIG =/=Int CURR #then Gsload < SCHED > #else #if ORIG ==Int 0 #then Gsstoreset < SCHED > #else Gsstorereset < SCHED > #fi #fi
      requires Ghasdirtysstore << SCHED >>
      [concrete]

    rule [Csstore.old]:
         Csstore(SCHED, NEW, CURR, _ORIG)
      => #if CURR ==Int 0 andBool NEW =/=Int 0 #then Gsstoreset < SCHED > #else Gsstorereset < SCHED > #fi
      requires notBool Ghasdirtysstore << SCHED >>
      [concrete]

    rule [Rsstore.new]:
         Rsstore(SCHED, NEW, CURR, ORIG)
      => #if CURR =/=Int NEW andBool ORIG ==Int CURR andBool NEW ==Int 0 #then
             Rsstoreclear < SCHED >
         #else
             #if CURR =/=Int NEW andBool ORIG =/=Int CURR andBool ORIG =/=Int 0 #then
                 #if CURR ==Int 0 #then 0 -Int Rsstoreclear < SCHED > #else #if NEW ==Int 0 #then Rsstoreclear < SCHED > #else 0 #fi #fi
             #else
                 0
             #fi +Int
             #if CURR =/=Int NEW andBool ORIG ==Int NEW #then
                 #if ORIG ==Int 0 #then Gsstoreset < SCHED > #else Gsstorereset < SCHED > #fi -Int Gsload < SCHED >
             #else
                 0
             #fi
         #fi
      requires Ghasdirtysstore << SCHED >>
      [concrete]

    rule [Rsstore.old]:
         Rsstore(SCHED, NEW, CURR, _ORIG)
      => #if CURR =/=Int 0 andBool NEW ==Int 0 #then Rsstoreclear < SCHED > #else 0 #fi
      requires notBool Ghasdirtysstore << SCHED >>
      [concrete]

    rule [Cextra.delegation]: Cextra(SCHED, ISEMPTY, VALUE, ISWARM ,  ISDELEGATION,  ISWARMDELEGATION) => Cdelegationaccess(SCHED, ISDELEGATION, ISWARMDELEGATION) +Int Caddraccess(SCHED, ISWARM) +Int Cnew(SCHED, ISEMPTY, VALUE) +Int Cxfer(SCHED, VALUE) requires         Ghasaccesslist << SCHED >> andBool         Ghasdelegation << SCHED >>
    rule [Cextra.new]:        Cextra(SCHED, ISEMPTY, VALUE, ISWARM , _ISDELEGATION, _ISWARMDELEGATION) => Caddraccess(SCHED, ISWARM) +Int Cnew(SCHED, ISEMPTY, VALUE) +Int Cxfer(SCHED, VALUE)                                                               requires         Ghasaccesslist << SCHED >> andBool notBool Ghasdelegation << SCHED >>
    rule [Cextra.old]:        Cextra(SCHED, ISEMPTY, VALUE, _ISWARM, _ISDELEGATION, _ISWARMDELEGATION) => Gcall < SCHED > +Int Cnew(SCHED, ISEMPTY, VALUE) +Int Cxfer(SCHED, VALUE)                                                                                      requires notBool Ghasaccesslist << SCHED >>

    rule [Cnew]:
         Cnew(SCHED, ISEMPTY:Bool, VALUE)
      => #if ISEMPTY andBool (VALUE =/=Int 0 orBool Gzerovaluenewaccountgas << SCHED >>) #then Gnewaccount < SCHED > #else 0 #fi

    rule [Cxfer.none]: Cxfer(_SCHED, 0) => 0
    rule [Cxfer.some]: Cxfer( SCHED, N) => Gcallvalue < SCHED > requires N =/=Int 0

    rule [Cmem]: Cmem(SCHED, N) => (N *Int Gmemory < SCHED >) +Int ((N *Int N) /Int Gquadcoeff < SCHED >) [concrete]

    rule [Cdelegationaccess]: Cdelegationaccess(SCHED, ISDELEGATION, ISWARM) => #if ISDELEGATION #then Caddraccess(SCHED, ISWARM) #else 0 #fi
    rule [Caddraccess]:    Caddraccess(SCHED, ISWARM)    => #if ISWARM #then Gwarmstorageread < SCHED > #else Gcoldaccountaccess < SCHED > #fi
    rule [Cstorageaccess]: Cstorageaccess(SCHED, ISWARM) => #if ISWARM #then Gwarmstorageread < SCHED > #else Gcoldsload < SCHED >         #fi

    rule [Csload.new]: Csload(SCHED, ISWARM)  => Cstorageaccess(SCHED, ISWARM) requires         Ghasaccesslist << SCHED >>
    rule [Csload.old]: Csload(SCHED, _ISWARM) => Gsload < SCHED >              requires notBool Ghasaccesslist << SCHED >>

    rule [Cextcodesize.new]: Cextcodesize(SCHED) => 0                      requires         Ghasaccesslist << SCHED >>
    rule [Cextcodesize.old]: Cextcodesize(SCHED) => Gextcodesize < SCHED > requires notBool Ghasaccesslist << SCHED >>

    rule [Cextcodehash.new]: Cextcodehash(SCHED) => 0                  requires         Ghasaccesslist << SCHED >>
    rule [Cextcodehash.old]: Cextcodehash(SCHED) => Gbalance < SCHED > requires notBool Ghasaccesslist << SCHED >>

    rule [Cbalance.new]: Cbalance(SCHED) => 0                  requires         Ghasaccesslist << SCHED >>
    rule [Cbalance.old]: Cbalance(SCHED) => Gbalance < SCHED > requires notBool Ghasaccesslist << SCHED >>

    rule [Cextcodecopy.new]: Cextcodecopy(SCHED, WIDTH) => Gcopy < SCHED > *Int (WIDTH up/Int 32)                               requires         Ghasaccesslist << SCHED >> [concrete]
    rule [Cextcodecopy.old]: Cextcodecopy(SCHED, WIDTH) => Gextcodecopy < SCHED > +Int (Gcopy < SCHED > *Int (WIDTH up/Int 32)) requires notBool Ghasaccesslist << SCHED >> [concrete]

    rule [Cmodexp.old]: Cmodexp(SCHED, DATA, BASELEN, EXPLEN, MODLEN) => #multComplexity(maxInt(BASELEN, MODLEN)) *Int maxInt(#adjustedExpLength(BASELEN, EXPLEN, DATA), 1) /Int Gquaddivisor < SCHED >
      requires notBool Ghasaccesslist << SCHED >>
      [concrete]

    rule [Cmodexp.new]: Cmodexp(SCHED, DATA, BASELEN, EXPLEN, MODLEN) => maxInt(200, (#newMultComplexity(maxInt(BASELEN, MODLEN)) *Int maxInt(#adjustedExpLength(BASELEN, EXPLEN, DATA), 1)) /Int Gquaddivisor < SCHED > )
      requires Ghasaccesslist << SCHED >>
      [concrete]

    rule [Cinitcode.new]: Cinitcode(SCHED, INITCODELEN) => Ginitcodewordcost < SCHED > *Int ( INITCODELEN up/Int 32 ) requires         Ghasmaxinitcodesize << SCHED >> [concrete]
    rule [Cinitcode.old]: Cinitcode(SCHED, _)           => 0                                                          requires notBool Ghasmaxinitcodesize << SCHED >> [concrete]

    rule [Cbls12g1MsmDiscount.new]: Cbls12g1MsmDiscount(SCHED, N) => #Cbls12g1MsmDiscount( N ) requires         Ghasbls12msmdiscount << SCHED >> [concrete]
    rule [Cbls12g1MsmDiscount.old]: Cbls12g1MsmDiscount(SCHED, _) => 0                         requires notBool Ghasbls12msmdiscount << SCHED >> [concrete]

    rule [Cbls12g2MsmDiscount.new]: Cbls12g2MsmDiscount(SCHED, N) => #Cbls12g2MsmDiscount( N ) requires         Ghasbls12msmdiscount << SCHED >> [concrete]
    rule [Cbls12g2MsmDiscount.old]: Cbls12g2MsmDiscount(SCHED, _) => 0                         requires notBool Ghasbls12msmdiscount << SCHED >> [concrete]

    syntax Int ::= #Cbls12g1MsmDiscount( Int ) [function, total]
  // -----------------------------------------------------------
    rule #Cbls12g1MsmDiscount(N) => 1000 requires N <Int 1
    rule #Cbls12g1MsmDiscount(1) => 1000
    rule #Cbls12g1MsmDiscount(2) => 949
    rule #Cbls12g1MsmDiscount(3) => 848
    rule #Cbls12g1MsmDiscount(4) => 797
    rule #Cbls12g1MsmDiscount(5) => 764
    rule #Cbls12g1MsmDiscount(6) => 750
    rule #Cbls12g1MsmDiscount(7) => 738
    rule #Cbls12g1MsmDiscount(8) => 728
    rule #Cbls12g1MsmDiscount(9) => 719
    rule #Cbls12g1MsmDiscount(10) => 712
    rule #Cbls12g1MsmDiscount(11) => 705
    rule #Cbls12g1MsmDiscount(12) => 698
    rule #Cbls12g1MsmDiscount(13) => 692
    rule #Cbls12g1MsmDiscount(14) => 687
    rule #Cbls12g1MsmDiscount(15) => 682
    rule #Cbls12g1MsmDiscount(16) => 677
    rule #Cbls12g1MsmDiscount(17) => 673
    rule #Cbls12g1MsmDiscount(18) => 669
    rule #Cbls12g1MsmDiscount(19) => 665
    rule #Cbls12g1MsmDiscount(20) => 661
    rule #Cbls12g1MsmDiscount(21) => 658
    rule #Cbls12g1MsmDiscount(22) => 654
    rule #Cbls12g1MsmDiscount(23) => 651
    rule #Cbls12g1MsmDiscount(24) => 648
    rule #Cbls12g1MsmDiscount(25) => 645
    rule #Cbls12g1MsmDiscount(26) => 642
    rule #Cbls12g1MsmDiscount(27) => 640
    rule #Cbls12g1MsmDiscount(28) => 637
    rule #Cbls12g1MsmDiscount(29) => 635
    rule #Cbls12g1MsmDiscount(30) => 632
    rule #Cbls12g1MsmDiscount(31) => 630
    rule #Cbls12g1MsmDiscount(32) => 627
    rule #Cbls12g1MsmDiscount(33) => 625
    rule #Cbls12g1MsmDiscount(34) => 623
    rule #Cbls12g1MsmDiscount(35) => 621
    rule #Cbls12g1MsmDiscount(36) => 619
    rule #Cbls12g1MsmDiscount(37) => 617
    rule #Cbls12g1MsmDiscount(38) => 615
    rule #Cbls12g1MsmDiscount(39) => 613
    rule #Cbls12g1MsmDiscount(40) => 611
    rule #Cbls12g1MsmDiscount(41) => 609
    rule #Cbls12g1MsmDiscount(42) => 608
    rule #Cbls12g1MsmDiscount(43) => 606
    rule #Cbls12g1MsmDiscount(44) => 604
    rule #Cbls12g1MsmDiscount(45) => 603
    rule #Cbls12g1MsmDiscount(46) => 601
    rule #Cbls12g1MsmDiscount(47) => 599
    rule #Cbls12g1MsmDiscount(48) => 598
    rule #Cbls12g1MsmDiscount(49) => 596
    rule #Cbls12g1MsmDiscount(50) => 595
    rule #Cbls12g1MsmDiscount(51) => 593
    rule #Cbls12g1MsmDiscount(52) => 592
    rule #Cbls12g1MsmDiscount(53) => 591
    rule #Cbls12g1MsmDiscount(54) => 589
    rule #Cbls12g1MsmDiscount(55) => 588
    rule #Cbls12g1MsmDiscount(56) => 586
    rule #Cbls12g1MsmDiscount(57) => 585
    rule #Cbls12g1MsmDiscount(58) => 584
    rule #Cbls12g1MsmDiscount(59) => 582
    rule #Cbls12g1MsmDiscount(60) => 581
    rule #Cbls12g1MsmDiscount(61) => 580
    rule #Cbls12g1MsmDiscount(62) => 579
    rule #Cbls12g1MsmDiscount(63) => 577
    rule #Cbls12g1MsmDiscount(64) => 576
    rule #Cbls12g1MsmDiscount(65) => 575
    rule #Cbls12g1MsmDiscount(66) => 574
    rule #Cbls12g1MsmDiscount(67) => 573
    rule #Cbls12g1MsmDiscount(68) => 572
    rule #Cbls12g1MsmDiscount(69) => 570
    rule #Cbls12g1MsmDiscount(70) => 569
    rule #Cbls12g1MsmDiscount(71) => 568
    rule #Cbls12g1MsmDiscount(72) => 567
    rule #Cbls12g1MsmDiscount(73) => 566
    rule #Cbls12g1MsmDiscount(74) => 565
    rule #Cbls12g1MsmDiscount(75) => 564
    rule #Cbls12g1MsmDiscount(76) => 563
    rule #Cbls12g1MsmDiscount(77) => 562
    rule #Cbls12g1MsmDiscount(78) => 561
    rule #Cbls12g1MsmDiscount(79) => 560
    rule #Cbls12g1MsmDiscount(80) => 559
    rule #Cbls12g1MsmDiscount(81) => 558
    rule #Cbls12g1MsmDiscount(82) => 557
    rule #Cbls12g1MsmDiscount(83) => 556
    rule #Cbls12g1MsmDiscount(84) => 555
    rule #Cbls12g1MsmDiscount(85) => 554
    rule #Cbls12g1MsmDiscount(86) => 553
    rule #Cbls12g1MsmDiscount(87) => 552
    rule #Cbls12g1MsmDiscount(88) => 551
    rule #Cbls12g1MsmDiscount(89) => 550
    rule #Cbls12g1MsmDiscount(90) => 549
    rule #Cbls12g1MsmDiscount(91) => 548
    rule #Cbls12g1MsmDiscount(92) => 547
    rule #Cbls12g1MsmDiscount(93) => 547
    rule #Cbls12g1MsmDiscount(94) => 546
    rule #Cbls12g1MsmDiscount(95) => 545
    rule #Cbls12g1MsmDiscount(96) => 544
    rule #Cbls12g1MsmDiscount(97) => 543
    rule #Cbls12g1MsmDiscount(98) => 542
    rule #Cbls12g1MsmDiscount(99) => 541
    rule #Cbls12g1MsmDiscount(100) => 540
    rule #Cbls12g1MsmDiscount(101) => 540
    rule #Cbls12g1MsmDiscount(102) => 539
    rule #Cbls12g1MsmDiscount(103) => 538
    rule #Cbls12g1MsmDiscount(104) => 537
    rule #Cbls12g1MsmDiscount(105) => 536
    rule #Cbls12g1MsmDiscount(106) => 536
    rule #Cbls12g1MsmDiscount(107) => 535
    rule #Cbls12g1MsmDiscount(108) => 534
    rule #Cbls12g1MsmDiscount(109) => 533
    rule #Cbls12g1MsmDiscount(110) => 532
    rule #Cbls12g1MsmDiscount(111) => 532
    rule #Cbls12g1MsmDiscount(112) => 531
    rule #Cbls12g1MsmDiscount(113) => 530
    rule #Cbls12g1MsmDiscount(114) => 529
    rule #Cbls12g1MsmDiscount(115) => 528
    rule #Cbls12g1MsmDiscount(116) => 528
    rule #Cbls12g1MsmDiscount(117) => 527
    rule #Cbls12g1MsmDiscount(118) => 526
    rule #Cbls12g1MsmDiscount(119) => 525
    rule #Cbls12g1MsmDiscount(120) => 525
    rule #Cbls12g1MsmDiscount(121) => 524
    rule #Cbls12g1MsmDiscount(122) => 523
    rule #Cbls12g1MsmDiscount(123) => 522
    rule #Cbls12g1MsmDiscount(124) => 522
    rule #Cbls12g1MsmDiscount(125) => 521
    rule #Cbls12g1MsmDiscount(126) => 520
    rule #Cbls12g1MsmDiscount(127) => 520
    rule #Cbls12g1MsmDiscount(128) => 519
    rule #Cbls12g1MsmDiscount(N) => 519 requires N >Int 128

    syntax Int ::= #Cbls12g2MsmDiscount( Int ) [function, total]
  // -----------------------------------------------------------
    rule #Cbls12g2MsmDiscount(N) => 1000 requires N <Int 1
    rule #Cbls12g2MsmDiscount(1) => 1000
    rule #Cbls12g2MsmDiscount(2) => 1000
    rule #Cbls12g2MsmDiscount(3) => 923
    rule #Cbls12g2MsmDiscount(4) => 884
    rule #Cbls12g2MsmDiscount(5) => 855
    rule #Cbls12g2MsmDiscount(6) => 832
    rule #Cbls12g2MsmDiscount(7) => 812
    rule #Cbls12g2MsmDiscount(8) => 796
    rule #Cbls12g2MsmDiscount(9) => 782
    rule #Cbls12g2MsmDiscount(10) => 770
    rule #Cbls12g2MsmDiscount(11) => 759
    rule #Cbls12g2MsmDiscount(12) => 749
    rule #Cbls12g2MsmDiscount(13) => 740
    rule #Cbls12g2MsmDiscount(14) => 732
    rule #Cbls12g2MsmDiscount(15) => 724
    rule #Cbls12g2MsmDiscount(16) => 717
    rule #Cbls12g2MsmDiscount(17) => 711
    rule #Cbls12g2MsmDiscount(18) => 704
    rule #Cbls12g2MsmDiscount(19) => 699
    rule #Cbls12g2MsmDiscount(20) => 693
    rule #Cbls12g2MsmDiscount(21) => 688
    rule #Cbls12g2MsmDiscount(22) => 683
    rule #Cbls12g2MsmDiscount(23) => 679
    rule #Cbls12g2MsmDiscount(24) => 674
    rule #Cbls12g2MsmDiscount(25) => 670
    rule #Cbls12g2MsmDiscount(26) => 666
    rule #Cbls12g2MsmDiscount(27) => 663
    rule #Cbls12g2MsmDiscount(28) => 659
    rule #Cbls12g2MsmDiscount(29) => 655
    rule #Cbls12g2MsmDiscount(30) => 652
    rule #Cbls12g2MsmDiscount(31) => 649
    rule #Cbls12g2MsmDiscount(32) => 646
    rule #Cbls12g2MsmDiscount(33) => 643
    rule #Cbls12g2MsmDiscount(34) => 640
    rule #Cbls12g2MsmDiscount(35) => 637
    rule #Cbls12g2MsmDiscount(36) => 634
    rule #Cbls12g2MsmDiscount(37) => 632
    rule #Cbls12g2MsmDiscount(38) => 629
    rule #Cbls12g2MsmDiscount(39) => 627
    rule #Cbls12g2MsmDiscount(40) => 624
    rule #Cbls12g2MsmDiscount(41) => 622
    rule #Cbls12g2MsmDiscount(42) => 620
    rule #Cbls12g2MsmDiscount(43) => 618
    rule #Cbls12g2MsmDiscount(44) => 615
    rule #Cbls12g2MsmDiscount(45) => 613
    rule #Cbls12g2MsmDiscount(46) => 611
    rule #Cbls12g2MsmDiscount(47) => 609
    rule #Cbls12g2MsmDiscount(48) => 607
    rule #Cbls12g2MsmDiscount(49) => 606
    rule #Cbls12g2MsmDiscount(50) => 604
    rule #Cbls12g2MsmDiscount(51) => 602
    rule #Cbls12g2MsmDiscount(52) => 600
    rule #Cbls12g2MsmDiscount(53) => 598
    rule #Cbls12g2MsmDiscount(54) => 597
    rule #Cbls12g2MsmDiscount(55) => 595
    rule #Cbls12g2MsmDiscount(56) => 593
    rule #Cbls12g2MsmDiscount(57) => 592
    rule #Cbls12g2MsmDiscount(58) => 590
    rule #Cbls12g2MsmDiscount(59) => 589
    rule #Cbls12g2MsmDiscount(60) => 587
    rule #Cbls12g2MsmDiscount(61) => 586
    rule #Cbls12g2MsmDiscount(62) => 584
    rule #Cbls12g2MsmDiscount(63) => 583
    rule #Cbls12g2MsmDiscount(64) => 582
    rule #Cbls12g2MsmDiscount(65) => 580
    rule #Cbls12g2MsmDiscount(66) => 579
    rule #Cbls12g2MsmDiscount(67) => 578
    rule #Cbls12g2MsmDiscount(68) => 576
    rule #Cbls12g2MsmDiscount(69) => 575
    rule #Cbls12g2MsmDiscount(70) => 574
    rule #Cbls12g2MsmDiscount(71) => 573
    rule #Cbls12g2MsmDiscount(72) => 571
    rule #Cbls12g2MsmDiscount(73) => 570
    rule #Cbls12g2MsmDiscount(74) => 569
    rule #Cbls12g2MsmDiscount(75) => 568
    rule #Cbls12g2MsmDiscount(76) => 567
    rule #Cbls12g2MsmDiscount(77) => 566
    rule #Cbls12g2MsmDiscount(78) => 565
    rule #Cbls12g2MsmDiscount(79) => 563
    rule #Cbls12g2MsmDiscount(80) => 562
    rule #Cbls12g2MsmDiscount(81) => 561
    rule #Cbls12g2MsmDiscount(82) => 560
    rule #Cbls12g2MsmDiscount(83) => 559
    rule #Cbls12g2MsmDiscount(84) => 558
    rule #Cbls12g2MsmDiscount(85) => 557
    rule #Cbls12g2MsmDiscount(86) => 556
    rule #Cbls12g2MsmDiscount(87) => 555
    rule #Cbls12g2MsmDiscount(88) => 554
    rule #Cbls12g2MsmDiscount(89) => 553
    rule #Cbls12g2MsmDiscount(90) => 552
    rule #Cbls12g2MsmDiscount(91) => 552
    rule #Cbls12g2MsmDiscount(92) => 551
    rule #Cbls12g2MsmDiscount(93) => 550
    rule #Cbls12g2MsmDiscount(94) => 549
    rule #Cbls12g2MsmDiscount(95) => 548
    rule #Cbls12g2MsmDiscount(96) => 547
    rule #Cbls12g2MsmDiscount(97) => 546
    rule #Cbls12g2MsmDiscount(98) => 545
    rule #Cbls12g2MsmDiscount(99) => 545
    rule #Cbls12g2MsmDiscount(100) => 544
    rule #Cbls12g2MsmDiscount(101) => 543
    rule #Cbls12g2MsmDiscount(102) => 542
    rule #Cbls12g2MsmDiscount(103) => 541
    rule #Cbls12g2MsmDiscount(104) => 541
    rule #Cbls12g2MsmDiscount(105) => 540
    rule #Cbls12g2MsmDiscount(106) => 539
    rule #Cbls12g2MsmDiscount(107) => 538
    rule #Cbls12g2MsmDiscount(108) => 537
    rule #Cbls12g2MsmDiscount(109) => 537
    rule #Cbls12g2MsmDiscount(110) => 536
    rule #Cbls12g2MsmDiscount(111) => 535
    rule #Cbls12g2MsmDiscount(112) => 535
    rule #Cbls12g2MsmDiscount(113) => 534
    rule #Cbls12g2MsmDiscount(114) => 533
    rule #Cbls12g2MsmDiscount(115) => 532
    rule #Cbls12g2MsmDiscount(116) => 532
    rule #Cbls12g2MsmDiscount(117) => 531
    rule #Cbls12g2MsmDiscount(118) => 530
    rule #Cbls12g2MsmDiscount(119) => 530
    rule #Cbls12g2MsmDiscount(120) => 529
    rule #Cbls12g2MsmDiscount(121) => 528
    rule #Cbls12g2MsmDiscount(122) => 528
    rule #Cbls12g2MsmDiscount(123) => 527
    rule #Cbls12g2MsmDiscount(124) => 526
    rule #Cbls12g2MsmDiscount(125) => 526
    rule #Cbls12g2MsmDiscount(126) => 525
    rule #Cbls12g2MsmDiscount(127) => 524
    rule #Cbls12g2MsmDiscount(128) => 524
    rule #Cbls12g2MsmDiscount(N) => 524 requires N >Int 128

    syntax Gas ::= #allBut64th ( Gas ) [symbol(#allBut64th_Gas), overload(#allBut64th), function, total, smtlib(gas_allBut64th_Gas)]
    syntax Int ::= #allBut64th ( Int ) [symbol(#allBut64th_Int), overload(#allBut64th), function, total, smtlib(gas_allBut64th_Int)]
 // --------------------------------------------------------------------------------------------------------------------------------
    rule [allBut64th.pos]: #allBut64th(N) => N -Int (N /Int 64) requires 0 <=Int N
    rule [allBut64th.neg]: #allBut64th(N) => 0                  requires N  <Int 0

    syntax Int ::= G0 ( Schedule , Bytes , Bool )           [function, symbol(G0base)]
                 | G0 ( Schedule , Bytes , Int , Int, Int ) [function, symbol(G0data)]
 // ----------------------------------------------------------------------------------
    rule G0(SCHED, WS, false) => G0(SCHED, WS, 0, lengthBytes(WS), 0) +Int Gtransaction < SCHED >
    rule G0(SCHED, WS, true)  => G0(SCHED, WS, 0, lengthBytes(WS), 0) +Int Gtxcreate < SCHED > +Int Cinitcode(SCHED, lengthBytes(WS))

    rule G0(    _,  _, I, I, R) => R
    rule G0(SCHED, WS, I, J, R) => G0(SCHED, WS, I +Int 1, J, R +Int #if WS[I] ==Int 0 #then Gtxdatazero < SCHED > #else Gtxdatanonzero < SCHED > #fi) [owise]

    syntax Gas ::= "G*" "(" Gas "," Int "," Int "," Schedule ")" [function]
 // -----------------------------------------------------------------------
    rule G*(GAVAIL, GLIMIT, REFUND, SCHED) => GAVAIL +Gas minGas((GLIMIT -Gas GAVAIL) /Gas Rmaxquotient < SCHED >, REFUND)

    syntax Int ::= #multComplexity(Int)    [symbol(#multComplexity),    function]
                 | #newMultComplexity(Int) [symbol(#newMultComplexity), function]
 // -----------------------------------------------------------------------------
    rule #multComplexity(X) => X *Int X                                     requires X <=Int 64
    rule #multComplexity(X) => X *Int X /Int 4 +Int 96 *Int X -Int 3072     requires X >Int 64 andBool X <=Int 1024
    rule #multComplexity(X) => X *Int X /Int 16 +Int 480 *Int X -Int 199680 requires X >Int 1024

    rule #newMultComplexity(X) => (X up/Int 8) ^Int 2

    syntax Int ::= #adjustedExpLength(Int, Int, Bytes) [symbol(#adjustedExpLength),    function]
                 | #adjustedExpLength(Int)             [symbol(#adjustedExpLengthAux), function]
 // --------------------------------------------------------------------------------------------
    rule #adjustedExpLength(BASELEN, EXPLEN, DATA) => #if EXPLEN <=Int 32 #then 0 #else 8 *Int (EXPLEN -Int 32) #fi +Int #adjustedExpLength(#asInteger(#range(DATA, 96 +Int BASELEN, minInt(EXPLEN, 32))))

    rule #adjustedExpLength(0) => 0
    rule #adjustedExpLength(1) => 0
    rule #adjustedExpLength(N) => 1 +Int #adjustedExpLength(N /Int 2) requires N >Int 1
endmodule
```

KEVM Gas Simplifications
========================

Here are simplification rules related to gas that the haskell backend uses.

```k
module GAS-SIMPLIFICATION [symbolic]
    imports GAS-SYNTAX
    imports INT
    imports BOOL

    rule A <Gas B => false requires B <=Gas A [simplification]
endmodule
```
