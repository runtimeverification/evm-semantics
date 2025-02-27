KEVM Schedules
==============

Fee Schedule
------------

The `Schedule` determines the constants/modes of operation for each hard fork.
There are `ScheduleFlag`s and `ScheduleConstant`s.

-   A `ScheduleFlag` is a boolean value determining whether a certain feature is turned on.
-   A `ScheduleConst` is an `Int` parameter which is used during EVM execution.

### Schedule Flags

A `ScheduleFlag` is a boolean determined by the fee schedule; applying a `ScheduleFlag` to a `Schedule` yields whether the flag is set or not.

```k
requires "data.md"

module SCHEDULE
    imports EVM-DATA

    syntax Bool ::= ScheduleFlag "<<" Schedule ">>" [function, total]
 // -----------------------------------------------------------------

    syntax ScheduleFlag ::= "Gselfdestructnewaccount" | "Gstaticcalldepth" | "Gemptyisnonexistent" | "Gzerovaluenewaccountgas"
                          | "Ghasrevert"              | "Ghasreturndata"   | "Ghasstaticcall"      | "Ghasshift"
                          | "Ghasdirtysstore"         | "Ghascreate2"      | "Ghasextcodehash"     | "Ghasselfbalance"
                          | "Ghassstorestipend"       | "Ghaschainid"      | "Ghasaccesslist"      | "Ghasbasefee"
                          | "Ghasrejectedfirstbyte"   | "Ghasprevrandao"   | "Ghasmaxinitcodesize" | "Ghaspushzero"
                          | "Ghaswarmcoinbase"        | "Ghaswithdrawals"  | "Ghastransient"       | "Ghasmcopy"
                          | "Ghasbeaconroot"          | "Ghaseip6780"      | "Ghasblobbasefee"     | "Ghasblobhash"
```

### Schedule Constants

A `ScheduleConst` is a constant determined by the fee schedule.

```k
    syntax Int ::= ScheduleConst "<" Schedule ">" [function, total]
 // ---------------------------------------------------------------

    syntax ScheduleConst ::= "Gzero"         | "Gbase"         | "Gverylow"      | "Glow"              | "Gmid"               | "Ghigh"            | "Gextcodesize"
                           | "Gextcodecopy"  | "Gbalance"      | "Gsload"        | "Gjumpdest"         | "Gsstoreset"         | "Gsstorereset"     | "Rsstoreclear"
                           | "Rselfdestruct" | "Gselfdestruct" | "Gcreate"       | "Gcodedeposit"      | "Gcall"              | "Gcallvalue"       | "Gcallstipend"
                           | "Gnewaccount"   | "Gexp"          | "Gexpbyte"      | "Gmemory"           | "Gtxcreate"          | "Gtxdatazero"      | "Gtxdatanonzero"
                           | "Gtransaction"  | "Glog"          | "Glogdata"      | "Glogtopic"         | "Gsha3"              | "Gsha3word"        | "Gcopy"
                           | "Gblockhash"    | "Gquadcoeff"    | "maxCodeSize"   | "Rb"                | "Gquaddivisor"       | "Gecadd"           | "Gecmul"
                           | "Gecpairconst"  | "Gecpaircoeff"  | "Gfround"       | "Gcoldsload"        | "Gcoldaccountaccess" | "Gwarmstorageread" | "Gaccesslistaddress"
                           | "Gaccessliststoragekey"           | "Rmaxquotient"  | "Ginitcodewordcost" | "maxInitCodeSize"    | "Gwarmstoragedirtystore"
                           | "Gpointeval"
 // ----------------------------------------------------------------------------------------------------------------------------------------------------
```

### Default Schedule

```k
    syntax Schedule ::= "DEFAULT" [symbol(DEFAULT_EVM), smtlib(schedule_DEFAULT)]
 // -----------------------------------------------------------------------------
    rule [GzeroDefault]:    Gzero    < DEFAULT > => 0
    rule [GbaseDefault]:    Gbase    < DEFAULT > => 2
    rule [GverylowDefault]: Gverylow < DEFAULT > => 3
    rule [GlowDefault]:     Glow     < DEFAULT > => 5
    rule [GmidDefault]:     Gmid     < DEFAULT > => 8
    rule [GhighDefault]:    Ghigh    < DEFAULT > => 10

    rule [GexpDefault]:      Gexp      < DEFAULT > => 10
    rule [GexpbyteDefault]:  Gexpbyte  < DEFAULT > => 10
    rule [Gsha3Default]:     Gsha3     < DEFAULT > => 30
    rule [Gsha3wordDefault]: Gsha3word < DEFAULT > => 6

    rule [GsloadDefault]:       Gsload       < DEFAULT > => 50
    rule [GsstoresetDefault]:   Gsstoreset   < DEFAULT > => 20000
    rule [GsstoreresetDefault]: Gsstorereset < DEFAULT > => 5000
    rule [RsstoreclearDefault]: Rsstoreclear < DEFAULT > => 15000

    rule [GlogDefault]:      Glog      < DEFAULT > => 375
    rule [GlogdataDefault]:  Glogdata  < DEFAULT > => 8
    rule [GlogtopicDefault]: Glogtopic < DEFAULT > => 375

    rule [GcallDefault]:        Gcall        < DEFAULT > => 40
    rule [GcallstipendDefault]: Gcallstipend < DEFAULT > => 2300
    rule [GcallvalueDefault]:   Gcallvalue   < DEFAULT > => 9000
    rule [GnewaccountDefault]:  Gnewaccount  < DEFAULT > => 25000

    rule [GcreateDefault]:       Gcreate       < DEFAULT > => 32000
    rule [GcodedepositDefault]:  Gcodedeposit  < DEFAULT > => 200
    rule [GselfdestructDefault]: Gselfdestruct < DEFAULT > => 0
    rule [RselfdestructDefault]: Rselfdestruct < DEFAULT > => 24000

    rule [GmemoryDefault]:      Gmemory      < DEFAULT > => 3
    rule [GquadcoeffDefault]:   Gquadcoeff   < DEFAULT > => 512
    rule [GcopyDefault]:        Gcopy        < DEFAULT > => 3
    rule [GquaddivisorDefault]: Gquaddivisor < DEFAULT > => 20

    rule [GtransactionDefault]:   Gtransaction   < DEFAULT > => 21000
    rule [GtxcreateDefault]:      Gtxcreate      < DEFAULT > => 53000
    rule [GtxdatazeroDefault]:    Gtxdatazero    < DEFAULT > => 4
    rule [GtxdatanonzeroDefault]: Gtxdatanonzero < DEFAULT > => 68

    rule [GjumpdestDefault]:    Gjumpdest    < DEFAULT > => 1
    rule [GbalanceDefault]:     Gbalance     < DEFAULT > => 20
    rule [GblockhashDefault]:   Gblockhash   < DEFAULT > => 20
    rule [GextcodesizeDefault]: Gextcodesize < DEFAULT > => 20
    rule [GextcodecopyDefault]: Gextcodecopy < DEFAULT > => 20

    rule [GecaddDefault]:       Gecadd       < DEFAULT > => 500
    rule [GecmulDefault]:       Gecmul       < DEFAULT > => 40000
    rule [GecpairconstDefault]: Gecpairconst < DEFAULT > => 100000
    rule [GecpaircoeffDefault]: Gecpaircoeff < DEFAULT > => 80000
    rule [GfroundDefault]:      Gfround      < DEFAULT > => 1

    rule [maxCodeSizeDefault]: maxCodeSize < DEFAULT > => 2 ^Int 32 -Int 1
    rule [RbDefault]:          Rb          < DEFAULT > => 5 *Int (10 ^Int 18)

    rule [GcoldsloadDefault]:             Gcoldsload             < DEFAULT > => 0
    rule [GcoldaccountaccessDefault]:     Gcoldaccountaccess     < DEFAULT > => 0
    rule [GwarmstoragereadDefault]:       Gwarmstorageread       < DEFAULT > => 0
    rule [GwarmstoragedirtystoreDefault]: Gwarmstoragedirtystore < DEFAULT > => 0

    rule [GpointevalDefault]: Gpointeval < DEFAULT > => 0

    rule [GaccessliststoragekeyDefault]: Gaccessliststoragekey < DEFAULT > => 0
    rule [GaccesslistaddressDefault]:    Gaccesslistaddress    < DEFAULT > => 0

    rule [maxInitCodeSizeDefault]:   maxInitCodeSize   < DEFAULT > => 0
    rule [GinitcodewordcostDefault]: Ginitcodewordcost < DEFAULT > => 0

    rule [RmaxquotientDefault]: Rmaxquotient < DEFAULT > => 2

    rule [GselfdestructnewaccountDefault]: Gselfdestructnewaccount << DEFAULT >> => false
    rule [GstaticcalldepthDefault]:        Gstaticcalldepth        << DEFAULT >> => true
    rule [GemptyisnonexistentDefault]:     Gemptyisnonexistent     << DEFAULT >> => false
    rule [GzerovaluenewaccountgasDefault]: Gzerovaluenewaccountgas << DEFAULT >> => true
    rule [GhasrevertDefault]:              Ghasrevert              << DEFAULT >> => false
    rule [GhasreturndataDefault]:          Ghasreturndata          << DEFAULT >> => false
    rule [GhasstaticcallDefault]:          Ghasstaticcall          << DEFAULT >> => false
    rule [GhasshiftDefault]:               Ghasshift               << DEFAULT >> => false
    rule [GhasdirtysstoreDefault]:         Ghasdirtysstore         << DEFAULT >> => false
    rule [GhassstorestipendDefault]:       Ghassstorestipend       << DEFAULT >> => false
    rule [Ghascreate2Default]:             Ghascreate2             << DEFAULT >> => false
    rule [GhasextcodehashDefault]:         Ghasextcodehash         << DEFAULT >> => false
    rule [GhasselfbalanceDefault]:         Ghasselfbalance         << DEFAULT >> => false
    rule [GhaschainidDefault]:             Ghaschainid             << DEFAULT >> => false
    rule [GhasaccesslistDefault]:          Ghasaccesslist          << DEFAULT >> => false
    rule [GhasbasefeeDefault]:             Ghasbasefee             << DEFAULT >> => false
    rule [GhasblobbasefeeDefault]:         Ghasblobbasefee         << DEFAULT >> => false
    rule [GhasrejectedfirstbyteDefault]:   Ghasrejectedfirstbyte   << DEFAULT >> => false
    rule [GhasprevrandaoDefault]:          Ghasprevrandao          << DEFAULT >> => false
    rule [GhasmaxinitcodesizeDefault]:     Ghasmaxinitcodesize     << DEFAULT >> => false
    rule [GhaspushzeroDefault]:            Ghaspushzero            << DEFAULT >> => false
    rule [GhaswarmcoinbaseDefault]:        Ghaswarmcoinbase        << DEFAULT >> => false
    rule [GhaswithdrawalsDefault]:         Ghaswithdrawals         << DEFAULT >> => false
    rule [GhastransientDefault]:           Ghastransient           << DEFAULT >> => false
    rule [GhasmcopyDefault]:               Ghasmcopy               << DEFAULT >> => false
    rule [GhasbeaconrootDefault]:          Ghasbeaconroot          << DEFAULT >> => false
    rule [Ghaseip6780Default]:             Ghaseip6780             << DEFAULT >> => false
    rule [GhasblobhashDefault]:            Ghasblobhash            << DEFAULT >> => false
```

### Frontier Schedule

```k
    syntax Schedule ::= "FRONTIER" [symbol(FRONTIER_EVM), smtlib(schedule_FRONTIER)]
 // --------------------------------------------------------------------------------
    rule [GtxcreateFrontier]:  Gtxcreate  < FRONTIER > => 21000
    rule [SCHEDCONSTFrontier]: SCHEDCONST < FRONTIER > => SCHEDCONST < DEFAULT > requires SCHEDCONST =/=K Gtxcreate

    rule [SCHEDFLAGFrontier]: SCHEDFLAG << FRONTIER >> => SCHEDFLAG << DEFAULT >>
```

### Homestead Schedule

```k
    syntax Schedule ::= "HOMESTEAD" [symbol(HOMESTEAD_EVM), smtlib(schedule_HOMESTEAD)]
 // -----------------------------------------------------------------------------------
    rule [SCHEDCONSTHomestead]: SCHEDCONST < HOMESTEAD > => SCHEDCONST < DEFAULT >

    rule [SCHEDFLAGHomestead]: SCHEDFLAG << HOMESTEAD >> => SCHEDFLAG << DEFAULT >>
```

### Tangerine Whistle Schedule

```k
    syntax Schedule ::= "TANGERINE_WHISTLE" [symbol(TANGERINE_WHISTLE_EVM), smtlib(schedule_TANGERINE_WHISTLE)]
 // -----------------------------------------------------------------------------------------------------------
    rule [GbalanceTangerine]:      Gbalance      < TANGERINE_WHISTLE > => 400
    rule [GsloadTangerine]:        Gsload        < TANGERINE_WHISTLE > => 200
    rule [GcallTangerine]:         Gcall         < TANGERINE_WHISTLE > => 700
    rule [GselfdestructTangerine]: Gselfdestruct < TANGERINE_WHISTLE > => 5000
    rule [GextcodesizeTangerine]:  Gextcodesize  < TANGERINE_WHISTLE > => 700
    rule [GextcodecopyTangerine]:  Gextcodecopy  < TANGERINE_WHISTLE > => 700

    rule [SCHEDCONSTTangerine]: SCHEDCONST    < TANGERINE_WHISTLE > => SCHEDCONST < HOMESTEAD >
      requires notBool ( SCHEDCONST ==K Gbalance      orBool SCHEDCONST ==K Gsload       orBool SCHEDCONST ==K Gcall
                  orBool SCHEDCONST ==K Gselfdestruct orBool SCHEDCONST ==K Gextcodesize orBool SCHEDCONST ==K Gextcodecopy
                       )

    rule [GselfdestructnewaccountTangerine]:   Gselfdestructnewaccount << TANGERINE_WHISTLE >> => true
    rule [GstaticcalldepthTangerine]:          Gstaticcalldepth        << TANGERINE_WHISTLE >> => false
    rule [SCHEDFLAGTangerine]:                 SCHEDFLAG               << TANGERINE_WHISTLE >> => SCHEDFLAG << HOMESTEAD >>
      requires notBool ( SCHEDCONST ==K Gselfdestructnewaccount orBool SCHEDCONST ==K Gstaticcalldepth )
```

### Spurious Dragon Schedule

```k
    syntax Schedule ::= "SPURIOUS_DRAGON" [symbol(SPURIOUS_DRAGON_EVM), smtlib(schedule_SPURIOUS_DRAGON)]
 // -----------------------------------------------------------------------------------------------------
    rule [GexpbyteDragon]:    Gexpbyte    < SPURIOUS_DRAGON > => 50
    rule [maxCodeSizeDragon]: maxCodeSize < SPURIOUS_DRAGON > => 24576

    rule [SCHEDCONSTDragon]: SCHEDCONST  < SPURIOUS_DRAGON > => SCHEDCONST < TANGERINE_WHISTLE >
      requires SCHEDCONST =/=K Gexpbyte andBool SCHEDCONST =/=K maxCodeSize

    rule [GemptyisnonexistentDragon]:     Gemptyisnonexistent     << SPURIOUS_DRAGON >> => true
    rule [GzerovaluenewaccountgasDragon]: Gzerovaluenewaccountgas << SPURIOUS_DRAGON >> => false
    rule [SCHEDFLAGDragon]:               SCHEDFLAG               << SPURIOUS_DRAGON >> => SCHEDFLAG << TANGERINE_WHISTLE >>
      requires notBool ( SCHEDCONST ==K Gemptyisnonexistent orBool SCHEDCONST ==K Gzerovaluenewaccountgas )
```

### Byzantium Schedule

```k
    syntax Schedule ::= "BYZANTIUM" [symbol(BYZANTIUM_EVM), smtlib(schedule_BYZANTIUM)]
 // -----------------------------------------------------------------------------------
    rule [RbByzantium]:         Rb         < BYZANTIUM > => 3 *Int eth
    rule [SCHEDCONSTByzantium]: SCHEDCONST < BYZANTIUM > => SCHEDCONST < SPURIOUS_DRAGON >
      requires notBool ( SCHEDCONST ==K Rb )

    rule [GhasrevertByzantium]:     Ghasrevert     << BYZANTIUM >> => true
    rule [GhasreturndataByzantium]: Ghasreturndata << BYZANTIUM >> => true
    rule [GhasstaticcallByzantium]: Ghasstaticcall << BYZANTIUM >> => true
    rule [SCHEDFLAGByzantium]:      SCHEDFLAG      << BYZANTIUM >> => SCHEDFLAG << SPURIOUS_DRAGON >>
      requires notBool ( SCHEDFLAG ==K Ghasrevert orBool SCHEDFLAG ==K Ghasreturndata orBool SCHEDFLAG ==K Ghasstaticcall )
```

### Constantinople Schedule

```k
    syntax Schedule ::= "CONSTANTINOPLE" [symbol(CONSTANTINOPLE_EVM), smtlib(schedule_CONSTANTINOPLE)]
 // --------------------------------------------------------------------------------------------------
    rule [RbConstantinople]:         Rb         < CONSTANTINOPLE > => 2 *Int eth
    rule [SCHEDCONSTConstantinople]: SCHEDCONST < CONSTANTINOPLE > => SCHEDCONST < BYZANTIUM >
      requires notBool ( SCHEDCONST ==K Rb )

    rule [GhasshiftConstantinople]:       Ghasshift       << CONSTANTINOPLE >> => true
    rule [GhasdirtysstoreConstantinople]: Ghasdirtysstore << CONSTANTINOPLE >> => true
    rule [Ghascreate2Constantinople]:     Ghascreate2     << CONSTANTINOPLE >> => true
    rule [GhasextcodehashConstantinople]: Ghasextcodehash << CONSTANTINOPLE >> => true
    rule [SCHEDFLAGConstantinople]:       SCHEDFLAG       << CONSTANTINOPLE >> => SCHEDFLAG << BYZANTIUM >>
      requires notBool ( SCHEDFLAG ==K Ghasshift orBool SCHEDFLAG ==K Ghasdirtysstore orBool SCHEDFLAG ==K Ghascreate2 orBool SCHEDFLAG ==K Ghasextcodehash )
```

### Petersburg Schedule

```k
    syntax Schedule ::= "PETERSBURG" [symbol(PETERSBURG_EVM), smtlib(schedule_PETERSBURG)]
 // --------------------------------------------------------------------------------------
    rule [SCHEDCONSTPetersburg]: SCHEDCONST < PETERSBURG > => SCHEDCONST < CONSTANTINOPLE >

    rule [GhasdirtysstorePetersburg]: Ghasdirtysstore << PETERSBURG >> => false
    rule [SCHEDFLAGPetersburg]:       SCHEDFLAG       << PETERSBURG >> => SCHEDFLAG << CONSTANTINOPLE >>
      requires notBool ( SCHEDFLAG ==K Ghasdirtysstore )
```

### Istanbul Schedule

```k
    syntax Schedule ::= "ISTANBUL" [symbol(ISTANBUL_EVM), smtlib(schedule_ISTANBUL)]
 // --------------------------------------------------------------------------------
    rule [GecaddIstanbul]:         Gecadd         < ISTANBUL > => 150
    rule [GecmulIstanbul]:         Gecmul         < ISTANBUL > => 6000
    rule [GecpairconstIstanbul]:   Gecpairconst   < ISTANBUL > => 45000
    rule [GecpaircoeffIstanbul]:   Gecpaircoeff   < ISTANBUL > => 34000
    rule [GtxdatanonzeroIstanbul]: Gtxdatanonzero < ISTANBUL > => 16
    rule [GsloadIstanbul]:         Gsload         < ISTANBUL > => 800
    rule [GbalanceIstanbul]:       Gbalance       < ISTANBUL > => 700
    rule [SCHEDCONSTIstanbul]:     SCHEDCONST     < ISTANBUL > => SCHEDCONST < PETERSBURG >
      requires notBool ( SCHEDCONST ==K Gecadd
                  orBool SCHEDCONST ==K Gecmul
                  orBool SCHEDCONST ==K Gecpairconst
                  orBool SCHEDCONST ==K Gecpaircoeff
                  orBool SCHEDCONST ==K Gtxdatanonzero
                  orBool SCHEDCONST ==K Gsload
                  orBool SCHEDCONST ==K Gbalance
                       )

    rule [GhasselfbalanceIstanbul]:   Ghasselfbalance   << ISTANBUL >> => true
    rule [GhasdirtysstoreIstanbul]:   Ghasdirtysstore   << ISTANBUL >> => true
    rule [GhassstorestipendIstanbul]: Ghassstorestipend << ISTANBUL >> => true
    rule [GhaschainidIstanbul]:       Ghaschainid       << ISTANBUL >> => true
    rule [SCHEDFLAGIstanbul]:         SCHEDFLAG         << ISTANBUL >> => SCHEDFLAG << PETERSBURG >>
      requires notBool ( SCHEDFLAG ==K Ghasselfbalance
                  orBool SCHEDFLAG ==K Ghasdirtysstore
                  orBool SCHEDFLAG ==K Ghassstorestipend
                  orBool SCHEDFLAG ==K Ghaschainid
                       )
```

### Berlin Schedule

```k
    syntax Schedule ::= "BERLIN" [symbol(BERLIN_EVM), smtlib(schedule_BERLIN)]
 // --------------------------------------------------------------------------
    rule [GcoldsloadBerlin]:            Gcoldsload            < BERLIN > => 2100
    rule [GcoldaccountaccessBerlin]:    Gcoldaccountaccess    < BERLIN > => 2600
    rule [GwarmstoragereadBerlin]:      Gwarmstorageread      < BERLIN > => 100
    rule [GsloadBerlin]:                Gsload                < BERLIN > => Gwarmstorageread < BERLIN >
    rule [GsstoreresetBerlin]:          Gsstorereset          < BERLIN > => 5000 -Int Gcoldsload < BERLIN >
    rule [GquaddivisorBerlin]:          Gquaddivisor          < BERLIN > => 3
    rule [GaccessliststoragekeyBerlin]: Gaccessliststoragekey < BERLIN > => 1900
    rule [GaccesslistaddressBerlin]:    Gaccesslistaddress    < BERLIN > => 2400

    rule [SCHEDCONSTBerlin]: SCHEDCONST < BERLIN > => SCHEDCONST < ISTANBUL >
      requires notBool ( SCHEDCONST ==K Gcoldsload
                  orBool SCHEDCONST ==K Gcoldaccountaccess
                  orBool SCHEDCONST ==K Gwarmstorageread
                  orBool SCHEDCONST ==K Gsload
                  orBool SCHEDCONST ==K Gsstorereset
                  orBool SCHEDCONST ==K Gquaddivisor
                  orBool SCHEDCONST ==K Gaccessliststoragekey
                  orBool SCHEDCONST ==K Gaccesslistaddress
                       )

    rule [hasaccesslistBerlin]: Ghasaccesslist << BERLIN >> => true
    rule [SCHEDFLAGBerlin]:     SCHEDFLAG      << BERLIN >> => SCHEDFLAG << ISTANBUL >>
      requires notBool ( SCHEDFLAG ==K Ghasaccesslist )
```

### London Schedule

```k
    syntax Schedule ::= "LONDON" [symbol(LONDON_EVM), smtlib(schedule_LONDON)]
 // --------------------------------------------------------------------------
    rule [RselfdestructLondon]: Rselfdestruct < LONDON > => 0
    rule [RsstoreclearLondon]:  Rsstoreclear  < LONDON > => Gsstorereset < LONDON > +Int Gaccessliststoragekey < LONDON >
    rule [RmaxquotientLondon]:  Rmaxquotient  < LONDON > => 5
    rule [SCHEDCONSTLondon]:    SCHEDCONST    < LONDON > => SCHEDCONST < BERLIN >
      requires notBool ( SCHEDCONST ==K Rselfdestruct
                  orBool SCHEDCONST ==K Rsstoreclear
                  orBool SCHEDCONST ==K Rmaxquotient
                       )

    rule [GhasbasefeeLondon]:           Ghasbasefee           << LONDON >> => true
    rule [GhasrejectedfirstbyteLondon]: Ghasrejectedfirstbyte << LONDON >> => true
    rule [SCHEDFLAGLondon]:             SCHEDFLAG             << LONDON >> => SCHEDFLAG << BERLIN >>
      requires notBool ( SCHEDFLAG ==K Ghasbasefee
                  orBool SCHEDFLAG ==K Ghasrejectedfirstbyte
                       )
```

### Merge Schedule

```k
    syntax Schedule ::= "MERGE" [symbol(MERGE_EVM), smtlib(schedule_MERGE)]
 // -----------------------------------------------------------------------
    rule [RbMerge]:         Rb         < MERGE > => 0
    rule [SCHEDCONSTMerge]: SCHEDCONST < MERGE > => SCHEDCONST < LONDON >
      requires notBool SCHEDCONST ==K Rb

    rule [GhasprevrandaoMerge]: Ghasprevrandao << MERGE >> => true
    rule [SCHEDFLAGMerge]:      SCHEDFLAG      << MERGE >> => SCHEDFLAG << LONDON >>
      requires notBool SCHEDFLAG ==K Ghasprevrandao
```

### Shanghai Schedule

```k
    syntax Schedule ::= "SHANGHAI" [symbol(SHANGHAI_EVM), smtlib(schedule_SHANGHAI)]
 // --------------------------------------------------------------------------------
    rule [maxInitCodeSizeShanghai]:   maxInitCodeSize   < SHANGHAI > => 2 *Int maxCodeSize < SHANGHAI >
    rule [GinitcodewordcostShanghai]: Ginitcodewordcost < SHANGHAI > => 2
    rule [SCHEDCONSTShanghai]:        SCHEDCONST        < SHANGHAI > => SCHEDCONST < MERGE >
      requires notBool ( SCHEDCONST ==K maxInitCodeSize
                  orBool SCHEDCONST ==K Ginitcodewordcost
                       )

    rule [GhasmaxinitcodesizeShanghai]: Ghasmaxinitcodesize << SHANGHAI >> => true
    rule [GhaspushzeroShanghai]:        Ghaspushzero        << SHANGHAI >> => true
    rule [GhaswarmcoinbaseShanghai]:    Ghaswarmcoinbase    << SHANGHAI >> => true
    rule [GhaswithdrawalsShanghai]:     Ghaswithdrawals     << SHANGHAI >> => true
    rule [SCHEDFLAGShanghai]:           SCHEDFLAG           << SHANGHAI >> => SCHEDFLAG << MERGE >>
      requires notBool ( SCHEDFLAG ==K Ghasmaxinitcodesize
                  orBool SCHEDFLAG ==K Ghaspushzero
                  orBool SCHEDFLAG ==K Ghaswarmcoinbase
                  orBool SCHEDFLAG ==K Ghaswithdrawals
                       )
```

### Cancun Schedule

```k
    syntax Schedule ::= "CANCUN" [symbol(CANCUN_EVM), smtlib(schedule_CANCUN)]
 // --------------------------------------------------------------------------
    rule [GwarmstoragedirtystoreCancun]: Gwarmstoragedirtystore < CANCUN > => Gwarmstorageread < CANCUN >
    rule [GpointevalCancun]:             Gpointeval             < CANCUN > => 50000
    rule [SCHEDCONSTCancun]:             SCHEDCONST             < CANCUN > => SCHEDCONST < SHANGHAI >
      requires notBool ( SCHEDCONST ==K Gwarmstoragedirtystore
                  orBool SCHEDCONST ==K Gpointeval
                       )

    rule [GhastransientCancun]:   Ghastransient   << CANCUN >> => true
    rule [GhasmcopyCancun]:       Ghasmcopy       << CANCUN >> => true
    rule [GhasbeaconrootCancun]:  Ghasbeaconroot  << CANCUN >> => true
    rule [Ghaseip6780Cancun]:     Ghaseip6780     << CANCUN >> => true
    rule [GhasblobbasefeeCancun]: Ghasblobbasefee << CANCUN >> => true
    rule [GhasblobhashCancun]:    Ghasblobhash    << CANCUN >> => true
    rule [SCHEDFLAGCancun]:       SCHEDFLAG       << CANCUN >> => SCHEDFLAG << SHANGHAI >>
      requires notBool ( SCHEDFLAG ==K Ghastransient
                  orBool SCHEDFLAG ==K Ghasmcopy
                  orBool SCHEDFLAG ==K Ghasbeaconroot
                  orBool SCHEDFLAG ==K Ghaseip6780
                  orBool SCHEDFLAG ==K Ghasblobbasefee
                  orBool SCHEDFLAG ==K Ghasblobhash
                       )
```
```k
endmodule
```
