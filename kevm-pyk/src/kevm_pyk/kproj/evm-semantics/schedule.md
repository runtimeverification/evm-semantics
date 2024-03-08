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
                          | "Ghaswarmcoinbase"
 // ------------------------------------------
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
                           | "Gaccessliststoragekey"           | "Rmaxquotient"  | "Ginitcodewordcost" | "maxInitCodeSize"
 // ----------------------------------------------------------------------------------------------------------------------
```

### Frontier Schedule

```k
    syntax Schedule ::= "AFTER_FRONTIER" [macro]
    syntax Schedule ::= "FRONTIER" [klabel(FRONTIER_EVM), symbol, smtlib(schedule_FRONTIER)]
 // ----------------------------------------------------------------------------------------
    rule AFTER_FRONTIER => FRONTIER #Or AFTER_HOMESTEAD

    rule Gzero    < AFTER_FRONTIER > => 0 [priority(200)]
    rule Gbase    < AFTER_FRONTIER > => 2 [priority(200)]
    rule Gverylow < AFTER_FRONTIER > => 3 [priority(200)]
    rule Glow     < AFTER_FRONTIER > => 5 [priority(200)]
    rule Gmid     < AFTER_FRONTIER > => 8 [priority(200)]
    rule Ghigh    < AFTER_FRONTIER > => 10 [priority(200)]

    rule Gexp      < AFTER_FRONTIER > => 10 [priority(200)]
    rule Gexpbyte  < AFTER_FRONTIER > => 10 [priority(200)]
    rule Gsha3     < AFTER_FRONTIER > => 30 [priority(200)]
    rule Gsha3word < AFTER_FRONTIER > => 6 [priority(200)]

    rule Gsload       < AFTER_FRONTIER > => 50 [priority(200)]
    rule Gsstoreset   < AFTER_FRONTIER > => 20000 [priority(200)]
    rule Gsstorereset < AFTER_FRONTIER > => 5000 [priority(200)]
    rule Rsstoreclear < AFTER_FRONTIER > => 15000 [priority(200)]

    rule Glog      < AFTER_FRONTIER > => 375 [priority(200)]
    rule Glogdata  < AFTER_FRONTIER > => 8 [priority(200)]
    rule Glogtopic < AFTER_FRONTIER > => 375 [priority(200)]

    rule Gcall        < AFTER_FRONTIER > => 40 [priority(200)]
    rule Gcallstipend < AFTER_FRONTIER > => 2300 [priority(200)]
    rule Gcallvalue   < AFTER_FRONTIER > => 9000 [priority(200)]
    rule Gnewaccount  < AFTER_FRONTIER > => 25000 [priority(200)]

    rule Gcreate       < AFTER_FRONTIER > => 32000 [priority(200)]
    rule Gcodedeposit  < AFTER_FRONTIER > => 200 [priority(200)]
    rule Gselfdestruct < AFTER_FRONTIER > => 0 [priority(200)]
    rule Rselfdestruct < AFTER_FRONTIER > => 24000 [priority(200)]

    rule Gmemory      < AFTER_FRONTIER > => 3 [priority(200)]
    rule Gquadcoeff   < AFTER_FRONTIER > => 512 [priority(200)]
    rule Gcopy        < AFTER_FRONTIER > => 3 [priority(200)]
    rule Gquaddivisor < AFTER_FRONTIER > => 20 [priority(200)]

    rule Gtransaction   < AFTER_FRONTIER > => 21000 [priority(200)]
    rule Gtxcreate      < AFTER_FRONTIER > => 21000 [priority(200)]
    rule Gtxdatazero    < AFTER_FRONTIER > => 4 [priority(200)]
    rule Gtxdatanonzero < AFTER_FRONTIER > => 68 [priority(200)]

    rule Gjumpdest    < AFTER_FRONTIER > => 1 [priority(200)]
    rule Gbalance     < AFTER_FRONTIER > => 20 [priority(200)]
    rule Gblockhash   < AFTER_FRONTIER > => 20 [priority(200)]
    rule Gextcodesize < AFTER_FRONTIER > => 20 [priority(200)]
    rule Gextcodecopy < AFTER_FRONTIER > => 20 [priority(200)]

    rule Gecadd       < AFTER_FRONTIER > => 500 [priority(200)]
    rule Gecmul       < AFTER_FRONTIER > => 40000 [priority(200)]
    rule Gecpairconst < AFTER_FRONTIER > => 100000 [priority(200)]
    rule Gecpaircoeff < AFTER_FRONTIER > => 80000 [priority(200)]
    rule Gfround      < AFTER_FRONTIER > => 1 [priority(200)]

    rule maxCodeSize < AFTER_FRONTIER > => maxUInt32 [priority(200)]
    rule Rb          < AFTER_FRONTIER > => 5 *Int eth [priority(200)]

    rule Gcoldsload         < AFTER_FRONTIER > => 0 [priority(200)]
    rule Gcoldaccountaccess < AFTER_FRONTIER > => 0 [priority(200)]
    rule Gwarmstorageread   < AFTER_FRONTIER > => 0 [priority(200)]

    rule Gaccessliststoragekey < AFTER_FRONTIER > => 0 [priority(200)]
    rule Gaccesslistaddress    < AFTER_FRONTIER > => 0 [priority(200)]

    rule maxInitCodeSize   < AFTER_FRONTIER > => 0 [priority(200)]
    rule Ginitcodewordcost < AFTER_FRONTIER > => 0 [priority(200)]

    rule Rmaxquotient < AFTER_FRONTIER > => 2 [priority(200)]

    rule Gselfdestructnewaccount << AFTER_FRONTIER >> => false [priority(200)]
    rule Gstaticcalldepth        << AFTER_FRONTIER >> => true [priority(200)]
    rule Gemptyisnonexistent     << AFTER_FRONTIER >> => false [priority(200)]
    rule Gzerovaluenewaccountgas << AFTER_FRONTIER >> => true [priority(200)]
    rule Ghasrevert              << AFTER_FRONTIER >> => false [priority(200)]
    rule Ghasreturndata          << AFTER_FRONTIER >> => false [priority(200)]
    rule Ghasstaticcall          << AFTER_FRONTIER >> => false [priority(200)]
    rule Ghasshift               << AFTER_FRONTIER >> => false [priority(200)]
    rule Ghasdirtysstore         << AFTER_FRONTIER >> => false [priority(200)]
    rule Ghassstorestipend       << AFTER_FRONTIER >> => false [priority(200)]
    rule Ghascreate2             << AFTER_FRONTIER >> => false [priority(200)]
    rule Ghasextcodehash         << AFTER_FRONTIER >> => false [priority(200)]
    rule Ghasselfbalance         << AFTER_FRONTIER >> => false [priority(200)]
    rule Ghaschainid             << AFTER_FRONTIER >> => false [priority(200)]
    rule Ghasaccesslist          << AFTER_FRONTIER >> => false [priority(200)]
    rule Ghasbasefee             << AFTER_FRONTIER >> => false [priority(200)]
    rule Ghasrejectedfirstbyte   << AFTER_FRONTIER >> => false [priority(200)]
    rule Ghasprevrandao          << AFTER_FRONTIER >> => false [priority(200)]
    rule Ghasmaxinitcodesize     << AFTER_FRONTIER >> => false [priority(200)]
    rule Ghaspushzero            << AFTER_FRONTIER >> => false [priority(200)]
    rule Ghaswarmcoinbase        << AFTER_FRONTIER >> => false [priority(200)]
```

### Homestead Schedule

```k
    syntax Schedule ::= "AFTER_HOMESTEAD" [macro]
    syntax Schedule ::= "HOMESTEAD" [klabel(HOMESTEAD_EVM), symbol, smtlib(schedule_HOMESTEAD)]
 // -------------------------------------------------------------------------------------------
    rule AFTER_HOMESTEAD => HOMESTEAD #Or AFTER_TANGERINE_WHISTLE

    rule Gtxcreate  < AFTER_HOMESTEAD > => 53000 [priority(199)]
```

### Tangerine Whistle Schedule

```k
    syntax Schedule ::= "AFTER_TANGERINE_WHISTLE" [macro]
    syntax Schedule ::= "TANGERINE_WHISTLE" [klabel(TANGERINE_WHISTLE_EVM), symbol, smtlib(schedule_TANGERINE_WHISTLE)]
 // -------------------------------------------------------------------------------------------------------------------
    rule AFTER_TANGERINE_WHISTLE => TANGERINE_WHISTLE #Or AFTER_SPURIOUS_DRAGON

    rule Gbalance      < AFTER_TANGERINE_WHISTLE > => 400 [priority(198)]
    rule Gsload        < AFTER_TANGERINE_WHISTLE > => 200 [priority(198)]
    rule Gcall         < AFTER_TANGERINE_WHISTLE > => 700 [priority(198)]
    rule Gselfdestruct < AFTER_TANGERINE_WHISTLE > => 5000 [priority(198)]
    rule Gextcodesize  < AFTER_TANGERINE_WHISTLE > => 700 [priority(198)]
    rule Gextcodecopy  < AFTER_TANGERINE_WHISTLE > => 700 [priority(198)]

    rule Gselfdestructnewaccount << AFTER_TANGERINE_WHISTLE >> => true [priority(198)]
    rule Gstaticcalldepth        << AFTER_TANGERINE_WHISTLE >> => false [priority(198)]
```

### Spurious Dragon Schedule

```k
    syntax Schedule ::= "AFTER_SPURIOUS_DRAGON" [macro]
    syntax Schedule ::= "SPURIOUS_DRAGON" [klabel(SPURIOUS_DRAGON_EVM), symbol, smtlib(schedule_SPURIOUS_DRAGON)]
 // -------------------------------------------------------------------------------------------------------------
    rule AFTER_SPURIOUS_DRAGON => SPURIOUS_DRAGON #Or AFTER_BYZANTIUM

    rule Gexpbyte    < AFTER_SPURIOUS_DRAGON > => 50 [priority(197)]
    rule maxCodeSize < AFTER_SPURIOUS_DRAGON > => 24576 [priority(197)]

    rule Gemptyisnonexistent     << AFTER_SPURIOUS_DRAGON >> => true [priority(197)]
    rule Gzerovaluenewaccountgas << AFTER_SPURIOUS_DRAGON >> => false [priority(197)]
```

### Byzantium Schedule

```k
    syntax Schedule ::= "AFTER_BYZANTIUM" [macro]
    syntax Schedule ::= "BYZANTIUM" [klabel(BYZANTIUM_EVM), symbol, smtlib(schedule_BYZANTIUM)]
 // -------------------------------------------------------------------------------------------
    rule AFTER_BYZANTIUM => BYZANTIUM #Or AFTER_CONSTANTINOPLE

    rule Rb         < AFTER_BYZANTIUM > => 3 *Int eth [priority(196)]

    rule Ghasrevert     << AFTER_BYZANTIUM >> => true [priority(196)]
    rule Ghasreturndata << AFTER_BYZANTIUM >> => true [priority(196)]
    rule Ghasstaticcall << AFTER_BYZANTIUM >> => true [priority(196)]
```

### Constantinople Schedule

```k
    syntax Schedule ::= "AFTER_CONSTANTINOPLE" [macro]
    syntax Schedule ::= "CONSTANTINOPLE" [klabel(CONSTANTINOPLE_EVM), symbol, smtlib(schedule_CONSTANTINOPLE)]
 // ----------------------------------------------------------------------------------------------------------
    rule AFTER_CONSTANTINOPLE => CONSTANTINOPLE #Or AFTER_PETERSBURG

    rule Rb         < AFTER_CONSTANTINOPLE > => 2 *Int eth [priority(195)]

    rule Ghasshift       << AFTER_CONSTANTINOPLE >> => true [priority(195)]
    rule Ghasdirtysstore << AFTER_CONSTANTINOPLE >> => true [priority(195)]
    rule Ghascreate2     << AFTER_CONSTANTINOPLE >> => true [priority(195)]
    rule Ghasextcodehash << AFTER_CONSTANTINOPLE >> => true [priority(195)]
```

### Petersburg Schedule

```k
    syntax Schedule ::= "AFTER_PETERSBURG" [macro]
    syntax Schedule ::= "PETERSBURG" [klabel(PETERSBURG_EVM), symbol, smtlib(schedule_PETERSBURG)]
 // ----------------------------------------------------------------------------------------------
    rule AFTER_PETERSBURG => PETERSBURG #Or AFTER_ISTANBUL

    rule Ghasdirtysstore << AFTER_PETERSBURG >> => false [priority(194)]
```

### Istanbul Schedule

```k
    syntax Schedule ::= "AFTER_ISTANBUL" [macro]
    syntax Schedule ::= "ISTANBUL" [klabel(ISTANBUL_EVM), symbol, smtlib(schedule_ISTANBUL)]
 // ----------------------------------------------------------------------------------------
    rule AFTER_ISTANBUL => ISTANBUL #Or AFTER_BERLIN

    rule Gecadd         < AFTER_ISTANBUL > => 150 [priority(193)]
    rule Gecmul         < AFTER_ISTANBUL > => 6000 [priority(193)]
    rule Gecpairconst   < AFTER_ISTANBUL > => 45000 [priority(193)]
    rule Gecpaircoeff   < AFTER_ISTANBUL > => 34000 [priority(193)]
    rule Gtxdatanonzero < AFTER_ISTANBUL > => 16 [priority(193)]
    rule Gsload         < AFTER_ISTANBUL > => 800 [priority(193)]
    rule Gbalance       < AFTER_ISTANBUL > => 700 [priority(193)]

    rule Ghasselfbalance   << AFTER_ISTANBUL >> => true [priority(193)]
    rule Ghasdirtysstore   << AFTER_ISTANBUL >> => true [priority(193)]
    rule Ghassstorestipend << AFTER_ISTANBUL >> => true [priority(193)]
    rule Ghaschainid       << AFTER_ISTANBUL >> => true [priority(193)]
```

### Berlin Schedule

```k
    syntax Schedule ::= "AFTER_BERLIN" [macro]
    syntax Schedule ::= "BERLIN" [klabel(BERLIN_EVM), symbol, smtlib(schedule_BERLIN)]
 // ----------------------------------------------------------------------------------
    rule AFTER_BERLIN => BERLIN #Or AFTER_LONDON

    rule Gcoldsload            < AFTER_BERLIN > => 2100 [priority(192)]
    rule Gcoldaccountaccess    < AFTER_BERLIN > => 2600 [priority(192)]
    rule Gwarmstorageread      < AFTER_BERLIN > => 100 [priority(192)]
    rule Gsload                < AFTER_BERLIN > => 100 [priority(192)]
    rule Gsstorereset          < AFTER_BERLIN > => 2900 [priority(192)]
    rule Gquaddivisor          < AFTER_BERLIN > => 3 [priority(192)]
    rule Gaccessliststoragekey < AFTER_BERLIN > => 1900 [priority(192)]
    rule Gaccesslistaddress    < AFTER_BERLIN > => 2400 [priority(192)]

    rule Ghasaccesslist << AFTER_BERLIN >> => true [priority(192)]
```

### London Schedule

```k
    syntax Schedule ::= "AFTER_LONDON" [macro]
    syntax Schedule ::= "LONDON" [klabel(LONDON_EVM), symbol, smtlib(schedule_LONDON)]
 // ----------------------------------------------------------------------------------
    rule AFTER_LONDON => LONDON #Or AFTER_MERGE

    rule Rselfdestruct < AFTER_LONDON > => 0 [priority(191)]
    rule Rsstoreclear  < AFTER_LONDON > => 4800 [priority(191)]
    rule Rmaxquotient  < AFTER_LONDON > => 5 [priority(191)]

    rule Ghasbasefee           << AFTER_LONDON >> => true [priority(191)]
    rule Ghasrejectedfirstbyte << AFTER_LONDON >> => true [priority(191)]
```

### Merge Schedule

```k
    syntax Schedule ::= "AFTER_MERGE" [macro]
    syntax Schedule ::= "MERGE" [klabel(MERGE_EVM), symbol, smtlib(schedule_MERGE)]
 // -------------------------------------------------------------------------------
    rule AFTER_MERGE => MERGE #Or AFTER_SHANGHAI

    rule Rb         < AFTER_MERGE > => 0 [priority(190)]

    rule Ghasprevrandao << AFTER_MERGE >> => true [priority(190)]
```

### Shanghai Schedule

```k
    syntax Schedule ::= "AFTER_SHANGHAI" [macro]
    syntax Schedule ::= "SHANGHAI" [klabel(SHANGHAI_EVM), symbol, smtlib(schedule_SHANGHAI)]
 // ----------------------------------------------------------------------------------------
    rule AFTER_SHANGHAI => SHANGHAI

    rule maxInitCodeSize   < AFTER_SHANGHAI > => 49152 [priority(189)]
    rule Ginitcodewordcost < AFTER_SHANGHAI > => 2 [priority(189)]

    rule Ghasmaxinitcodesize << AFTER_SHANGHAI >> => true [priority(189)]
    rule Ghaspushzero        << AFTER_SHANGHAI >> => true [priority(189)]
    rule Ghaswarmcoinbase    << AFTER_SHANGHAI >> => true [priority(189)]
endmodule
```
