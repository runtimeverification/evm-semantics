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
                          | "Ghaswarmcoinbase"        | "Ghastransient"    | "Ghasmcopy"           | "Ghasbeaconroot"
 // -----------------------------------------------------------------------------------------------------------------
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
 // ----------------------------------------------------------------------------------------------------------------------------------------------------
```

### Frontier Schedule

```k
    syntax Schedule ::= "FRONTIER" [symbol(FRONTIER_EVM), smtlib(schedule_FRONTIER)]
 // --------------------------------------------------------------------------------
    rule Gzero    < FRONTIER > => 0
    rule Gbase    < FRONTIER > => 2
    rule Gverylow < FRONTIER > => 3
    rule Glow     < FRONTIER > => 5
    rule Gmid     < FRONTIER > => 8
    rule Ghigh    < FRONTIER > => 10

    rule Gexp      < FRONTIER > => 10
    rule Gexpbyte  < FRONTIER > => 10
    rule Gsha3     < FRONTIER > => 30
    rule Gsha3word < FRONTIER > => 6

    rule Gsload       < FRONTIER > => 50
    rule Gsstoreset   < FRONTIER > => 20000
    rule Gsstorereset < FRONTIER > => 5000
    rule Rsstoreclear < FRONTIER > => 15000

    rule Glog      < FRONTIER > => 375
    rule Glogdata  < FRONTIER > => 8
    rule Glogtopic < FRONTIER > => 375

    rule Gcall        < FRONTIER > => 40
    rule Gcallstipend < FRONTIER > => 2300
    rule Gcallvalue   < FRONTIER > => 9000
    rule Gnewaccount  < FRONTIER > => 25000

    rule Gcreate       < FRONTIER > => 32000
    rule Gcodedeposit  < FRONTIER > => 200
    rule Gselfdestruct < FRONTIER > => 0
    rule Rselfdestruct < FRONTIER > => 24000

    rule Gmemory      < FRONTIER > => 3
    rule Gquadcoeff   < FRONTIER > => 512
    rule Gcopy        < FRONTIER > => 3
    rule Gquaddivisor < FRONTIER > => 20

    rule Gtransaction   < FRONTIER > => 21000
    rule Gtxcreate      < FRONTIER > => 21000
    rule Gtxdatazero    < FRONTIER > => 4
    rule Gtxdatanonzero < FRONTIER > => 68

    rule Gjumpdest    < FRONTIER > => 1
    rule Gbalance     < FRONTIER > => 20
    rule Gblockhash   < FRONTIER > => 20
    rule Gextcodesize < FRONTIER > => 20
    rule Gextcodecopy < FRONTIER > => 20

    rule Gecadd       < FRONTIER > => 500
    rule Gecmul       < FRONTIER > => 40000
    rule Gecpairconst < FRONTIER > => 100000
    rule Gecpaircoeff < FRONTIER > => 80000
    rule Gfround      < FRONTIER > => 1

    rule maxCodeSize < FRONTIER > => 2 ^Int 32 -Int 1
    rule Rb          < FRONTIER > => 5 *Int eth

    rule Gcoldsload             < FRONTIER > => 0
    rule Gcoldaccountaccess     < FRONTIER > => 0
    rule Gwarmstorageread       < FRONTIER > => 0
    rule Gwarmstoragedirtystore < FRONTIER > => 0

    rule Gaccessliststoragekey < FRONTIER > => 0
    rule Gaccesslistaddress    < FRONTIER > => 0

    rule maxInitCodeSize   < FRONTIER > => 0
    rule Ginitcodewordcost < FRONTIER > => 0

    rule Rmaxquotient < FRONTIER > => 2

    rule Gselfdestructnewaccount << FRONTIER >> => false
    rule Gstaticcalldepth        << FRONTIER >> => true
    rule Gemptyisnonexistent     << FRONTIER >> => false
    rule Gzerovaluenewaccountgas << FRONTIER >> => true
    rule Ghasrevert              << FRONTIER >> => false
    rule Ghasreturndata          << FRONTIER >> => false
    rule Ghasstaticcall          << FRONTIER >> => false
    rule Ghasshift               << FRONTIER >> => false
    rule Ghasdirtysstore         << FRONTIER >> => false
    rule Ghassstorestipend       << FRONTIER >> => false
    rule Ghascreate2             << FRONTIER >> => false
    rule Ghasextcodehash         << FRONTIER >> => false
    rule Ghasselfbalance         << FRONTIER >> => false
    rule Ghaschainid             << FRONTIER >> => false
    rule Ghasaccesslist          << FRONTIER >> => false
    rule Ghasbasefee             << FRONTIER >> => false
    rule Ghasrejectedfirstbyte   << FRONTIER >> => false
    rule Ghasprevrandao          << FRONTIER >> => false
    rule Ghasmaxinitcodesize     << FRONTIER >> => false
    rule Ghaspushzero            << FRONTIER >> => false
    rule Ghaswarmcoinbase        << FRONTIER >> => false
    rule Ghastransient           << FRONTIER >> => false
    rule Ghasmcopy               << FRONTIER >> => false
    rule Ghasbeaconroot          << FRONTIER >> => false
```

### Homestead Schedule

```k
    syntax Schedule ::= "HOMESTEAD" [symbol(HOMESTEAD_EVM), smtlib(schedule_HOMESTEAD)]
 // -----------------------------------------------------------------------------------
    rule Gzero    < HOMESTEAD > => 0
    rule Gbase    < HOMESTEAD > => 2
    rule Gverylow < HOMESTEAD > => 3
    rule Glow     < HOMESTEAD > => 5
    rule Gmid     < HOMESTEAD > => 8
    rule Ghigh    < HOMESTEAD > => 10

    rule Gexp      < HOMESTEAD > => 10
    rule Gexpbyte  < HOMESTEAD > => 10
    rule Gsha3     < HOMESTEAD > => 30
    rule Gsha3word < HOMESTEAD > => 6

    rule Gsload       < HOMESTEAD > => 50
    rule Gsstoreset   < HOMESTEAD > => 20000
    rule Gsstorereset < HOMESTEAD > => 5000
    rule Rsstoreclear < HOMESTEAD > => 15000

    rule Glog      < HOMESTEAD > => 375
    rule Glogdata  < HOMESTEAD > => 8
    rule Glogtopic < HOMESTEAD > => 375

    rule Gcall        < HOMESTEAD > => 40
    rule Gcallstipend < HOMESTEAD > => 2300
    rule Gcallvalue   < HOMESTEAD > => 9000
    rule Gnewaccount  < HOMESTEAD > => 25000

    rule Gcreate       < HOMESTEAD > => 32000
    rule Gcodedeposit  < HOMESTEAD > => 200
    rule Gselfdestruct < HOMESTEAD > => 0
    rule Rselfdestruct < HOMESTEAD > => 24000

    rule Gmemory      < HOMESTEAD > => 3
    rule Gquadcoeff   < HOMESTEAD > => 512
    rule Gcopy        < HOMESTEAD > => 3
    rule Gquaddivisor < HOMESTEAD > => 20

    rule Gtransaction   < HOMESTEAD > => 21000
    rule Gtxcreate      < HOMESTEAD > => 53000
    rule Gtxdatazero    < HOMESTEAD > => 4
    rule Gtxdatanonzero < HOMESTEAD > => 68

    rule Gjumpdest    < HOMESTEAD > => 1
    rule Gbalance     < HOMESTEAD > => 20
    rule Gblockhash   < HOMESTEAD > => 20
    rule Gextcodesize < HOMESTEAD > => 20
    rule Gextcodecopy < HOMESTEAD > => 20

    rule Gecadd       < HOMESTEAD > => 500
    rule Gecmul       < HOMESTEAD > => 40000
    rule Gecpairconst < HOMESTEAD > => 100000
    rule Gecpaircoeff < HOMESTEAD > => 80000
    rule Gfround      < HOMESTEAD > => 1

    rule maxCodeSize < HOMESTEAD > => 2 ^Int 32 -Int 1
    rule Rb          < HOMESTEAD > => 5 *Int eth

    rule Gcoldsload             < HOMESTEAD > => 0
    rule Gcoldaccountaccess     < HOMESTEAD > => 0
    rule Gwarmstorageread       < HOMESTEAD > => 0
    rule Gwarmstoragedirtystore < HOMESTEAD > => 0

    rule Gaccessliststoragekey < HOMESTEAD > => 0
    rule Gaccesslistaddress    < HOMESTEAD > => 0

    rule maxInitCodeSize   < HOMESTEAD > => 0
    rule Ginitcodewordcost < HOMESTEAD > => 0

    rule Rmaxquotient < HOMESTEAD > => 2

    rule Gselfdestructnewaccount << HOMESTEAD >> => false
    rule Gstaticcalldepth        << HOMESTEAD >> => true
    rule Gemptyisnonexistent     << HOMESTEAD >> => false
    rule Gzerovaluenewaccountgas << HOMESTEAD >> => true
    rule Ghasrevert              << HOMESTEAD >> => false
    rule Ghasreturndata          << HOMESTEAD >> => false
    rule Ghasstaticcall          << HOMESTEAD >> => false
    rule Ghasshift               << HOMESTEAD >> => false
    rule Ghasdirtysstore         << HOMESTEAD >> => false
    rule Ghassstorestipend       << HOMESTEAD >> => false
    rule Ghascreate2             << HOMESTEAD >> => false
    rule Ghasextcodehash         << HOMESTEAD >> => false
    rule Ghasselfbalance         << HOMESTEAD >> => false
    rule Ghaschainid             << HOMESTEAD >> => false
    rule Ghasaccesslist          << HOMESTEAD >> => false
    rule Ghasbasefee             << HOMESTEAD >> => false
    rule Ghasrejectedfirstbyte   << HOMESTEAD >> => false
    rule Ghasprevrandao          << HOMESTEAD >> => false
    rule Ghasmaxinitcodesize     << HOMESTEAD >> => false
    rule Ghaspushzero            << HOMESTEAD >> => false
    rule Ghaswarmcoinbase        << HOMESTEAD >> => false
    rule Ghastransient           << HOMESTEAD >> => false
    rule Ghasmcopy               << HOMESTEAD >> => false
    rule Ghasbeaconroot          << HOMESTEAD >> => false
```

### Tangerine Whistle Schedule

```k
    syntax Schedule ::= "TANGERINE_WHISTLE" [symbol(TANGERINE_WHISTLE_EVM), smtlib(schedule_TANGERINE_WHISTLE)]
 // -----------------------------------------------------------------------------------------------------------
    rule Gzero    < TANGERINE_WHISTLE > => 0
    rule Gbase    < TANGERINE_WHISTLE > => 2
    rule Gverylow < TANGERINE_WHISTLE > => 3
    rule Glow     < TANGERINE_WHISTLE > => 5
    rule Gmid     < TANGERINE_WHISTLE > => 8
    rule Ghigh    < TANGERINE_WHISTLE > => 10

    rule Gexp      < TANGERINE_WHISTLE > => 10
    rule Gexpbyte  < TANGERINE_WHISTLE > => 10
    rule Gsha3     < TANGERINE_WHISTLE > => 30
    rule Gsha3word < TANGERINE_WHISTLE > => 6

    rule Gsload       < TANGERINE_WHISTLE > => 200
    rule Gsstoreset   < TANGERINE_WHISTLE > => 20000
    rule Gsstorereset < TANGERINE_WHISTLE > => 5000
    rule Rsstoreclear < TANGERINE_WHISTLE > => 15000

    rule Glog      < TANGERINE_WHISTLE > => 375
    rule Glogdata  < TANGERINE_WHISTLE > => 8
    rule Glogtopic < TANGERINE_WHISTLE > => 375

    rule Gcall        < TANGERINE_WHISTLE > => 700
    rule Gcallstipend < TANGERINE_WHISTLE > => 2300
    rule Gcallvalue   < TANGERINE_WHISTLE > => 9000
    rule Gnewaccount  < TANGERINE_WHISTLE > => 25000

    rule Gcreate       < TANGERINE_WHISTLE > => 32000
    rule Gcodedeposit  < TANGERINE_WHISTLE > => 200
    rule Gselfdestruct < TANGERINE_WHISTLE > => 5000
    rule Rselfdestruct < TANGERINE_WHISTLE > => 24000

    rule Gmemory      < TANGERINE_WHISTLE > => 3
    rule Gquadcoeff   < TANGERINE_WHISTLE > => 512
    rule Gcopy        < TANGERINE_WHISTLE > => 3
    rule Gquaddivisor < TANGERINE_WHISTLE > => 20

    rule Gtransaction   < TANGERINE_WHISTLE > => 21000
    rule Gtxcreate      < TANGERINE_WHISTLE > => 53000
    rule Gtxdatazero    < TANGERINE_WHISTLE > => 4
    rule Gtxdatanonzero < TANGERINE_WHISTLE > => 68

    rule Gjumpdest    < TANGERINE_WHISTLE > => 1
    rule Gbalance     < TANGERINE_WHISTLE > => 400
    rule Gblockhash   < TANGERINE_WHISTLE > => 20
    rule Gextcodesize < TANGERINE_WHISTLE > => 700
    rule Gextcodecopy < TANGERINE_WHISTLE > => 700

    rule Gecadd       < TANGERINE_WHISTLE > => 500
    rule Gecmul       < TANGERINE_WHISTLE > => 40000
    rule Gecpairconst < TANGERINE_WHISTLE > => 100000
    rule Gecpaircoeff < TANGERINE_WHISTLE > => 80000
    rule Gfround      < TANGERINE_WHISTLE > => 1

    rule maxCodeSize < TANGERINE_WHISTLE > => 2 ^Int 32 -Int 1
    rule Rb          < TANGERINE_WHISTLE > => 5 *Int eth

    rule Gcoldsload             < TANGERINE_WHISTLE > => 0
    rule Gcoldaccountaccess     < TANGERINE_WHISTLE > => 0
    rule Gwarmstorageread       < TANGERINE_WHISTLE > => 0
    rule Gwarmstoragedirtystore < TANGERINE_WHISTLE > => 0

    rule Gaccessliststoragekey < TANGERINE_WHISTLE > => 0
    rule Gaccesslistaddress    < TANGERINE_WHISTLE > => 0

    rule maxInitCodeSize   < TANGERINE_WHISTLE > => 0
    rule Ginitcodewordcost < TANGERINE_WHISTLE > => 0

    rule Rmaxquotient < TANGERINE_WHISTLE > => 2

    rule Gselfdestructnewaccount << TANGERINE_WHISTLE >> => true
    rule Gstaticcalldepth        << TANGERINE_WHISTLE >> => false
    rule Gemptyisnonexistent     << TANGERINE_WHISTLE >> => false
    rule Gzerovaluenewaccountgas << TANGERINE_WHISTLE >> => true
    rule Ghasrevert              << TANGERINE_WHISTLE >> => false
    rule Ghasreturndata          << TANGERINE_WHISTLE >> => false
    rule Ghasstaticcall          << TANGERINE_WHISTLE >> => false
    rule Ghasshift               << TANGERINE_WHISTLE >> => false
    rule Ghasdirtysstore         << TANGERINE_WHISTLE >> => false
    rule Ghassstorestipend       << TANGERINE_WHISTLE >> => false
    rule Ghascreate2             << TANGERINE_WHISTLE >> => false
    rule Ghasextcodehash         << TANGERINE_WHISTLE >> => false
    rule Ghasselfbalance         << TANGERINE_WHISTLE >> => false
    rule Ghaschainid             << TANGERINE_WHISTLE >> => false
    rule Ghasaccesslist          << TANGERINE_WHISTLE >> => false
    rule Ghasbasefee             << TANGERINE_WHISTLE >> => false
    rule Ghasrejectedfirstbyte   << TANGERINE_WHISTLE >> => false
    rule Ghasprevrandao          << TANGERINE_WHISTLE >> => false
    rule Ghasmaxinitcodesize     << TANGERINE_WHISTLE >> => false
    rule Ghaspushzero            << TANGERINE_WHISTLE >> => false
    rule Ghaswarmcoinbase        << TANGERINE_WHISTLE >> => false
    rule Ghastransient           << TANGERINE_WHISTLE >> => false
    rule Ghasmcopy               << TANGERINE_WHISTLE >> => false
    rule Ghasbeaconroot          << TANGERINE_WHISTLE >> => false
```

### Spurious Dragon Schedule

```k
    syntax Schedule ::= "SPURIOUS_DRAGON" [symbol(SPURIOUS_DRAGON_EVM), smtlib(schedule_SPURIOUS_DRAGON)]
 // -----------------------------------------------------------------------------------------------------
    rule Gzero    < SPURIOUS_DRAGON > => 0
    rule Gbase    < SPURIOUS_DRAGON > => 2
    rule Gverylow < SPURIOUS_DRAGON > => 3
    rule Glow     < SPURIOUS_DRAGON > => 5
    rule Gmid     < SPURIOUS_DRAGON > => 8
    rule Ghigh    < SPURIOUS_DRAGON > => 10

    rule Gexp      < SPURIOUS_DRAGON > => 10
    rule Gexpbyte  < SPURIOUS_DRAGON > => 50
    rule Gsha3     < SPURIOUS_DRAGON > => 30
    rule Gsha3word < SPURIOUS_DRAGON > => 6

    rule Gsload       < SPURIOUS_DRAGON > => 200
    rule Gsstoreset   < SPURIOUS_DRAGON > => 20000
    rule Gsstorereset < SPURIOUS_DRAGON > => 5000
    rule Rsstoreclear < SPURIOUS_DRAGON > => 15000

    rule Glog      < SPURIOUS_DRAGON > => 375
    rule Glogdata  < SPURIOUS_DRAGON > => 8
    rule Glogtopic < SPURIOUS_DRAGON > => 375

    rule Gcall        < SPURIOUS_DRAGON > => 700
    rule Gcallstipend < SPURIOUS_DRAGON > => 2300
    rule Gcallvalue   < SPURIOUS_DRAGON > => 9000
    rule Gnewaccount  < SPURIOUS_DRAGON > => 25000

    rule Gcreate       < SPURIOUS_DRAGON > => 32000
    rule Gcodedeposit  < SPURIOUS_DRAGON > => 200
    rule Gselfdestruct < SPURIOUS_DRAGON > => 5000
    rule Rselfdestruct < SPURIOUS_DRAGON > => 24000

    rule Gmemory      < SPURIOUS_DRAGON > => 3
    rule Gquadcoeff   < SPURIOUS_DRAGON > => 512
    rule Gcopy        < SPURIOUS_DRAGON > => 3
    rule Gquaddivisor < SPURIOUS_DRAGON > => 20

    rule Gtransaction   < SPURIOUS_DRAGON > => 21000
    rule Gtxcreate      < SPURIOUS_DRAGON > => 53000
    rule Gtxdatazero    < SPURIOUS_DRAGON > => 4
    rule Gtxdatanonzero < SPURIOUS_DRAGON > => 68

    rule Gjumpdest    < SPURIOUS_DRAGON > => 1
    rule Gbalance     < SPURIOUS_DRAGON > => 400
    rule Gblockhash   < SPURIOUS_DRAGON > => 20
    rule Gextcodesize < SPURIOUS_DRAGON > => 700
    rule Gextcodecopy < SPURIOUS_DRAGON > => 700

    rule Gecadd       < SPURIOUS_DRAGON > => 500
    rule Gecmul       < SPURIOUS_DRAGON > => 40000
    rule Gecpairconst < SPURIOUS_DRAGON > => 100000
    rule Gecpaircoeff < SPURIOUS_DRAGON > => 80000
    rule Gfround      < SPURIOUS_DRAGON > => 1

    rule maxCodeSize < SPURIOUS_DRAGON > => 24576
    rule Rb          < SPURIOUS_DRAGON > => 5 *Int eth

    rule Gcoldsload             < SPURIOUS_DRAGON > => 0
    rule Gcoldaccountaccess     < SPURIOUS_DRAGON > => 0
    rule Gwarmstorageread       < SPURIOUS_DRAGON > => 0
    rule Gwarmstoragedirtystore < SPURIOUS_DRAGON > => 0

    rule Gaccessliststoragekey < SPURIOUS_DRAGON > => 0
    rule Gaccesslistaddress    < SPURIOUS_DRAGON > => 0

    rule maxInitCodeSize   < SPURIOUS_DRAGON > => 0
    rule Ginitcodewordcost < SPURIOUS_DRAGON > => 0

    rule Rmaxquotient < SPURIOUS_DRAGON > => 2

    rule Gselfdestructnewaccount << SPURIOUS_DRAGON >> => true
    rule Gstaticcalldepth        << SPURIOUS_DRAGON >> => false
    rule Gemptyisnonexistent     << SPURIOUS_DRAGON >> => true
    rule Gzerovaluenewaccountgas << SPURIOUS_DRAGON >> => false
    rule Ghasrevert              << SPURIOUS_DRAGON >> => false
    rule Ghasreturndata          << SPURIOUS_DRAGON >> => false
    rule Ghasstaticcall          << SPURIOUS_DRAGON >> => false
    rule Ghasshift               << SPURIOUS_DRAGON >> => false
    rule Ghasdirtysstore         << SPURIOUS_DRAGON >> => false
    rule Ghassstorestipend       << SPURIOUS_DRAGON >> => false
    rule Ghascreate2             << SPURIOUS_DRAGON >> => false
    rule Ghasextcodehash         << SPURIOUS_DRAGON >> => false
    rule Ghasselfbalance         << SPURIOUS_DRAGON >> => false
    rule Ghaschainid             << SPURIOUS_DRAGON >> => false
    rule Ghasaccesslist          << SPURIOUS_DRAGON >> => false
    rule Ghasbasefee             << SPURIOUS_DRAGON >> => false
    rule Ghasrejectedfirstbyte   << SPURIOUS_DRAGON >> => false
    rule Ghasprevrandao          << SPURIOUS_DRAGON >> => false
    rule Ghasmaxinitcodesize     << SPURIOUS_DRAGON >> => false
    rule Ghaspushzero            << SPURIOUS_DRAGON >> => false
    rule Ghaswarmcoinbase        << SPURIOUS_DRAGON >> => false
    rule Ghastransient           << SPURIOUS_DRAGON >> => false
    rule Ghasmcopy               << SPURIOUS_DRAGON >> => false
    rule Ghasbeaconroot          << SPURIOUS_DRAGON >> => false
```

### Byzantium Schedule

```k
    syntax Schedule ::= "BYZANTIUM" [symbol(BYZANTIUM_EVM), smtlib(schedule_BYZANTIUM)]
 // -----------------------------------------------------------------------------------
    rule Gzero    < BYZANTIUM > => 0
    rule Gbase    < BYZANTIUM > => 2
    rule Gverylow < BYZANTIUM > => 3
    rule Glow     < BYZANTIUM > => 5
    rule Gmid     < BYZANTIUM > => 8
    rule Ghigh    < BYZANTIUM > => 10

    rule Gexp      < BYZANTIUM > => 10
    rule Gexpbyte  < BYZANTIUM > => 50
    rule Gsha3     < BYZANTIUM > => 30
    rule Gsha3word < BYZANTIUM > => 6

    rule Gsload       < BYZANTIUM > => 200
    rule Gsstoreset   < BYZANTIUM > => 20000
    rule Gsstorereset < BYZANTIUM > => 5000
    rule Rsstoreclear < BYZANTIUM > => 15000

    rule Glog      < BYZANTIUM > => 375
    rule Glogdata  < BYZANTIUM > => 8
    rule Glogtopic < BYZANTIUM > => 375

    rule Gcall        < BYZANTIUM > => 700
    rule Gcallstipend < BYZANTIUM > => 2300
    rule Gcallvalue   < BYZANTIUM > => 9000
    rule Gnewaccount  < BYZANTIUM > => 25000

    rule Gcreate       < BYZANTIUM > => 32000
    rule Gcodedeposit  < BYZANTIUM > => 200
    rule Gselfdestruct < BYZANTIUM > => 5000
    rule Rselfdestruct < BYZANTIUM > => 24000

    rule Gmemory      < BYZANTIUM > => 3
    rule Gquadcoeff   < BYZANTIUM > => 512
    rule Gcopy        < BYZANTIUM > => 3
    rule Gquaddivisor < BYZANTIUM > => 20

    rule Gtransaction   < BYZANTIUM > => 21000
    rule Gtxcreate      < BYZANTIUM > => 53000
    rule Gtxdatazero    < BYZANTIUM > => 4
    rule Gtxdatanonzero < BYZANTIUM > => 68

    rule Gjumpdest    < BYZANTIUM > => 1
    rule Gbalance     < BYZANTIUM > => 400
    rule Gblockhash   < BYZANTIUM > => 20
    rule Gextcodesize < BYZANTIUM > => 700
    rule Gextcodecopy < BYZANTIUM > => 700

    rule Gecadd       < BYZANTIUM > => 500
    rule Gecmul       < BYZANTIUM > => 40000
    rule Gecpairconst < BYZANTIUM > => 100000
    rule Gecpaircoeff < BYZANTIUM > => 80000
    rule Gfround      < BYZANTIUM > => 1

    rule maxCodeSize < BYZANTIUM > => 24576
    rule Rb          < BYZANTIUM > => 3 *Int eth

    rule Gcoldsload             < BYZANTIUM > => 0
    rule Gcoldaccountaccess     < BYZANTIUM > => 0
    rule Gwarmstorageread       < BYZANTIUM > => 0
    rule Gwarmstoragedirtystore < BYZANTIUM > => 0

    rule Gaccessliststoragekey < BYZANTIUM > => 0
    rule Gaccesslistaddress    < BYZANTIUM > => 0

    rule maxInitCodeSize   < BYZANTIUM > => 0
    rule Ginitcodewordcost < BYZANTIUM > => 0

    rule Rmaxquotient < BYZANTIUM > => 2

    rule Gselfdestructnewaccount << BYZANTIUM >> => true
    rule Gstaticcalldepth        << BYZANTIUM >> => false
    rule Gemptyisnonexistent     << BYZANTIUM >> => true
    rule Gzerovaluenewaccountgas << BYZANTIUM >> => false
    rule Ghasrevert              << BYZANTIUM >> => true
    rule Ghasreturndata          << BYZANTIUM >> => true
    rule Ghasstaticcall          << BYZANTIUM >> => true
    rule Ghasshift               << BYZANTIUM >> => false
    rule Ghasdirtysstore         << BYZANTIUM >> => false
    rule Ghassstorestipend       << BYZANTIUM >> => false
    rule Ghascreate2             << BYZANTIUM >> => false
    rule Ghasextcodehash         << BYZANTIUM >> => false
    rule Ghasselfbalance         << BYZANTIUM >> => false
    rule Ghaschainid             << BYZANTIUM >> => false
    rule Ghasaccesslist          << BYZANTIUM >> => false
    rule Ghasbasefee             << BYZANTIUM >> => false
    rule Ghasrejectedfirstbyte   << BYZANTIUM >> => false
    rule Ghasprevrandao          << BYZANTIUM >> => false
    rule Ghasmaxinitcodesize     << BYZANTIUM >> => false
    rule Ghaspushzero            << BYZANTIUM >> => false
    rule Ghaswarmcoinbase        << BYZANTIUM >> => false
    rule Ghastransient           << BYZANTIUM >> => false
    rule Ghasmcopy               << BYZANTIUM >> => false
    rule Ghasbeaconroot          << BYZANTIUM >> => false
```

### Constantinople Schedule

```k
    syntax Schedule ::= "CONSTANTINOPLE" [symbol(CONSTANTINOPLE_EVM), smtlib(schedule_CONSTANTINOPLE)]
 // --------------------------------------------------------------------------------------------------
    rule Gzero    < CONSTANTINOPLE > => 0
    rule Gbase    < CONSTANTINOPLE > => 2
    rule Gverylow < CONSTANTINOPLE > => 3
    rule Glow     < CONSTANTINOPLE > => 5
    rule Gmid     < CONSTANTINOPLE > => 8
    rule Ghigh    < CONSTANTINOPLE > => 10

    rule Gexp      < CONSTANTINOPLE > => 10
    rule Gexpbyte  < CONSTANTINOPLE > => 50
    rule Gsha3     < CONSTANTINOPLE > => 30
    rule Gsha3word < CONSTANTINOPLE > => 6

    rule Gsload       < CONSTANTINOPLE > => 200
    rule Gsstoreset   < CONSTANTINOPLE > => 20000
    rule Gsstorereset < CONSTANTINOPLE > => 5000
    rule Rsstoreclear < CONSTANTINOPLE > => 15000

    rule Glog      < CONSTANTINOPLE > => 375
    rule Glogdata  < CONSTANTINOPLE > => 8
    rule Glogtopic < CONSTANTINOPLE > => 375

    rule Gcall        < CONSTANTINOPLE > => 700
    rule Gcallstipend < CONSTANTINOPLE > => 2300
    rule Gcallvalue   < CONSTANTINOPLE > => 9000
    rule Gnewaccount  < CONSTANTINOPLE > => 25000

    rule Gcreate       < CONSTANTINOPLE > => 32000
    rule Gcodedeposit  < CONSTANTINOPLE > => 200
    rule Gselfdestruct < CONSTANTINOPLE > => 5000
    rule Rselfdestruct < CONSTANTINOPLE > => 24000

    rule Gmemory      < CONSTANTINOPLE > => 3
    rule Gquadcoeff   < CONSTANTINOPLE > => 512
    rule Gcopy        < CONSTANTINOPLE > => 3
    rule Gquaddivisor < CONSTANTINOPLE > => 20

    rule Gtransaction   < CONSTANTINOPLE > => 21000
    rule Gtxcreate      < CONSTANTINOPLE > => 53000
    rule Gtxdatazero    < CONSTANTINOPLE > => 4
    rule Gtxdatanonzero < CONSTANTINOPLE > => 68

    rule Gjumpdest    < CONSTANTINOPLE > => 1
    rule Gbalance     < CONSTANTINOPLE > => 400
    rule Gblockhash   < CONSTANTINOPLE > => 20
    rule Gextcodesize < CONSTANTINOPLE > => 700
    rule Gextcodecopy < CONSTANTINOPLE > => 700

    rule Gecadd       < CONSTANTINOPLE > => 500
    rule Gecmul       < CONSTANTINOPLE > => 40000
    rule Gecpairconst < CONSTANTINOPLE > => 100000
    rule Gecpaircoeff < CONSTANTINOPLE > => 80000
    rule Gfround      < CONSTANTINOPLE > => 1

    rule maxCodeSize < CONSTANTINOPLE > => 24576
    rule Rb          < CONSTANTINOPLE > => 2 *Int eth

    rule Gcoldsload             < CONSTANTINOPLE > => 0
    rule Gcoldaccountaccess     < CONSTANTINOPLE > => 0
    rule Gwarmstorageread       < CONSTANTINOPLE > => 0
    rule Gwarmstoragedirtystore < CONSTANTINOPLE > => 0

    rule Gaccessliststoragekey < CONSTANTINOPLE > => 0
    rule Gaccesslistaddress    < CONSTANTINOPLE > => 0

    rule maxInitCodeSize   < CONSTANTINOPLE > => 0
    rule Ginitcodewordcost < CONSTANTINOPLE > => 0

    rule Rmaxquotient < CONSTANTINOPLE > => 2

    rule Gselfdestructnewaccount << CONSTANTINOPLE >> => true
    rule Gstaticcalldepth        << CONSTANTINOPLE >> => false
    rule Gemptyisnonexistent     << CONSTANTINOPLE >> => true
    rule Gzerovaluenewaccountgas << CONSTANTINOPLE >> => false
    rule Ghasrevert              << CONSTANTINOPLE >> => true
    rule Ghasreturndata          << CONSTANTINOPLE >> => true
    rule Ghasstaticcall          << CONSTANTINOPLE >> => true
    rule Ghasshift               << CONSTANTINOPLE >> => true
    rule Ghasdirtysstore         << CONSTANTINOPLE >> => true
    rule Ghassstorestipend       << CONSTANTINOPLE >> => false
    rule Ghascreate2             << CONSTANTINOPLE >> => true
    rule Ghasextcodehash         << CONSTANTINOPLE >> => true
    rule Ghasselfbalance         << CONSTANTINOPLE >> => false
    rule Ghaschainid             << CONSTANTINOPLE >> => false
    rule Ghasaccesslist          << CONSTANTINOPLE >> => false
    rule Ghasbasefee             << CONSTANTINOPLE >> => false
    rule Ghasrejectedfirstbyte   << CONSTANTINOPLE >> => false
    rule Ghasprevrandao          << CONSTANTINOPLE >> => false
    rule Ghasmaxinitcodesize     << CONSTANTINOPLE >> => false
    rule Ghaspushzero            << CONSTANTINOPLE >> => false
    rule Ghaswarmcoinbase        << CONSTANTINOPLE >> => false
    rule Ghastransient           << CONSTANTINOPLE >> => false
    rule Ghasmcopy               << CONSTANTINOPLE >> => false
    rule Ghasbeaconroot          << CONSTANTINOPLE >> => false
```

### Petersburg Schedule

```k
    syntax Schedule ::= "PETERSBURG" [symbol(PETERSBURG_EVM), smtlib(schedule_PETERSBURG)]
 // --------------------------------------------------------------------------------------
    rule Gzero    < PETERSBURG > => 0
    rule Gbase    < PETERSBURG > => 2
    rule Gverylow < PETERSBURG > => 3
    rule Glow     < PETERSBURG > => 5
    rule Gmid     < PETERSBURG > => 8
    rule Ghigh    < PETERSBURG > => 10

    rule Gexp      < PETERSBURG > => 10
    rule Gexpbyte  < PETERSBURG > => 50
    rule Gsha3     < PETERSBURG > => 30
    rule Gsha3word < PETERSBURG > => 6

    rule Gsload       < PETERSBURG > => 200
    rule Gsstoreset   < PETERSBURG > => 20000
    rule Gsstorereset < PETERSBURG > => 5000
    rule Rsstoreclear < PETERSBURG > => 15000

    rule Glog      < PETERSBURG > => 375
    rule Glogdata  < PETERSBURG > => 8
    rule Glogtopic < PETERSBURG > => 375

    rule Gcall        < PETERSBURG > => 700
    rule Gcallstipend < PETERSBURG > => 2300
    rule Gcallvalue   < PETERSBURG > => 9000
    rule Gnewaccount  < PETERSBURG > => 25000

    rule Gcreate       < PETERSBURG > => 32000
    rule Gcodedeposit  < PETERSBURG > => 200
    rule Gselfdestruct < PETERSBURG > => 5000
    rule Rselfdestruct < PETERSBURG > => 24000

    rule Gmemory      < PETERSBURG > => 3
    rule Gquadcoeff   < PETERSBURG > => 512
    rule Gcopy        < PETERSBURG > => 3
    rule Gquaddivisor < PETERSBURG > => 20

    rule Gtransaction   < PETERSBURG > => 21000
    rule Gtxcreate      < PETERSBURG > => 53000
    rule Gtxdatazero    < PETERSBURG > => 4
    rule Gtxdatanonzero < PETERSBURG > => 68

    rule Gjumpdest    < PETERSBURG > => 1
    rule Gbalance     < PETERSBURG > => 400
    rule Gblockhash   < PETERSBURG > => 20
    rule Gextcodesize < PETERSBURG > => 700
    rule Gextcodecopy < PETERSBURG > => 700

    rule Gecadd       < PETERSBURG > => 500
    rule Gecmul       < PETERSBURG > => 40000
    rule Gecpairconst < PETERSBURG > => 100000
    rule Gecpaircoeff < PETERSBURG > => 80000
    rule Gfround      < PETERSBURG > => 1

    rule maxCodeSize < PETERSBURG > => 24576
    rule Rb          < PETERSBURG > => 2 *Int eth

    rule Gcoldsload             < PETERSBURG > => 0
    rule Gcoldaccountaccess     < PETERSBURG > => 0
    rule Gwarmstorageread       < PETERSBURG > => 0
    rule Gwarmstoragedirtystore < PETERSBURG > => 0

    rule Gaccessliststoragekey < PETERSBURG > => 0
    rule Gaccesslistaddress    < PETERSBURG > => 0

    rule maxInitCodeSize   < PETERSBURG > => 0
    rule Ginitcodewordcost < PETERSBURG > => 0

    rule Rmaxquotient < PETERSBURG > => 2

    rule Gselfdestructnewaccount << PETERSBURG >> => true
    rule Gstaticcalldepth        << PETERSBURG >> => false
    rule Gemptyisnonexistent     << PETERSBURG >> => true
    rule Gzerovaluenewaccountgas << PETERSBURG >> => false
    rule Ghasrevert              << PETERSBURG >> => true
    rule Ghasreturndata          << PETERSBURG >> => true
    rule Ghasstaticcall          << PETERSBURG >> => true
    rule Ghasshift               << PETERSBURG >> => true
    rule Ghasdirtysstore         << PETERSBURG >> => false
    rule Ghassstorestipend       << PETERSBURG >> => false
    rule Ghascreate2             << PETERSBURG >> => true
    rule Ghasextcodehash         << PETERSBURG >> => true
    rule Ghasselfbalance         << PETERSBURG >> => false
    rule Ghaschainid             << PETERSBURG >> => false
    rule Ghasaccesslist          << PETERSBURG >> => false
    rule Ghasbasefee             << PETERSBURG >> => false
    rule Ghasrejectedfirstbyte   << PETERSBURG >> => false
    rule Ghasprevrandao          << PETERSBURG >> => false
    rule Ghasmaxinitcodesize     << PETERSBURG >> => false
    rule Ghaspushzero            << PETERSBURG >> => false
    rule Ghaswarmcoinbase        << PETERSBURG >> => false
    rule Ghastransient           << PETERSBURG >> => false
    rule Ghasmcopy               << PETERSBURG >> => false
    rule Ghasbeaconroot          << PETERSBURG >> => false
```

### Istanbul Schedule

```k
    syntax Schedule ::= "ISTANBUL" [symbol(ISTANBUL_EVM), smtlib(schedule_ISTANBUL)]
 // --------------------------------------------------------------------------------
    rule Gzero    < ISTANBUL > => 0
    rule Gbase    < ISTANBUL > => 2
    rule Gverylow < ISTANBUL > => 3
    rule Glow     < ISTANBUL > => 5
    rule Gmid     < ISTANBUL > => 8
    rule Ghigh    < ISTANBUL > => 10

    rule Gexp      < ISTANBUL > => 10
    rule Gexpbyte  < ISTANBUL > => 50
    rule Gsha3     < ISTANBUL > => 30
    rule Gsha3word < ISTANBUL > => 6

    rule Gsload       < ISTANBUL > => 800
    rule Gsstoreset   < ISTANBUL > => 20000
    rule Gsstorereset < ISTANBUL > => 5000
    rule Rsstoreclear < ISTANBUL > => 15000

    rule Glog      < ISTANBUL > => 375
    rule Glogdata  < ISTANBUL > => 8
    rule Glogtopic < ISTANBUL > => 375

    rule Gcall        < ISTANBUL > => 700
    rule Gcallstipend < ISTANBUL > => 2300
    rule Gcallvalue   < ISTANBUL > => 9000
    rule Gnewaccount  < ISTANBUL > => 25000

    rule Gcreate       < ISTANBUL > => 32000
    rule Gcodedeposit  < ISTANBUL > => 200
    rule Gselfdestruct < ISTANBUL > => 5000
    rule Rselfdestruct < ISTANBUL > => 24000

    rule Gmemory      < ISTANBUL > => 3
    rule Gquadcoeff   < ISTANBUL > => 512
    rule Gcopy        < ISTANBUL > => 3
    rule Gquaddivisor < ISTANBUL > => 20

    rule Gtransaction   < ISTANBUL > => 21000
    rule Gtxcreate      < ISTANBUL > => 53000
    rule Gtxdatazero    < ISTANBUL > => 4
    rule Gtxdatanonzero < ISTANBUL > => 16

    rule Gjumpdest    < ISTANBUL > => 1
    rule Gbalance     < ISTANBUL > => 700
    rule Gblockhash   < ISTANBUL > => 20
    rule Gextcodesize < ISTANBUL > => 700
    rule Gextcodecopy < ISTANBUL > => 700

    rule Gecadd       < ISTANBUL > => 150
    rule Gecmul       < ISTANBUL > => 6000
    rule Gecpairconst < ISTANBUL > => 45000
    rule Gecpaircoeff < ISTANBUL > => 34000
    rule Gfround      < ISTANBUL > => 1

    rule maxCodeSize < ISTANBUL > => 24576
    rule Rb          < ISTANBUL > => 2 *Int eth

    rule Gcoldsload             < ISTANBUL > => 0
    rule Gcoldaccountaccess     < ISTANBUL > => 0
    rule Gwarmstorageread       < ISTANBUL > => 0
    rule Gwarmstoragedirtystore < ISTANBUL > => 0

    rule Gaccessliststoragekey < ISTANBUL > => 0
    rule Gaccesslistaddress    < ISTANBUL > => 0

    rule maxInitCodeSize   < ISTANBUL > => 0
    rule Ginitcodewordcost < ISTANBUL > => 0

    rule Rmaxquotient < ISTANBUL > => 2

    rule Gselfdestructnewaccount << ISTANBUL >> => true
    rule Gstaticcalldepth        << ISTANBUL >> => false
    rule Gemptyisnonexistent     << ISTANBUL >> => true
    rule Gzerovaluenewaccountgas << ISTANBUL >> => false
    rule Ghasrevert              << ISTANBUL >> => true
    rule Ghasreturndata          << ISTANBUL >> => true
    rule Ghasstaticcall          << ISTANBUL >> => true
    rule Ghasshift               << ISTANBUL >> => true
    rule Ghasdirtysstore         << ISTANBUL >> => true
    rule Ghassstorestipend       << ISTANBUL >> => true
    rule Ghascreate2             << ISTANBUL >> => true
    rule Ghasextcodehash         << ISTANBUL >> => true
    rule Ghasselfbalance         << ISTANBUL >> => true
    rule Ghaschainid             << ISTANBUL >> => true
    rule Ghasaccesslist          << ISTANBUL >> => false
    rule Ghasbasefee             << ISTANBUL >> => false
    rule Ghasrejectedfirstbyte   << ISTANBUL >> => false
    rule Ghasprevrandao          << ISTANBUL >> => false
    rule Ghasmaxinitcodesize     << ISTANBUL >> => false
    rule Ghaspushzero            << ISTANBUL >> => false
    rule Ghaswarmcoinbase        << ISTANBUL >> => false
    rule Ghastransient           << ISTANBUL >> => false
    rule Ghasmcopy               << ISTANBUL >> => false
    rule Ghasbeaconroot          << ISTANBUL >> => false
```

### Berlin Schedule

```k
    syntax Schedule ::= "BERLIN" [symbol(BERLIN_EVM), smtlib(schedule_BERLIN)]
 // --------------------------------------------------------------------------
    rule Gzero    < BERLIN > => 0
    rule Gbase    < BERLIN > => 2
    rule Gverylow < BERLIN > => 3
    rule Glow     < BERLIN > => 5
    rule Gmid     < BERLIN > => 8
    rule Ghigh    < BERLIN > => 10

    rule Gexp      < BERLIN > => 10
    rule Gexpbyte  < BERLIN > => 50
    rule Gsha3     < BERLIN > => 30
    rule Gsha3word < BERLIN > => 6

    rule Gsload       < BERLIN > => 100
    rule Gsstoreset   < BERLIN > => 20000
    rule Gsstorereset < BERLIN > => 2900
    rule Rsstoreclear < BERLIN > => 15000

    rule Glog      < BERLIN > => 375
    rule Glogdata  < BERLIN > => 8
    rule Glogtopic < BERLIN > => 375

    rule Gcall        < BERLIN > => 700
    rule Gcallstipend < BERLIN > => 2300
    rule Gcallvalue   < BERLIN > => 9000
    rule Gnewaccount  < BERLIN > => 25000

    rule Gcreate       < BERLIN > => 32000
    rule Gcodedeposit  < BERLIN > => 200
    rule Gselfdestruct < BERLIN > => 5000
    rule Rselfdestruct < BERLIN > => 24000

    rule Gmemory      < BERLIN > => 3
    rule Gquadcoeff   < BERLIN > => 512
    rule Gcopy        < BERLIN > => 3
    rule Gquaddivisor < BERLIN > => 3

    rule Gtransaction   < BERLIN > => 21000
    rule Gtxcreate      < BERLIN > => 53000
    rule Gtxdatazero    < BERLIN > => 4
    rule Gtxdatanonzero < BERLIN > => 16

    rule Gjumpdest    < BERLIN > => 1
    rule Gbalance     < BERLIN > => 700
    rule Gblockhash   < BERLIN > => 20
    rule Gextcodesize < BERLIN > => 700
    rule Gextcodecopy < BERLIN > => 700

    rule Gecadd       < BERLIN > => 150
    rule Gecmul       < BERLIN > => 6000
    rule Gecpairconst < BERLIN > => 45000
    rule Gecpaircoeff < BERLIN > => 34000
    rule Gfround      < BERLIN > => 1

    rule maxCodeSize < BERLIN > => 24576
    rule Rb          < BERLIN > => 2 *Int eth

    rule Gcoldsload             < BERLIN > => 2100
    rule Gcoldaccountaccess     < BERLIN > => 2600
    rule Gwarmstorageread       < BERLIN > => 100
    rule Gwarmstoragedirtystore < BERLIN > => 0

    rule Gaccessliststoragekey < BERLIN > => 1900
    rule Gaccesslistaddress    < BERLIN > => 2400

    rule maxInitCodeSize   < BERLIN > => 0
    rule Ginitcodewordcost < BERLIN > => 0

    rule Rmaxquotient < BERLIN > => 2

    rule Gselfdestructnewaccount << BERLIN >> => true
    rule Gstaticcalldepth        << BERLIN >> => false
    rule Gemptyisnonexistent     << BERLIN >> => true
    rule Gzerovaluenewaccountgas << BERLIN >> => false
    rule Ghasrevert              << BERLIN >> => true
    rule Ghasreturndata          << BERLIN >> => true
    rule Ghasstaticcall          << BERLIN >> => true
    rule Ghasshift               << BERLIN >> => true
    rule Ghasdirtysstore         << BERLIN >> => true
    rule Ghassstorestipend       << BERLIN >> => true
    rule Ghascreate2             << BERLIN >> => true
    rule Ghasextcodehash         << BERLIN >> => true
    rule Ghasselfbalance         << BERLIN >> => true
    rule Ghaschainid             << BERLIN >> => true
    rule Ghasaccesslist          << BERLIN >> => true
    rule Ghasbasefee             << BERLIN >> => false
    rule Ghasrejectedfirstbyte   << BERLIN >> => false
    rule Ghasprevrandao          << BERLIN >> => false
    rule Ghasmaxinitcodesize     << BERLIN >> => false
    rule Ghaspushzero            << BERLIN >> => false
    rule Ghaswarmcoinbase        << BERLIN >> => false
    rule Ghastransient           << BERLIN >> => false
    rule Ghasmcopy               << BERLIN >> => false
    rule Ghasbeaconroot          << BERLIN >> => false
```

### London Schedule

```k
    syntax Schedule ::= "LONDON" [symbol(LONDON_EVM), smtlib(schedule_LONDON)]
 // --------------------------------------------------------------------------
    rule Gzero    < LONDON > => 0
    rule Gbase    < LONDON > => 2
    rule Gverylow < LONDON > => 3
    rule Glow     < LONDON > => 5
    rule Gmid     < LONDON > => 8
    rule Ghigh    < LONDON > => 10

    rule Gexp      < LONDON > => 10
    rule Gexpbyte  < LONDON > => 50
    rule Gsha3     < LONDON > => 30
    rule Gsha3word < LONDON > => 6

    rule Gsload       < LONDON > => 100
    rule Gsstoreset   < LONDON > => 20000
    rule Gsstorereset < LONDON > => 2900
    rule Rsstoreclear < LONDON > => 4800

    rule Glog      < LONDON > => 375
    rule Glogdata  < LONDON > => 8
    rule Glogtopic < LONDON > => 375

    rule Gcall        < LONDON > => 700
    rule Gcallstipend < LONDON > => 2300
    rule Gcallvalue   < LONDON > => 9000
    rule Gnewaccount  < LONDON > => 25000

    rule Gcreate       < LONDON > => 32000
    rule Gcodedeposit  < LONDON > => 200
    rule Gselfdestruct < LONDON > => 5000
    rule Rselfdestruct < LONDON > => 0

    rule Gmemory      < LONDON > => 3
    rule Gquadcoeff   < LONDON > => 512
    rule Gcopy        < LONDON > => 3
    rule Gquaddivisor < LONDON > => 3

    rule Gtransaction   < LONDON > => 21000
    rule Gtxcreate      < LONDON > => 53000
    rule Gtxdatazero    < LONDON > => 4
    rule Gtxdatanonzero < LONDON > => 16

    rule Gjumpdest    < LONDON > => 1
    rule Gbalance     < LONDON > => 700
    rule Gblockhash   < LONDON > => 20
    rule Gextcodesize < LONDON > => 700
    rule Gextcodecopy < LONDON > => 700

    rule Gecadd       < LONDON > => 150
    rule Gecmul       < LONDON > => 6000
    rule Gecpairconst < LONDON > => 45000
    rule Gecpaircoeff < LONDON > => 34000
    rule Gfround      < LONDON > => 1

    rule maxCodeSize < LONDON > => 24576
    rule Rb          < LONDON > => 2 *Int eth

    rule Gcoldsload             < LONDON > => 2100
    rule Gcoldaccountaccess     < LONDON > => 2600
    rule Gwarmstorageread       < LONDON > => 100
    rule Gwarmstoragedirtystore < LONDON > => 0

    rule Gaccessliststoragekey < LONDON > => 1900
    rule Gaccesslistaddress    < LONDON > => 2400

    rule maxInitCodeSize   < LONDON > => 0
    rule Ginitcodewordcost < LONDON > => 0

    rule Rmaxquotient < LONDON > => 5

    rule Gselfdestructnewaccount << LONDON >> => true
    rule Gstaticcalldepth        << LONDON >> => false
    rule Gemptyisnonexistent     << LONDON >> => true
    rule Gzerovaluenewaccountgas << LONDON >> => false
    rule Ghasrevert              << LONDON >> => true
    rule Ghasreturndata          << LONDON >> => true
    rule Ghasstaticcall          << LONDON >> => true
    rule Ghasshift               << LONDON >> => true
    rule Ghasdirtysstore         << LONDON >> => true
    rule Ghassstorestipend       << LONDON >> => true
    rule Ghascreate2             << LONDON >> => true
    rule Ghasextcodehash         << LONDON >> => true
    rule Ghasselfbalance         << LONDON >> => true
    rule Ghaschainid             << LONDON >> => true
    rule Ghasaccesslist          << LONDON >> => true
    rule Ghasbasefee             << LONDON >> => true
    rule Ghasrejectedfirstbyte   << LONDON >> => true
    rule Ghasprevrandao          << LONDON >> => false
    rule Ghasmaxinitcodesize     << LONDON >> => false
    rule Ghaspushzero            << LONDON >> => false
    rule Ghaswarmcoinbase        << LONDON >> => false
    rule Ghastransient           << LONDON >> => false
    rule Ghasmcopy               << LONDON >> => false
    rule Ghasbeaconroot          << LONDON >> => false
```

### Merge Schedule

```k
    syntax Schedule ::= "MERGE" [symbol(MERGE_EVM), smtlib(schedule_MERGE)]
 // -----------------------------------------------------------------------
    rule Gzero    < MERGE > => 0
    rule Gbase    < MERGE > => 2
    rule Gverylow < MERGE > => 3
    rule Glow     < MERGE > => 5
    rule Gmid     < MERGE > => 8
    rule Ghigh    < MERGE > => 10

    rule Gexp      < MERGE > => 10
    rule Gexpbyte  < MERGE > => 50
    rule Gsha3     < MERGE > => 30
    rule Gsha3word < MERGE > => 6

    rule Gsload       < MERGE > => 100
    rule Gsstoreset   < MERGE > => 20000
    rule Gsstorereset < MERGE > => 2900
    rule Rsstoreclear < MERGE > => 4800

    rule Glog      < MERGE > => 375
    rule Glogdata  < MERGE > => 8
    rule Glogtopic < MERGE > => 375

    rule Gcall        < MERGE > => 700
    rule Gcallstipend < MERGE > => 2300
    rule Gcallvalue   < MERGE > => 9000
    rule Gnewaccount  < MERGE > => 25000

    rule Gcreate       < MERGE > => 32000
    rule Gcodedeposit  < MERGE > => 200
    rule Gselfdestruct < MERGE > => 5000
    rule Rselfdestruct < MERGE > => 0

    rule Gmemory      < MERGE > => 3
    rule Gquadcoeff   < MERGE > => 512
    rule Gcopy        < MERGE > => 3
    rule Gquaddivisor < MERGE > => 3

    rule Gtransaction   < MERGE > => 21000
    rule Gtxcreate      < MERGE > => 53000
    rule Gtxdatazero    < MERGE > => 4
    rule Gtxdatanonzero < MERGE > => 16

    rule Gjumpdest    < MERGE > => 1
    rule Gbalance     < MERGE > => 700
    rule Gblockhash   < MERGE > => 20
    rule Gextcodesize < MERGE > => 700
    rule Gextcodecopy < MERGE > => 700

    rule Gecadd       < MERGE > => 150
    rule Gecmul       < MERGE > => 6000
    rule Gecpairconst < MERGE > => 45000
    rule Gecpaircoeff < MERGE > => 34000
    rule Gfround      < MERGE > => 1

    rule maxCodeSize < MERGE > => 24576
    rule Rb          < MERGE > => 0

    rule Gcoldsload             < MERGE > => 2100
    rule Gcoldaccountaccess     < MERGE > => 2600
    rule Gwarmstorageread       < MERGE > => 100
    rule Gwarmstoragedirtystore < MERGE > => 0 

    rule Gaccessliststoragekey < MERGE > => 1900
    rule Gaccesslistaddress    < MERGE > => 2400

    rule maxInitCodeSize   < MERGE > => 0
    rule Ginitcodewordcost < MERGE > => 0

    rule Rmaxquotient < MERGE > => 5

    rule Gselfdestructnewaccount << MERGE >> => true
    rule Gstaticcalldepth        << MERGE >> => false
    rule Gemptyisnonexistent     << MERGE >> => true
    rule Gzerovaluenewaccountgas << MERGE >> => false
    rule Ghasrevert              << MERGE >> => true
    rule Ghasreturndata          << MERGE >> => true
    rule Ghasstaticcall          << MERGE >> => true
    rule Ghasshift               << MERGE >> => true
    rule Ghasdirtysstore         << MERGE >> => true
    rule Ghassstorestipend       << MERGE >> => true
    rule Ghascreate2             << MERGE >> => true
    rule Ghasextcodehash         << MERGE >> => true
    rule Ghasselfbalance         << MERGE >> => true
    rule Ghaschainid             << MERGE >> => true
    rule Ghasaccesslist          << MERGE >> => true
    rule Ghasbasefee             << MERGE >> => true
    rule Ghasrejectedfirstbyte   << MERGE >> => true
    rule Ghasprevrandao          << MERGE >> => true
    rule Ghasmaxinitcodesize     << MERGE >> => false
    rule Ghaspushzero            << MERGE >> => false
    rule Ghaswarmcoinbase        << MERGE >> => false
    rule Ghastransient           << MERGE >> => false
    rule Ghasmcopy               << MERGE >> => false
    rule Ghasbeaconroot          << MERGE >> => false
```

### Shanghai Schedule

```k
    syntax Schedule ::= "SHANGHAI" [symbol(SHANGHAI_EVM), smtlib(schedule_SHANGHAI)]
 // --------------------------------------------------------------------------------
    rule Gzero    < SHANGHAI > => 0
    
    rule Gbase    < SHANGHAI > => 2
    rule Gverylow < SHANGHAI > => 3
    rule Glow     < SHANGHAI > => 5
    rule Gmid     < SHANGHAI > => 8
    rule Ghigh    < SHANGHAI > => 10
   
    rule Gexp      < SHANGHAI > => 10
    rule Gexpbyte  < SHANGHAI > => 50
    rule Gsha3     < SHANGHAI > => 30
    rule Gsha3word < SHANGHAI > => 6

    rule Gsload       < SHANGHAI > => 100
    rule Gsstoreset   < SHANGHAI > => 20000
    rule Gsstorereset < SHANGHAI > => 2900
    rule Rsstoreclear < SHANGHAI > => 4800

    rule Glog      < SHANGHAI > => 375
    rule Glogdata  < SHANGHAI > => 8
    rule Glogtopic < SHANGHAI > => 375

    rule Gcall        < SHANGHAI > => 700
    rule Gcallstipend < SHANGHAI > => 2300
    rule Gcallvalue   < SHANGHAI > => 9000
    rule Gnewaccount  < SHANGHAI > => 25000

    rule Gcreate       < SHANGHAI > => 32000
    rule Gcodedeposit  < SHANGHAI > => 200
    rule Gselfdestruct < SHANGHAI > => 5000
    rule Rselfdestruct < SHANGHAI > => 0

    rule Gmemory      < SHANGHAI > => 3
    rule Gquadcoeff   < SHANGHAI > => 512
    rule Gcopy        < SHANGHAI > => 3
    rule Gquaddivisor < SHANGHAI > => 3

    rule Gtransaction   < SHANGHAI > => 21000
    rule Gtxcreate      < SHANGHAI > => 53000
    rule Gtxdatazero    < SHANGHAI > => 4
    rule Gtxdatanonzero < SHANGHAI > => 16

    rule Gjumpdest    < SHANGHAI > => 1
    rule Gbalance     < SHANGHAI > => 700
    rule Gblockhash   < SHANGHAI > => 20
    rule Gextcodesize < SHANGHAI > => 700
    rule Gextcodecopy < SHANGHAI > => 700

    rule Gecadd       < SHANGHAI > => 150
    rule Gecmul       < SHANGHAI > => 6000
    rule Gecpairconst < SHANGHAI > => 45000
    rule Gecpaircoeff < SHANGHAI > => 34000
    rule Gfround      < SHANGHAI > => 1

    rule maxCodeSize < SHANGHAI > => 24576
    rule Rb          < SHANGHAI > => 0

    rule Gcoldsload             < SHANGHAI > => 2100
    rule Gcoldaccountaccess     < SHANGHAI > => 2600
    rule Gwarmstorageread       < SHANGHAI > => 100
    rule Gwarmstoragedirtystore < SHANGHAI > => 0 

    rule Gaccessliststoragekey < SHANGHAI > => 1900
    rule Gaccesslistaddress    < SHANGHAI > => 2400

    rule maxInitCodeSize   < SHANGHAI > => 49152
    rule Ginitcodewordcost < SHANGHAI > => 2

    rule Rmaxquotient < SHANGHAI > => 5

    rule Gselfdestructnewaccount << SHANGHAI >> => true
    rule Gstaticcalldepth        << SHANGHAI >> => false
    rule Gemptyisnonexistent     << SHANGHAI >> => true
    rule Gzerovaluenewaccountgas << SHANGHAI >> => false
    rule Ghasrevert              << SHANGHAI >> => true
    rule Ghasreturndata          << SHANGHAI >> => true
    rule Ghasstaticcall          << SHANGHAI >> => true
    rule Ghasshift               << SHANGHAI >> => true
    rule Ghasdirtysstore         << SHANGHAI >> => true
    rule Ghassstorestipend       << SHANGHAI >> => true
    rule Ghascreate2             << SHANGHAI >> => true
    rule Ghasextcodehash         << SHANGHAI >> => true
    rule Ghasselfbalance         << SHANGHAI >> => true
    rule Ghaschainid             << SHANGHAI >> => true
    rule Ghasaccesslist          << SHANGHAI >> => true
    rule Ghasbasefee             << SHANGHAI >> => true
    rule Ghasrejectedfirstbyte   << SHANGHAI >> => true
    rule Ghasprevrandao          << SHANGHAI >> => true
    rule Ghasmaxinitcodesize     << SHANGHAI >> => true
    rule Ghaspushzero            << SHANGHAI >> => true
    rule Ghaswarmcoinbase        << SHANGHAI >> => true
    rule Ghastransient           << SHANGHAI >> => false
    rule Ghasmcopy               << SHANGHAI >> => false
    rule Ghasbeaconroot          << SHANGHAI >> => false
```

### Cancun Schedule

```k
    syntax Schedule ::= "CANCUN" [symbol(CANCUN_EVM), smtlib(schedule_CANCUN)]
 // --------------------------------------------------------------------------
    rule Gzero    < CANCUN > => 0
    
    rule Gbase    < CANCUN > => 2
    rule Gverylow < CANCUN > => 3
    rule Glow     < CANCUN > => 5
    rule Gmid     < CANCUN > => 8
    rule Ghigh    < CANCUN > => 10
   
    rule Gexp      < CANCUN > => 10
    rule Gexpbyte  < CANCUN > => 50
    rule Gsha3     < CANCUN > => 30
    rule Gsha3word < CANCUN > => 6

    rule Gsload       < CANCUN > => 100
    rule Gsstoreset   < CANCUN > => 20000
    rule Gsstorereset < CANCUN > => 2900
    rule Rsstoreclear < CANCUN > => 4800

    rule Glog      < CANCUN > => 375
    rule Glogdata  < CANCUN > => 8
    rule Glogtopic < CANCUN > => 375

    rule Gcall        < CANCUN > => 700
    rule Gcallstipend < CANCUN > => 2300
    rule Gcallvalue   < CANCUN > => 9000
    rule Gnewaccount  < CANCUN > => 25000

    rule Gcreate       < CANCUN > => 32000
    rule Gcodedeposit  < CANCUN > => 200
    rule Gselfdestruct < CANCUN > => 5000
    rule Rselfdestruct < CANCUN > => 0

    rule Gmemory      < CANCUN > => 3
    rule Gquadcoeff   < CANCUN > => 512
    rule Gcopy        < CANCUN > => 3
    rule Gquaddivisor < CANCUN > => 3

    rule Gtransaction   < CANCUN > => 21000
    rule Gtxcreate      < CANCUN > => 53000
    rule Gtxdatazero    < CANCUN > => 4
    rule Gtxdatanonzero < CANCUN > => 16

    rule Gjumpdest    < CANCUN > => 1
    rule Gbalance     < CANCUN > => 700
    rule Gblockhash   < CANCUN > => 20
    rule Gextcodesize < CANCUN > => 700
    rule Gextcodecopy < CANCUN > => 700

    rule Gecadd       < CANCUN > => 150
    rule Gecmul       < CANCUN > => 6000
    rule Gecpairconst < CANCUN > => 45000
    rule Gecpaircoeff < CANCUN > => 34000
    rule Gfround      < CANCUN > => 1

    rule maxCodeSize < CANCUN > => 24576
    rule Rb          < CANCUN > => 0

    rule Gcoldsload             < CANCUN > => 2100
    rule Gcoldaccountaccess     < CANCUN > => 2600
    rule Gwarmstorageread       < CANCUN > => 100
    rule Gwarmstoragedirtystore < DEFAULT > => 100

    rule Gaccessliststoragekey < CANCUN > => 1900
    rule Gaccesslistaddress    < CANCUN > => 2400

    rule maxInitCodeSize   < CANCUN > => 49152
    rule Ginitcodewordcost < CANCUN > => 2

    rule Rmaxquotient < CANCUN > => 5

    rule Gselfdestructnewaccount << CANCUN >> => true
    rule Gstaticcalldepth        << CANCUN >> => false
    rule Gemptyisnonexistent     << CANCUN >> => true
    rule Gzerovaluenewaccountgas << CANCUN >> => false
    rule Ghasrevert              << CANCUN >> => true
    rule Ghasreturndata          << CANCUN >> => true
    rule Ghasstaticcall          << CANCUN >> => true
    rule Ghasshift               << CANCUN >> => true
    rule Ghasdirtysstore         << CANCUN >> => true
    rule Ghassstorestipend       << CANCUN >> => true
    rule Ghascreate2             << CANCUN >> => true
    rule Ghasextcodehash         << CANCUN >> => true
    rule Ghasselfbalance         << CANCUN >> => true
    rule Ghaschainid             << CANCUN >> => true
    rule Ghasaccesslist          << CANCUN >> => true
    rule Ghasbasefee             << CANCUN >> => true
    rule Ghasrejectedfirstbyte   << CANCUN >> => true
    rule Ghasprevrandao          << CANCUN >> => true
    rule Ghasmaxinitcodesize     << CANCUN >> => true
    rule Ghaspushzero            << CANCUN >> => true
    rule Ghaswarmcoinbase        << CANCUN >> => true
    rule Ghastransient           << CANCUN >> => true
    rule Ghasmcopy               << CANCUN >> => true
    rule Ghasbeaconroot          << CANCUN >> => true

endmodule
```