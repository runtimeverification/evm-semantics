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

    syntax Schedule ::= getSchedule(Int) [function]
    rule getSchedule(0) => FRONTIER
    rule getSchedule(1) => HOMESTEAD
    rule getSchedule(2) => TANGERINE_WHISTLE
    rule getSchedule(3) => SPURIOUS_DRAGON
    rule getSchedule(4) => BYZANTIUM
    rule getSchedule(5) => CONSTANTINOPLE
    rule getSchedule(6) => PETERSBURG
    rule getSchedule(7) => ISTANBUL
    rule getSchedule(8) => BERLIN
    rule getSchedule(9) => LONDON
    rule getSchedule(10) => MERGE
    rule getSchedule(11) => SHANGHAI
    rule getSchedule(12) => CANCUN
    rule getSchedule(13) => PRAGUE
    rule getSchedule(100) => BEDROCK
    rule getSchedule(101) => REGOLITH
    rule getSchedule(102) => CANYON
    rule getSchedule(103) => ECOTONE
    rule getSchedule(104) => FJORD
    rule getSchedule(105) => GRANITE
    rule getSchedule(106) => HOLOCENE
    rule getSchedule(107) => ISTHMUS

    syntax Bool ::= ScheduleFlag "<<" Schedule ">>" [function, total]
 // -----------------------------------------------------------------

    syntax ScheduleFlag ::= "Gselfdestructnewaccount" | "Gstaticcalldepth" | "Gemptyisnonexistent" | "Gzerovaluenewaccountgas"
                          | "Ghasrevert"              | "Ghasreturndata"   | "Ghasstaticcall"      | "Ghasshift"
                          | "Ghasdirtysstore"         | "Ghascreate2"      | "Ghasextcodehash"     | "Ghasselfbalance"
                          | "Ghassstorestipend"       | "Ghaschainid"      | "Ghasaccesslist"      | "Ghasbasefee"
                          | "Ghasrejectedfirstbyte"   | "Ghasprevrandao"   | "Ghasmaxinitcodesize" | "Ghaspushzero"
                          | "Ghaswarmcoinbase"        | "Ghaswithdrawals"  | "Ghastransient"       | "Ghasmcopy"
                          | "Ghasbeaconroot"          | "Ghaseip6780"      | "Ghasblobbasefee"     | "Ghasblobhash"
                          | "Ghasbls12msmdiscount"    | "Ghasdelegation"
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
                           | "Gpointeval"    | "Gbls12g1add"   | "Gbls12g1mul"   | "Gbls12g2add"       | "Gbls12g2mul"        | "Gbls12PairingCheckMul"
                           | "Gbls12PairingCheckAdd"           | "Gbls12mapfptog1"                     | "Gbls12mapfp2tog2"
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
    rule Rb          < FRONTIER > => 5 *Int (10 ^Int 18)

    rule Gcoldsload             < FRONTIER > => 0
    rule Gcoldaccountaccess     < FRONTIER > => 0
    rule Gwarmstorageread       < FRONTIER > => 0
    rule Gwarmstoragedirtystore < FRONTIER > => 0

    rule Gpointeval < FRONTIER > => 0

    rule Gbls12g1add < FRONTIER > => 0
    rule Gbls12g1mul < FRONTIER > => 0
    rule Gbls12g2add < FRONTIER > => 0
    rule Gbls12g2mul < FRONTIER > => 0
    rule Gbls12PairingCheckMul < FRONTIER > => 0
    rule Gbls12PairingCheckAdd < FRONTIER > => 0
    rule Gbls12mapfptog1 < FRONTIER > => 0
    rule Gbls12mapfp2tog2 < FRONTIER > => 0

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
    rule Ghaswithdrawals         << FRONTIER >> => false
    rule Ghastransient           << FRONTIER >> => false
    rule Ghasmcopy               << FRONTIER >> => false
    rule Ghasbeaconroot          << FRONTIER >> => false
    rule Ghaseip6780             << FRONTIER >> => false
    rule Ghasblobbasefee         << FRONTIER >> => false
    rule Ghasblobhash            << FRONTIER >> => false
    rule Ghasbls12msmdiscount    << FRONTIER >> => false
    rule Ghasdelegation          << FRONTIER >> => false
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
    rule Rb          < HOMESTEAD > => 5 *Int (10 ^Int 18)

    rule Gcoldsload             < HOMESTEAD > => 0
    rule Gcoldaccountaccess     < HOMESTEAD > => 0
    rule Gwarmstorageread       < HOMESTEAD > => 0
    rule Gwarmstoragedirtystore < HOMESTEAD > => 0

    rule Gpointeval < HOMESTEAD > => 0

    rule Gbls12g1add < HOMESTEAD > => 0
    rule Gbls12g1mul < HOMESTEAD > => 0
    rule Gbls12g2add < HOMESTEAD > => 0
    rule Gbls12g2mul < HOMESTEAD > => 0
    rule Gbls12PairingCheckMul < HOMESTEAD > => 0
    rule Gbls12PairingCheckAdd < HOMESTEAD > => 0
    rule Gbls12mapfptog1 < HOMESTEAD > => 0
    rule Gbls12mapfp2tog2 < HOMESTEAD > => 0

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
    rule Ghaswithdrawals         << HOMESTEAD >> => false
    rule Ghastransient           << HOMESTEAD >> => false
    rule Ghasmcopy               << HOMESTEAD >> => false
    rule Ghasbeaconroot          << HOMESTEAD >> => false
    rule Ghaseip6780             << HOMESTEAD >> => false
    rule Ghasblobbasefee         << HOMESTEAD >> => false
    rule Ghasblobhash            << HOMESTEAD >> => false
    rule Ghasbls12msmdiscount    << HOMESTEAD >> => false
    rule Ghasdelegation          << HOMESTEAD >> => false
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
    rule Rb          < TANGERINE_WHISTLE > => 5 *Int (10 ^Int 18)

    rule Gcoldsload             < TANGERINE_WHISTLE > => 0
    rule Gcoldaccountaccess     < TANGERINE_WHISTLE > => 0
    rule Gwarmstorageread       < TANGERINE_WHISTLE > => 0
    rule Gwarmstoragedirtystore < TANGERINE_WHISTLE > => 0

    rule Gpointeval < TANGERINE_WHISTLE > => 0

    rule Gbls12g1add < TANGERINE_WHISTLE > => 0
    rule Gbls12g1mul < TANGERINE_WHISTLE > => 0
    rule Gbls12g2add < TANGERINE_WHISTLE > => 0
    rule Gbls12g2mul < TANGERINE_WHISTLE > => 0
    rule Gbls12PairingCheckMul < TANGERINE_WHISTLE > => 0
    rule Gbls12PairingCheckAdd < TANGERINE_WHISTLE > => 0
    rule Gbls12mapfptog1 < TANGERINE_WHISTLE > => 0
    rule Gbls12mapfp2tog2 < TANGERINE_WHISTLE > => 0

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
    rule Ghaswithdrawals         << TANGERINE_WHISTLE >> => false
    rule Ghastransient           << TANGERINE_WHISTLE >> => false
    rule Ghasmcopy               << TANGERINE_WHISTLE >> => false
    rule Ghasbeaconroot          << TANGERINE_WHISTLE >> => false
    rule Ghaseip6780             << TANGERINE_WHISTLE >> => false
    rule Ghasblobbasefee         << TANGERINE_WHISTLE >> => false
    rule Ghasblobhash            << TANGERINE_WHISTLE >> => false
    rule Ghasbls12msmdiscount    << TANGERINE_WHISTLE >> => false
    rule Ghasdelegation          << TANGERINE_WHISTLE >> => false
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
    rule Rb          < SPURIOUS_DRAGON > => 5 *Int (10 ^Int 18)

    rule Gcoldsload             < SPURIOUS_DRAGON > => 0
    rule Gcoldaccountaccess     < SPURIOUS_DRAGON > => 0
    rule Gwarmstorageread       < SPURIOUS_DRAGON > => 0
    rule Gwarmstoragedirtystore < SPURIOUS_DRAGON > => 0

    rule Gpointeval < SPURIOUS_DRAGON > => 0

    rule Gbls12g1add < SPURIOUS_DRAGON > => 0
    rule Gbls12g1mul < SPURIOUS_DRAGON > => 0
    rule Gbls12g2add < SPURIOUS_DRAGON > => 0
    rule Gbls12g2mul < SPURIOUS_DRAGON > => 0
    rule Gbls12PairingCheckMul < SPURIOUS_DRAGON > => 0
    rule Gbls12PairingCheckAdd < SPURIOUS_DRAGON > => 0
    rule Gbls12mapfptog1 < SPURIOUS_DRAGON > => 0
    rule Gbls12mapfp2tog2 < SPURIOUS_DRAGON > => 0

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
    rule Ghaswithdrawals         << SPURIOUS_DRAGON >> => false
    rule Ghastransient           << SPURIOUS_DRAGON >> => false
    rule Ghasmcopy               << SPURIOUS_DRAGON >> => false
    rule Ghasbeaconroot          << SPURIOUS_DRAGON >> => false
    rule Ghaseip6780             << SPURIOUS_DRAGON >> => false
    rule Ghasblobbasefee         << SPURIOUS_DRAGON >> => false
    rule Ghasblobhash            << SPURIOUS_DRAGON >> => false
    rule Ghasbls12msmdiscount    << SPURIOUS_DRAGON >> => false
    rule Ghasdelegation          << SPURIOUS_DRAGON >> => false
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

    rule Gpointeval < BYZANTIUM > => 0

    rule Gbls12g1add < BYZANTIUM > => 0
    rule Gbls12g1mul < BYZANTIUM > => 0
    rule Gbls12g2add < BYZANTIUM > => 0
    rule Gbls12g2mul < BYZANTIUM > => 0
    rule Gbls12PairingCheckMul < BYZANTIUM > => 0
    rule Gbls12PairingCheckAdd < BYZANTIUM > => 0
    rule Gbls12mapfptog1 < BYZANTIUM > => 0
    rule Gbls12mapfp2tog2 < BYZANTIUM > => 0

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
    rule Ghaswithdrawals         << BYZANTIUM >> => false
    rule Ghastransient           << BYZANTIUM >> => false
    rule Ghasmcopy               << BYZANTIUM >> => false
    rule Ghasbeaconroot          << BYZANTIUM >> => false
    rule Ghaseip6780             << BYZANTIUM >> => false
    rule Ghasblobbasefee         << BYZANTIUM >> => false
    rule Ghasblobhash            << BYZANTIUM >> => false
    rule Ghasbls12msmdiscount    << BYZANTIUM >> => false
    rule Ghasdelegation          << BYZANTIUM >> => false
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

    rule Gpointeval < CONSTANTINOPLE > => 0

    rule Gbls12g1add < CONSTANTINOPLE > => 0
    rule Gbls12g1mul < CONSTANTINOPLE > => 0
    rule Gbls12g2add < CONSTANTINOPLE > => 0
    rule Gbls12g2mul < CONSTANTINOPLE > => 0
    rule Gbls12PairingCheckMul < CONSTANTINOPLE > => 0
    rule Gbls12PairingCheckAdd < CONSTANTINOPLE > => 0
    rule Gbls12mapfptog1 < CONSTANTINOPLE > => 0
    rule Gbls12mapfp2tog2 < CONSTANTINOPLE > => 0

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
    rule Ghaswithdrawals         << CONSTANTINOPLE >> => false
    rule Ghastransient           << CONSTANTINOPLE >> => false
    rule Ghasmcopy               << CONSTANTINOPLE >> => false
    rule Ghasbeaconroot          << CONSTANTINOPLE >> => false
    rule Ghaseip6780             << CONSTANTINOPLE >> => false
    rule Ghasblobbasefee         << CONSTANTINOPLE >> => false
    rule Ghasblobhash            << CONSTANTINOPLE >> => false
    rule Ghasbls12msmdiscount    << CONSTANTINOPLE >> => false
    rule Ghasdelegation          << CONSTANTINOPLE >> => false
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

    rule Gpointeval < PETERSBURG > => 0

    rule Gbls12g1add < PETERSBURG > => 0
    rule Gbls12g1mul < PETERSBURG > => 0
    rule Gbls12g2add < PETERSBURG > => 0
    rule Gbls12g2mul < PETERSBURG > => 0
    rule Gbls12PairingCheckMul < PETERSBURG > => 0
    rule Gbls12PairingCheckAdd < PETERSBURG > => 0
    rule Gbls12mapfptog1 < PETERSBURG > => 0
    rule Gbls12mapfp2tog2 < PETERSBURG > => 0

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
    rule Ghaswithdrawals         << PETERSBURG >> => false
    rule Ghastransient           << PETERSBURG >> => false
    rule Ghasmcopy               << PETERSBURG >> => false
    rule Ghasbeaconroot          << PETERSBURG >> => false
    rule Ghaseip6780             << PETERSBURG >> => false
    rule Ghasblobbasefee         << PETERSBURG >> => false
    rule Ghasblobhash            << PETERSBURG >> => false
    rule Ghasbls12msmdiscount    << PETERSBURG >> => false
    rule Ghasdelegation          << PETERSBURG >> => false
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

    rule Gpointeval < ISTANBUL > => 0

    rule Gbls12g1add < ISTANBUL > => 0
    rule Gbls12g1mul < ISTANBUL > => 0
    rule Gbls12g2add < ISTANBUL > => 0
    rule Gbls12g2mul < ISTANBUL > => 0
    rule Gbls12PairingCheckMul < ISTANBUL > => 0
    rule Gbls12PairingCheckAdd < ISTANBUL > => 0
    rule Gbls12mapfptog1 < ISTANBUL > => 0
    rule Gbls12mapfp2tog2 < ISTANBUL > => 0

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
    rule Ghaswithdrawals         << ISTANBUL >> => false
    rule Ghastransient           << ISTANBUL >> => false
    rule Ghasmcopy               << ISTANBUL >> => false
    rule Ghasbeaconroot          << ISTANBUL >> => false
    rule Ghaseip6780             << ISTANBUL >> => false
    rule Ghasblobbasefee         << ISTANBUL >> => false
    rule Ghasblobhash            << ISTANBUL >> => false
    rule Ghasbls12msmdiscount    << ISTANBUL >> => false
    rule Ghasdelegation          << ISTANBUL >> => false
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

    rule Gpointeval < BERLIN > => 0

    rule Gbls12g1add < BERLIN > => 0
    rule Gbls12g1mul < BERLIN > => 0
    rule Gbls12g2add < BERLIN > => 0
    rule Gbls12g2mul < BERLIN > => 0
    rule Gbls12PairingCheckMul < BERLIN > => 0
    rule Gbls12PairingCheckAdd < BERLIN > => 0
    rule Gbls12mapfptog1 < BERLIN > => 0
    rule Gbls12mapfp2tog2 < BERLIN > => 0

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
    rule Ghaswithdrawals         << BERLIN >> => false
    rule Ghastransient           << BERLIN >> => false
    rule Ghasmcopy               << BERLIN >> => false
    rule Ghasbeaconroot          << BERLIN >> => false
    rule Ghaseip6780             << BERLIN >> => false
    rule Ghasblobbasefee         << BERLIN >> => false
    rule Ghasblobhash            << BERLIN >> => false
    rule Ghasbls12msmdiscount    << BERLIN >> => false
    rule Ghasdelegation          << BERLIN >> => false
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

    rule Gpointeval < LONDON > => 0

    rule Gbls12g1add < LONDON > => 0
    rule Gbls12g1mul < LONDON > => 0
    rule Gbls12g2add < LONDON > => 0
    rule Gbls12g2mul < LONDON > => 0
    rule Gbls12PairingCheckMul < LONDON > => 0
    rule Gbls12PairingCheckAdd < LONDON > => 0
    rule Gbls12mapfptog1 < LONDON > => 0
    rule Gbls12mapfp2tog2 < LONDON > => 0

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
    rule Ghaswithdrawals         << LONDON >> => false
    rule Ghastransient           << LONDON >> => false
    rule Ghasmcopy               << LONDON >> => false
    rule Ghasbeaconroot          << LONDON >> => false
    rule Ghaseip6780             << LONDON >> => false
    rule Ghasblobbasefee         << LONDON >> => false
    rule Ghasblobhash            << LONDON >> => false
    rule Ghasbls12msmdiscount    << LONDON >> => false
    rule Ghasdelegation          << LONDON >> => false
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

    rule Gpointeval < MERGE > => 0

    rule Gbls12g1add < MERGE > => 0
    rule Gbls12g1mul < MERGE > => 0
    rule Gbls12g2add < MERGE > => 0
    rule Gbls12g2mul < MERGE > => 0
    rule Gbls12PairingCheckMul < MERGE > => 0
    rule Gbls12PairingCheckAdd < MERGE > => 0
    rule Gbls12mapfptog1 < MERGE > => 0
    rule Gbls12mapfp2tog2 < MERGE > => 0

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
    rule Ghaswithdrawals         << MERGE >> => false
    rule Ghastransient           << MERGE >> => false
    rule Ghasmcopy               << MERGE >> => false
    rule Ghasbeaconroot          << MERGE >> => false
    rule Ghaseip6780             << MERGE >> => false
    rule Ghasblobbasefee         << MERGE >> => false
    rule Ghasblobhash            << MERGE >> => false
    rule Ghasbls12msmdiscount    << MERGE >> => false
    rule Ghasdelegation          << MERGE >> => false
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

    rule Gpointeval < SHANGHAI > => 0

    rule Gbls12g1add < SHANGHAI > => 0
    rule Gbls12g1mul < SHANGHAI > => 0
    rule Gbls12g2add < SHANGHAI > => 0
    rule Gbls12g2mul < SHANGHAI > => 0
    rule Gbls12PairingCheckMul < SHANGHAI > => 0
    rule Gbls12PairingCheckAdd < SHANGHAI > => 0
    rule Gbls12mapfptog1 < SHANGHAI > => 0
    rule Gbls12mapfp2tog2 < SHANGHAI > => 0

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
    rule Ghaswithdrawals         << SHANGHAI >> => true
    rule Ghastransient           << SHANGHAI >> => false
    rule Ghasmcopy               << SHANGHAI >> => false
    rule Ghasbeaconroot          << SHANGHAI >> => false
    rule Ghaseip6780             << SHANGHAI >> => false
    rule Ghasblobbasefee         << SHANGHAI >> => false
    rule Ghasblobhash            << SHANGHAI >> => false
    rule Ghasbls12msmdiscount    << SHANGHAI >> => false
    rule Ghasdelegation          << SHANGHAI >> => false
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
    rule Gwarmstoragedirtystore < CANCUN > => 100

    rule Gpointeval < CANCUN > => 50000

    rule Gbls12g1add < CANCUN > => 0
    rule Gbls12g1mul < CANCUN > => 0
    rule Gbls12g2add < CANCUN > => 0
    rule Gbls12g2mul < CANCUN > => 0
    rule Gbls12PairingCheckMul < CANCUN > => 0
    rule Gbls12PairingCheckAdd < CANCUN > => 0
    rule Gbls12mapfptog1 < CANCUN > => 0
    rule Gbls12mapfp2tog2 < CANCUN > => 0

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
    rule Ghaswithdrawals         << CANCUN >> => true
    rule Ghastransient           << CANCUN >> => true
    rule Ghasmcopy               << CANCUN >> => true
    rule Ghasbeaconroot          << CANCUN >> => true
    rule Ghaseip6780             << CANCUN >> => true
    rule Ghasblobbasefee         << CANCUN >> => true
    rule Ghasblobhash            << CANCUN >> => true
    rule Ghasbls12msmdiscount    << CANCUN >> => false
    rule Ghasdelegation          << CANCUN >> => false
```

### Prague Schedule

```k
    syntax Schedule ::= "PRAGUE" [symbol(PRAGUE_EVM), smtlib(schedule_PRAGUE)]
 // --------------------------------------------------------------------------

    rule Gzero    < PRAGUE > => 0

    rule Gbase    < PRAGUE > => 2
    rule Gverylow < PRAGUE > => 3
    rule Glow     < PRAGUE > => 5
    rule Gmid     < PRAGUE > => 8
    rule Ghigh    < PRAGUE > => 10

    rule Gexp      < PRAGUE > => 10
    rule Gexpbyte  < PRAGUE > => 50
    rule Gsha3     < PRAGUE > => 30
    rule Gsha3word < PRAGUE > => 6

    rule Gsload       < PRAGUE > => 100
    rule Gsstoreset   < PRAGUE > => 20000
    rule Gsstorereset < PRAGUE > => 2900
    rule Rsstoreclear < PRAGUE > => 4800

    rule Glog      < PRAGUE > => 375
    rule Glogdata  < PRAGUE > => 8
    rule Glogtopic < PRAGUE > => 375

    rule Gcall        < PRAGUE > => 700
    rule Gcallstipend < PRAGUE > => 2300
    rule Gcallvalue   < PRAGUE > => 9000
    rule Gnewaccount  < PRAGUE > => 25000

    rule Gcreate       < PRAGUE > => 32000
    rule Gcodedeposit  < PRAGUE > => 200
    rule Gselfdestruct < PRAGUE > => 5000
    rule Rselfdestruct < PRAGUE > => 0

    rule Gmemory      < PRAGUE > => 3
    rule Gquadcoeff   < PRAGUE > => 512
    rule Gcopy        < PRAGUE > => 3
    rule Gquaddivisor < PRAGUE > => 3

    rule Gtransaction   < PRAGUE > => 21000
    rule Gtxcreate      < PRAGUE > => 53000
    rule Gtxdatazero    < PRAGUE > => 4
    rule Gtxdatanonzero < PRAGUE > => 16

    rule Gjumpdest    < PRAGUE > => 1
    rule Gbalance     < PRAGUE > => 700
    rule Gblockhash   < PRAGUE > => 20
    rule Gextcodesize < PRAGUE > => 700
    rule Gextcodecopy < PRAGUE > => 700

    rule Gecadd       < PRAGUE > => 150
    rule Gecmul       < PRAGUE > => 6000
    rule Gecpairconst < PRAGUE > => 45000
    rule Gecpaircoeff < PRAGUE > => 34000
    rule Gfround      < PRAGUE > => 1

    rule maxCodeSize < PRAGUE > => 24576
    rule Rb          < PRAGUE > => 0

    rule Gcoldsload             < PRAGUE > => 2100
    rule Gcoldaccountaccess     < PRAGUE > => 2600
    rule Gwarmstorageread       < PRAGUE > => 100
    rule Gwarmstoragedirtystore < PRAGUE > => 100

    rule Gpointeval < PRAGUE > => 50000

    rule Gbls12g1add < PRAGUE > => 375
    rule Gbls12g1mul < PRAGUE > => 12000
    rule Gbls12g2add < PRAGUE > => 600
    rule Gbls12g2mul < PRAGUE > => 22500
    rule Gbls12PairingCheckMul < PRAGUE > => 32600
    rule Gbls12PairingCheckAdd < PRAGUE > => 37700
    rule Gbls12mapfptog1 < PRAGUE > => 5500
    rule Gbls12mapfp2tog2 < PRAGUE > => 23800

    rule Gaccessliststoragekey < PRAGUE > => 1900
    rule Gaccesslistaddress    < PRAGUE > => 2400

    rule maxInitCodeSize   < PRAGUE > => 49152
    rule Ginitcodewordcost < PRAGUE > => 2

    rule Rmaxquotient < PRAGUE > => 5

    rule Gselfdestructnewaccount << PRAGUE >> => true
    rule Gstaticcalldepth        << PRAGUE >> => false
    rule Gemptyisnonexistent     << PRAGUE >> => true
    rule Gzerovaluenewaccountgas << PRAGUE >> => false
    rule Ghasrevert              << PRAGUE >> => true
    rule Ghasreturndata          << PRAGUE >> => true
    rule Ghasstaticcall          << PRAGUE >> => true
    rule Ghasshift               << PRAGUE >> => true
    rule Ghasdirtysstore         << PRAGUE >> => true
    rule Ghassstorestipend       << PRAGUE >> => true
    rule Ghascreate2             << PRAGUE >> => true
    rule Ghasextcodehash         << PRAGUE >> => true
    rule Ghasselfbalance         << PRAGUE >> => true
    rule Ghaschainid             << PRAGUE >> => true
    rule Ghasaccesslist          << PRAGUE >> => true
    rule Ghasbasefee             << PRAGUE >> => true
    rule Ghasrejectedfirstbyte   << PRAGUE >> => true
    rule Ghasprevrandao          << PRAGUE >> => true
    rule Ghasmaxinitcodesize     << PRAGUE >> => true
    rule Ghaspushzero            << PRAGUE >> => true
    rule Ghaswarmcoinbase        << PRAGUE >> => true
    rule Ghaswithdrawals         << PRAGUE >> => true
    rule Ghastransient           << PRAGUE >> => true
    rule Ghasmcopy               << PRAGUE >> => true
    rule Ghasbeaconroot          << PRAGUE >> => true
    rule Ghaseip6780             << PRAGUE >> => true
    rule Ghasblobbasefee         << PRAGUE >> => true
    rule Ghasblobhash            << PRAGUE >> => true
    rule Ghasbls12msmdiscount    << PRAGUE >> => true
    rule Ghasdelegation          << PRAGUE >> => true
```

### Bedrock Schedule

```k
    syntax Schedule ::= "BEDROCK" [symbol(BEDROCK_EVM), smtlib(schedule_BEDROCK)]
 // -----------------------------------------------------------------------------
    rule Gzero    < BEDROCK > => 0
    rule Gbase    < BEDROCK > => 2
    rule Gverylow < BEDROCK > => 3
    rule Glow     < BEDROCK > => 5
    rule Gmid     < BEDROCK > => 8
    rule Ghigh    < BEDROCK > => 10

    rule Gexp      < BEDROCK > => 10
    rule Gexpbyte  < BEDROCK > => 50
    rule Gsha3     < BEDROCK > => 30
    rule Gsha3word < BEDROCK > => 6

    rule Gsload       < BEDROCK > => 100
    rule Gsstoreset   < BEDROCK > => 20000
    rule Gsstorereset < BEDROCK > => 2900
    rule Rsstoreclear < BEDROCK > => 4800

    rule Glog      < BEDROCK > => 375
    rule Glogdata  < BEDROCK > => 8
    rule Glogtopic < BEDROCK > => 375

    rule Gcall        < BEDROCK > => 700
    rule Gcallstipend < BEDROCK > => 2300
    rule Gcallvalue   < BEDROCK > => 9000
    rule Gnewaccount  < BEDROCK > => 25000

    rule Gcreate       < BEDROCK > => 32000
    rule Gcodedeposit  < BEDROCK > => 200
    rule Gselfdestruct < BEDROCK > => 5000
    rule Rselfdestruct < BEDROCK > => 0

    rule Gmemory      < BEDROCK > => 3
    rule Gquadcoeff   < BEDROCK > => 512
    rule Gcopy        < BEDROCK > => 3
    rule Gquaddivisor < BEDROCK > => 3

    rule Gtransaction   < BEDROCK > => 21000
    rule Gtxcreate      < BEDROCK > => 53000
    rule Gtxdatazero    < BEDROCK > => 4
    rule Gtxdatanonzero < BEDROCK > => 16

    rule Gjumpdest    < BEDROCK > => 1
    rule Gbalance     < BEDROCK > => 700
    rule Gblockhash   < BEDROCK > => 20
    rule Gextcodesize < BEDROCK > => 700
    rule Gextcodecopy < BEDROCK > => 700

    rule Gecadd       < BEDROCK > => 150
    rule Gecmul       < BEDROCK > => 6000
    rule Gecpairconst < BEDROCK > => 45000
    rule Gecpaircoeff < BEDROCK > => 34000
    rule Gfround      < BEDROCK > => 1

    rule maxCodeSize < BEDROCK > => 24576
    rule Rb          < BEDROCK > => 0

    rule Gcoldsload             < BEDROCK > => 2100
    rule Gcoldaccountaccess     < BEDROCK > => 2600
    rule Gwarmstorageread       < BEDROCK > => 100
    rule Gwarmstoragedirtystore < BEDROCK > => 0

    rule Gpointeval < BEDROCK > => 0

    rule Gbls12g1add < BEDROCK > => 0
    rule Gbls12g1mul < BEDROCK > => 0
    rule Gbls12g2add < BEDROCK > => 0
    rule Gbls12g2mul < BEDROCK > => 0
    rule Gbls12PairingCheckMul < BEDROCK > => 0
    rule Gbls12PairingCheckAdd < BEDROCK > => 0
    rule Gbls12mapfptog1 < BEDROCK > => 0
    rule Gbls12mapfp2tog2 < BEDROCK > => 0

    rule Gaccessliststoragekey < BEDROCK > => 1900
    rule Gaccesslistaddress    < BEDROCK > => 2400

    rule maxInitCodeSize   < BEDROCK > => 0
    rule Ginitcodewordcost < BEDROCK > => 0

    rule Rmaxquotient < BEDROCK > => 5

    rule Gselfdestructnewaccount << BEDROCK >> => true
    rule Gstaticcalldepth        << BEDROCK >> => false
    rule Gemptyisnonexistent     << BEDROCK >> => true
    rule Gzerovaluenewaccountgas << BEDROCK >> => false
    rule Ghasrevert              << BEDROCK >> => true
    rule Ghasreturndata          << BEDROCK >> => true
    rule Ghasstaticcall          << BEDROCK >> => true
    rule Ghasshift               << BEDROCK >> => true
    rule Ghasdirtysstore         << BEDROCK >> => true
    rule Ghassstorestipend       << BEDROCK >> => true
    rule Ghascreate2             << BEDROCK >> => true
    rule Ghasextcodehash         << BEDROCK >> => true
    rule Ghasselfbalance         << BEDROCK >> => true
    rule Ghaschainid             << BEDROCK >> => true
    rule Ghasaccesslist          << BEDROCK >> => true
    rule Ghasbasefee             << BEDROCK >> => true
    rule Ghasrejectedfirstbyte   << BEDROCK >> => true
    rule Ghasprevrandao          << BEDROCK >> => true
    rule Ghasmaxinitcodesize     << BEDROCK >> => false
    rule Ghaspushzero            << BEDROCK >> => false
    rule Ghaswarmcoinbase        << BEDROCK >> => false
    rule Ghaswithdrawals         << BEDROCK >> => false
    rule Ghastransient           << BEDROCK >> => false
    rule Ghasmcopy               << BEDROCK >> => false
    rule Ghasbeaconroot          << BEDROCK >> => false
    rule Ghaseip6780             << BEDROCK >> => false
    rule Ghasblobbasefee         << BEDROCK >> => false
    rule Ghasblobhash            << BEDROCK >> => false
    rule Ghasbls12msmdiscount    << BEDROCK >> => false
    rule Ghasdelegation          << BEDROCK >> => false
```

### Regolith Schedule

```k
    syntax Schedule ::= "REGOLITH" [symbol(REGOLITH_EVM), smtlib(schedule_REGOLITH)]
 // --------------------------------------------------------------------------------
    rule Gzero    < REGOLITH > => 0
    rule Gbase    < REGOLITH > => 2
    rule Gverylow < REGOLITH > => 3
    rule Glow     < REGOLITH > => 5
    rule Gmid     < REGOLITH > => 8
    rule Ghigh    < REGOLITH > => 10

    rule Gexp      < REGOLITH > => 10
    rule Gexpbyte  < REGOLITH > => 50
    rule Gsha3     < REGOLITH > => 30
    rule Gsha3word < REGOLITH > => 6

    rule Gsload       < REGOLITH > => 100
    rule Gsstoreset   < REGOLITH > => 20000
    rule Gsstorereset < REGOLITH > => 2900
    rule Rsstoreclear < REGOLITH > => 4800

    rule Glog      < REGOLITH > => 375
    rule Glogdata  < REGOLITH > => 8
    rule Glogtopic < REGOLITH > => 375

    rule Gcall        < REGOLITH > => 700
    rule Gcallstipend < REGOLITH > => 2300
    rule Gcallvalue   < REGOLITH > => 9000
    rule Gnewaccount  < REGOLITH > => 25000

    rule Gcreate       < REGOLITH > => 32000
    rule Gcodedeposit  < REGOLITH > => 200
    rule Gselfdestruct < REGOLITH > => 5000
    rule Rselfdestruct < REGOLITH > => 0

    rule Gmemory      < REGOLITH > => 3
    rule Gquadcoeff   < REGOLITH > => 512
    rule Gcopy        < REGOLITH > => 3
    rule Gquaddivisor < REGOLITH > => 3

    rule Gtransaction   < REGOLITH > => 21000
    rule Gtxcreate      < REGOLITH > => 53000
    rule Gtxdatazero    < REGOLITH > => 4
    rule Gtxdatanonzero < REGOLITH > => 16

    rule Gjumpdest    < REGOLITH > => 1
    rule Gbalance     < REGOLITH > => 700
    rule Gblockhash   < REGOLITH > => 20
    rule Gextcodesize < REGOLITH > => 700
    rule Gextcodecopy < REGOLITH > => 700

    rule Gecadd       < REGOLITH > => 150
    rule Gecmul       < REGOLITH > => 6000
    rule Gecpairconst < REGOLITH > => 45000
    rule Gecpaircoeff < REGOLITH > => 34000
    rule Gfround      < REGOLITH > => 1

    rule maxCodeSize < REGOLITH > => 24576
    rule Rb          < REGOLITH > => 0

    rule Gcoldsload             < REGOLITH > => 2100
    rule Gcoldaccountaccess     < REGOLITH > => 2600
    rule Gwarmstorageread       < REGOLITH > => 100
    rule Gwarmstoragedirtystore < REGOLITH > => 0

    rule Gpointeval < REGOLITH > => 0

    rule Gbls12g1add < REGOLITH > => 0
    rule Gbls12g1mul < REGOLITH > => 0
    rule Gbls12g2add < REGOLITH > => 0
    rule Gbls12g2mul < REGOLITH > => 0
    rule Gbls12PairingCheckMul < REGOLITH > => 0
    rule Gbls12PairingCheckAdd < REGOLITH > => 0
    rule Gbls12mapfptog1 < REGOLITH > => 0
    rule Gbls12mapfp2tog2 < REGOLITH > => 0

    rule Gaccessliststoragekey < REGOLITH > => 1900
    rule Gaccesslistaddress    < REGOLITH > => 2400

    rule maxInitCodeSize   < REGOLITH > => 0
    rule Ginitcodewordcost < REGOLITH > => 0

    rule Rmaxquotient < REGOLITH > => 5

    rule Gselfdestructnewaccount << REGOLITH >> => true
    rule Gstaticcalldepth        << REGOLITH >> => false
    rule Gemptyisnonexistent     << REGOLITH >> => true
    rule Gzerovaluenewaccountgas << REGOLITH >> => false
    rule Ghasrevert              << REGOLITH >> => true
    rule Ghasreturndata          << REGOLITH >> => true
    rule Ghasstaticcall          << REGOLITH >> => true
    rule Ghasshift               << REGOLITH >> => true
    rule Ghasdirtysstore         << REGOLITH >> => true
    rule Ghassstorestipend       << REGOLITH >> => true
    rule Ghascreate2             << REGOLITH >> => true
    rule Ghasextcodehash         << REGOLITH >> => true
    rule Ghasselfbalance         << REGOLITH >> => true
    rule Ghaschainid             << REGOLITH >> => true
    rule Ghasaccesslist          << REGOLITH >> => true
    rule Ghasbasefee             << REGOLITH >> => true
    rule Ghasrejectedfirstbyte   << REGOLITH >> => true
    rule Ghasprevrandao          << REGOLITH >> => true
    rule Ghasmaxinitcodesize     << REGOLITH >> => false
    rule Ghaspushzero            << REGOLITH >> => false
    rule Ghaswarmcoinbase        << REGOLITH >> => false
    rule Ghaswithdrawals         << REGOLITH >> => false
    rule Ghastransient           << REGOLITH >> => false
    rule Ghasmcopy               << REGOLITH >> => false
    rule Ghasbeaconroot          << REGOLITH >> => false
    rule Ghaseip6780             << REGOLITH >> => false
    rule Ghasblobbasefee         << REGOLITH >> => false
    rule Ghasblobhash            << REGOLITH >> => false
    rule Ghasbls12msmdiscount    << REGOLITH >> => false
    rule Ghasdelegation          << REGOLITH >> => false
```

### Canyon Schedule

```k
    syntax Schedule ::= "CANYON" [symbol(CANYON_EVM), smtlib(schedule_CANYON)]
 // --------------------------------------------------------------------------
    rule Gzero    < CANYON > => 0

    rule Gbase    < CANYON > => 2
    rule Gverylow < CANYON > => 3
    rule Glow     < CANYON > => 5
    rule Gmid     < CANYON > => 8
    rule Ghigh    < CANYON > => 10

    rule Gexp      < CANYON > => 10
    rule Gexpbyte  < CANYON > => 50
    rule Gsha3     < CANYON > => 30
    rule Gsha3word < CANYON > => 6

    rule Gsload       < CANYON > => 100
    rule Gsstoreset   < CANYON > => 20000
    rule Gsstorereset < CANYON > => 2900
    rule Rsstoreclear < CANYON > => 4800

    rule Glog      < CANYON > => 375
    rule Glogdata  < CANYON > => 8
    rule Glogtopic < CANYON > => 375

    rule Gcall        < CANYON > => 700
    rule Gcallstipend < CANYON > => 2300
    rule Gcallvalue   < CANYON > => 9000
    rule Gnewaccount  < CANYON > => 25000

    rule Gcreate       < CANYON > => 32000
    rule Gcodedeposit  < CANYON > => 200
    rule Gselfdestruct < CANYON > => 5000
    rule Rselfdestruct < CANYON > => 0

    rule Gmemory      < CANYON > => 3
    rule Gquadcoeff   < CANYON > => 512
    rule Gcopy        < CANYON > => 3
    rule Gquaddivisor < CANYON > => 3

    rule Gtransaction   < CANYON > => 21000
    rule Gtxcreate      < CANYON > => 53000
    rule Gtxdatazero    < CANYON > => 4
    rule Gtxdatanonzero < CANYON > => 16

    rule Gjumpdest    < CANYON > => 1
    rule Gbalance     < CANYON > => 700
    rule Gblockhash   < CANYON > => 20
    rule Gextcodesize < CANYON > => 700
    rule Gextcodecopy < CANYON > => 700

    rule Gecadd       < CANYON > => 150
    rule Gecmul       < CANYON > => 6000
    rule Gecpairconst < CANYON > => 45000
    rule Gecpaircoeff < CANYON > => 34000
    rule Gfround      < CANYON > => 1

    rule maxCodeSize < CANYON > => 24576
    rule Rb          < CANYON > => 0

    rule Gcoldsload             < CANYON > => 2100
    rule Gcoldaccountaccess     < CANYON > => 2600
    rule Gwarmstorageread       < CANYON > => 100
    rule Gwarmstoragedirtystore < CANYON > => 0

    rule Gpointeval < CANYON > => 0

    rule Gbls12g1add < CANYON > => 0
    rule Gbls12g1mul < CANYON > => 0
    rule Gbls12g2add < CANYON > => 0
    rule Gbls12g2mul < CANYON > => 0
    rule Gbls12PairingCheckMul < CANYON > => 0
    rule Gbls12PairingCheckAdd < CANYON > => 0
    rule Gbls12mapfptog1 < CANYON > => 0
    rule Gbls12mapfp2tog2 < CANYON > => 0

    rule Gaccessliststoragekey < CANYON > => 1900
    rule Gaccesslistaddress    < CANYON > => 2400

    rule maxInitCodeSize   < CANYON > => 49152
    rule Ginitcodewordcost < CANYON > => 2

    rule Rmaxquotient < CANYON > => 5

    rule Gselfdestructnewaccount << CANYON >> => true
    rule Gstaticcalldepth        << CANYON >> => false
    rule Gemptyisnonexistent     << CANYON >> => true
    rule Gzerovaluenewaccountgas << CANYON >> => false
    rule Ghasrevert              << CANYON >> => true
    rule Ghasreturndata          << CANYON >> => true
    rule Ghasstaticcall          << CANYON >> => true
    rule Ghasshift               << CANYON >> => true
    rule Ghasdirtysstore         << CANYON >> => true
    rule Ghassstorestipend       << CANYON >> => true
    rule Ghascreate2             << CANYON >> => true
    rule Ghasextcodehash         << CANYON >> => true
    rule Ghasselfbalance         << CANYON >> => true
    rule Ghaschainid             << CANYON >> => true
    rule Ghasaccesslist          << CANYON >> => true
    rule Ghasbasefee             << CANYON >> => true
    rule Ghasrejectedfirstbyte   << CANYON >> => true
    rule Ghasprevrandao          << CANYON >> => true
    rule Ghasmaxinitcodesize     << CANYON >> => true
    rule Ghaspushzero            << CANYON >> => true
    rule Ghaswarmcoinbase        << CANYON >> => true
    rule Ghaswithdrawals         << CANYON >> => true
    rule Ghastransient           << CANYON >> => false
    rule Ghasmcopy               << CANYON >> => false
    rule Ghasbeaconroot          << CANYON >> => false
    rule Ghaseip6780             << CANYON >> => false
    rule Ghasblobbasefee         << CANYON >> => false
    rule Ghasblobhash            << CANYON >> => false
    rule Ghasbls12msmdiscount    << CANYON >> => false
    rule Ghasdelegation          << CANYON >> => false
```

### Ecotone Schedule

```k
    syntax Schedule ::= "ECOTONE" [symbol(ECOTONE_EVM), smtlib(schedule_ECOTONE)]
 // -----------------------------------------------------------------------------
    rule Gzero    < ECOTONE > => 0

    rule Gbase    < ECOTONE > => 2
    rule Gverylow < ECOTONE > => 3
    rule Glow     < ECOTONE > => 5
    rule Gmid     < ECOTONE > => 8
    rule Ghigh    < ECOTONE > => 10

    rule Gexp      < ECOTONE > => 10
    rule Gexpbyte  < ECOTONE > => 50
    rule Gsha3     < ECOTONE > => 30
    rule Gsha3word < ECOTONE > => 6

    rule Gsload       < ECOTONE > => 100
    rule Gsstoreset   < ECOTONE > => 20000
    rule Gsstorereset < ECOTONE > => 2900
    rule Rsstoreclear < ECOTONE > => 4800

    rule Glog      < ECOTONE > => 375
    rule Glogdata  < ECOTONE > => 8
    rule Glogtopic < ECOTONE > => 375

    rule Gcall        < ECOTONE > => 700
    rule Gcallstipend < ECOTONE > => 2300
    rule Gcallvalue   < ECOTONE > => 9000
    rule Gnewaccount  < ECOTONE > => 25000

    rule Gcreate       < ECOTONE > => 32000
    rule Gcodedeposit  < ECOTONE > => 200
    rule Gselfdestruct < ECOTONE > => 5000
    rule Rselfdestruct < ECOTONE > => 0

    rule Gmemory      < ECOTONE > => 3
    rule Gquadcoeff   < ECOTONE > => 512
    rule Gcopy        < ECOTONE > => 3
    rule Gquaddivisor < ECOTONE > => 3

    rule Gtransaction   < ECOTONE > => 21000
    rule Gtxcreate      < ECOTONE > => 53000
    rule Gtxdatazero    < ECOTONE > => 4
    rule Gtxdatanonzero < ECOTONE > => 16

    rule Gjumpdest    < ECOTONE > => 1
    rule Gbalance     < ECOTONE > => 700
    rule Gblockhash   < ECOTONE > => 20
    rule Gextcodesize < ECOTONE > => 700
    rule Gextcodecopy < ECOTONE > => 700

    rule Gecadd       < ECOTONE > => 150
    rule Gecmul       < ECOTONE > => 6000
    rule Gecpairconst < ECOTONE > => 45000
    rule Gecpaircoeff < ECOTONE > => 34000
    rule Gfround      < ECOTONE > => 1

    rule maxCodeSize < ECOTONE > => 24576
    rule Rb          < ECOTONE > => 0

    rule Gcoldsload             < ECOTONE > => 2100
    rule Gcoldaccountaccess     < ECOTONE > => 2600
    rule Gwarmstorageread       < ECOTONE > => 100
    rule Gwarmstoragedirtystore < ECOTONE > => 100

    rule Gpointeval < ECOTONE > => 50000

    rule Gbls12g1add < ECOTONE > => 0
    rule Gbls12g1mul < ECOTONE > => 0
    rule Gbls12g2add < ECOTONE > => 0
    rule Gbls12g2mul < ECOTONE > => 0
    rule Gbls12PairingCheckMul < ECOTONE > => 0
    rule Gbls12PairingCheckAdd < ECOTONE > => 0
    rule Gbls12mapfptog1 < ECOTONE > => 0
    rule Gbls12mapfp2tog2 < ECOTONE > => 0

    rule Gaccessliststoragekey < ECOTONE > => 1900
    rule Gaccesslistaddress    < ECOTONE > => 2400

    rule maxInitCodeSize   < ECOTONE > => 49152
    rule Ginitcodewordcost < ECOTONE > => 2

    rule Rmaxquotient < ECOTONE > => 5

    rule Gselfdestructnewaccount << ECOTONE >> => true
    rule Gstaticcalldepth        << ECOTONE >> => false
    rule Gemptyisnonexistent     << ECOTONE >> => true
    rule Gzerovaluenewaccountgas << ECOTONE >> => false
    rule Ghasrevert              << ECOTONE >> => true
    rule Ghasreturndata          << ECOTONE >> => true
    rule Ghasstaticcall          << ECOTONE >> => true
    rule Ghasshift               << ECOTONE >> => true
    rule Ghasdirtysstore         << ECOTONE >> => true
    rule Ghassstorestipend       << ECOTONE >> => true
    rule Ghascreate2             << ECOTONE >> => true
    rule Ghasextcodehash         << ECOTONE >> => true
    rule Ghasselfbalance         << ECOTONE >> => true
    rule Ghaschainid             << ECOTONE >> => true
    rule Ghasaccesslist          << ECOTONE >> => true
    rule Ghasbasefee             << ECOTONE >> => true
    rule Ghasrejectedfirstbyte   << ECOTONE >> => true
    rule Ghasprevrandao          << ECOTONE >> => true
    rule Ghasmaxinitcodesize     << ECOTONE >> => true
    rule Ghaspushzero            << ECOTONE >> => true
    rule Ghaswarmcoinbase        << ECOTONE >> => true
    rule Ghaswithdrawals         << ECOTONE >> => true
    rule Ghastransient           << ECOTONE >> => true
    rule Ghasmcopy               << ECOTONE >> => true
    rule Ghasbeaconroot          << ECOTONE >> => true
    rule Ghaseip6780             << ECOTONE >> => true
    rule Ghasblobbasefee         << ECOTONE >> => true
    rule Ghasblobhash            << ECOTONE >> => true
    rule Ghasbls12msmdiscount    << ECOTONE >> => false
    rule Ghasdelegation          << ECOTONE >> => false
```

### Fjord Schedule

```k
    syntax Schedule ::= "FJORD" [symbol(FJORD_EVM), smtlib(schedule_FJORD)]
 // -----------------------------------------------------------------------
    rule Gzero    < FJORD > => 0

    rule Gbase    < FJORD > => 2
    rule Gverylow < FJORD > => 3
    rule Glow     < FJORD > => 5
    rule Gmid     < FJORD > => 8
    rule Ghigh    < FJORD > => 10

    rule Gexp      < FJORD > => 10
    rule Gexpbyte  < FJORD > => 50
    rule Gsha3     < FJORD > => 30
    rule Gsha3word < FJORD > => 6

    rule Gsload       < FJORD > => 100
    rule Gsstoreset   < FJORD > => 20000
    rule Gsstorereset < FJORD > => 2900
    rule Rsstoreclear < FJORD > => 4800

    rule Glog      < FJORD > => 375
    rule Glogdata  < FJORD > => 8
    rule Glogtopic < FJORD > => 375

    rule Gcall        < FJORD > => 700
    rule Gcallstipend < FJORD > => 2300
    rule Gcallvalue   < FJORD > => 9000
    rule Gnewaccount  < FJORD > => 25000

    rule Gcreate       < FJORD > => 32000
    rule Gcodedeposit  < FJORD > => 200
    rule Gselfdestruct < FJORD > => 5000
    rule Rselfdestruct < FJORD > => 0

    rule Gmemory      < FJORD > => 3
    rule Gquadcoeff   < FJORD > => 512
    rule Gcopy        < FJORD > => 3
    rule Gquaddivisor < FJORD > => 3

    rule Gtransaction   < FJORD > => 21000
    rule Gtxcreate      < FJORD > => 53000
    rule Gtxdatazero    < FJORD > => 4
    rule Gtxdatanonzero < FJORD > => 16

    rule Gjumpdest    < FJORD > => 1
    rule Gbalance     < FJORD > => 700
    rule Gblockhash   < FJORD > => 20
    rule Gextcodesize < FJORD > => 700
    rule Gextcodecopy < FJORD > => 700

    rule Gecadd       < FJORD > => 150
    rule Gecmul       < FJORD > => 6000
    rule Gecpairconst < FJORD > => 45000
    rule Gecpaircoeff < FJORD > => 34000
    rule Gfround      < FJORD > => 1

    rule maxCodeSize < FJORD > => 24576
    rule Rb          < FJORD > => 0

    rule Gcoldsload             < FJORD > => 2100
    rule Gcoldaccountaccess     < FJORD > => 2600
    rule Gwarmstorageread       < FJORD > => 100
    rule Gwarmstoragedirtystore < FJORD > => 100

    rule Gpointeval < FJORD > => 50000

    rule Gbls12g1add < FJORD > => 0
    rule Gbls12g1mul < FJORD > => 0
    rule Gbls12g2add < FJORD > => 0
    rule Gbls12g2mul < FJORD > => 0
    rule Gbls12PairingCheckMul < FJORD > => 0
    rule Gbls12PairingCheckAdd < FJORD > => 0
    rule Gbls12mapfptog1 < FJORD > => 0
    rule Gbls12mapfp2tog2 < FJORD > => 0

    rule Gaccessliststoragekey < FJORD > => 1900
    rule Gaccesslistaddress    < FJORD > => 2400

    rule maxInitCodeSize   < FJORD > => 49152
    rule Ginitcodewordcost < FJORD > => 2

    rule Rmaxquotient < FJORD > => 5

    rule Gselfdestructnewaccount << FJORD >> => true
    rule Gstaticcalldepth        << FJORD >> => false
    rule Gemptyisnonexistent     << FJORD >> => true
    rule Gzerovaluenewaccountgas << FJORD >> => false
    rule Ghasrevert              << FJORD >> => true
    rule Ghasreturndata          << FJORD >> => true
    rule Ghasstaticcall          << FJORD >> => true
    rule Ghasshift               << FJORD >> => true
    rule Ghasdirtysstore         << FJORD >> => true
    rule Ghassstorestipend       << FJORD >> => true
    rule Ghascreate2             << FJORD >> => true
    rule Ghasextcodehash         << FJORD >> => true
    rule Ghasselfbalance         << FJORD >> => true
    rule Ghaschainid             << FJORD >> => true
    rule Ghasaccesslist          << FJORD >> => true
    rule Ghasbasefee             << FJORD >> => true
    rule Ghasrejectedfirstbyte   << FJORD >> => true
    rule Ghasprevrandao          << FJORD >> => true
    rule Ghasmaxinitcodesize     << FJORD >> => true
    rule Ghaspushzero            << FJORD >> => true
    rule Ghaswarmcoinbase        << FJORD >> => true
    rule Ghaswithdrawals         << FJORD >> => true
    rule Ghastransient           << FJORD >> => true
    rule Ghasmcopy               << FJORD >> => true
    rule Ghasbeaconroot          << FJORD >> => true
    rule Ghaseip6780             << FJORD >> => true
    rule Ghasblobbasefee         << FJORD >> => true
    rule Ghasblobhash            << FJORD >> => true
    rule Ghasbls12msmdiscount    << FJORD >> => false
    rule Ghasdelegation          << FJORD >> => false
```

### Granite Schedule

```k
    syntax Schedule ::= "GRANITE" [symbol(GRANITE_EVM), smtlib(schedule_GRANITE)]
 // -----------------------------------------------------------------------------
    rule Gzero    < GRANITE > => 0

    rule Gbase    < GRANITE > => 2
    rule Gverylow < GRANITE > => 3
    rule Glow     < GRANITE > => 5
    rule Gmid     < GRANITE > => 8
    rule Ghigh    < GRANITE > => 10

    rule Gexp      < GRANITE > => 10
    rule Gexpbyte  < GRANITE > => 50
    rule Gsha3     < GRANITE > => 30
    rule Gsha3word < GRANITE > => 6

    rule Gsload       < GRANITE > => 100
    rule Gsstoreset   < GRANITE > => 20000
    rule Gsstorereset < GRANITE > => 2900
    rule Rsstoreclear < GRANITE > => 4800

    rule Glog      < GRANITE > => 375
    rule Glogdata  < GRANITE > => 8
    rule Glogtopic < GRANITE > => 375

    rule Gcall        < GRANITE > => 700
    rule Gcallstipend < GRANITE > => 2300
    rule Gcallvalue   < GRANITE > => 9000
    rule Gnewaccount  < GRANITE > => 25000

    rule Gcreate       < GRANITE > => 32000
    rule Gcodedeposit  < GRANITE > => 200
    rule Gselfdestruct < GRANITE > => 5000
    rule Rselfdestruct < GRANITE > => 0

    rule Gmemory      < GRANITE > => 3
    rule Gquadcoeff   < GRANITE > => 512
    rule Gcopy        < GRANITE > => 3
    rule Gquaddivisor < GRANITE > => 3

    rule Gtransaction   < GRANITE > => 21000
    rule Gtxcreate      < GRANITE > => 53000
    rule Gtxdatazero    < GRANITE > => 4
    rule Gtxdatanonzero < GRANITE > => 16

    rule Gjumpdest    < GRANITE > => 1
    rule Gbalance     < GRANITE > => 700
    rule Gblockhash   < GRANITE > => 20
    rule Gextcodesize < GRANITE > => 700
    rule Gextcodecopy < GRANITE > => 700

    rule Gecadd       < GRANITE > => 150
    rule Gecmul       < GRANITE > => 6000
    rule Gecpairconst < GRANITE > => 45000
    rule Gecpaircoeff < GRANITE > => 34000
    rule Gfround      < GRANITE > => 1

    rule maxCodeSize < GRANITE > => 24576
    rule Rb          < GRANITE > => 0

    rule Gcoldsload             < GRANITE > => 2100
    rule Gcoldaccountaccess     < GRANITE > => 2600
    rule Gwarmstorageread       < GRANITE > => 100
    rule Gwarmstoragedirtystore < GRANITE > => 100

    rule Gpointeval < GRANITE > => 50000

    rule Gbls12g1add < GRANITE > => 0
    rule Gbls12g1mul < GRANITE > => 0
    rule Gbls12g2add < GRANITE > => 0
    rule Gbls12g2mul < GRANITE > => 0
    rule Gbls12PairingCheckMul < GRANITE > => 0
    rule Gbls12PairingCheckAdd < GRANITE > => 0
    rule Gbls12mapfptog1 < GRANITE > => 0
    rule Gbls12mapfp2tog2 < GRANITE > => 0

    rule Gaccessliststoragekey < GRANITE > => 1900
    rule Gaccesslistaddress    < GRANITE > => 2400

    rule maxInitCodeSize   < GRANITE > => 49152
    rule Ginitcodewordcost < GRANITE > => 2

    rule Rmaxquotient < GRANITE > => 5

    rule Gselfdestructnewaccount << GRANITE >> => true
    rule Gstaticcalldepth        << GRANITE >> => false
    rule Gemptyisnonexistent     << GRANITE >> => true
    rule Gzerovaluenewaccountgas << GRANITE >> => false
    rule Ghasrevert              << GRANITE >> => true
    rule Ghasreturndata          << GRANITE >> => true
    rule Ghasstaticcall          << GRANITE >> => true
    rule Ghasshift               << GRANITE >> => true
    rule Ghasdirtysstore         << GRANITE >> => true
    rule Ghassstorestipend       << GRANITE >> => true
    rule Ghascreate2             << GRANITE >> => true
    rule Ghasextcodehash         << GRANITE >> => true
    rule Ghasselfbalance         << GRANITE >> => true
    rule Ghaschainid             << GRANITE >> => true
    rule Ghasaccesslist          << GRANITE >> => true
    rule Ghasbasefee             << GRANITE >> => true
    rule Ghasrejectedfirstbyte   << GRANITE >> => true
    rule Ghasprevrandao          << GRANITE >> => true
    rule Ghasmaxinitcodesize     << GRANITE >> => true
    rule Ghaspushzero            << GRANITE >> => true
    rule Ghaswarmcoinbase        << GRANITE >> => true
    rule Ghaswithdrawals         << GRANITE >> => true
    rule Ghastransient           << GRANITE >> => true
    rule Ghasmcopy               << GRANITE >> => true
    rule Ghasbeaconroot          << GRANITE >> => true
    rule Ghaseip6780             << GRANITE >> => true
    rule Ghasblobbasefee         << GRANITE >> => true
    rule Ghasblobhash            << GRANITE >> => true
    rule Ghasbls12msmdiscount    << GRANITE >> => false
    rule Ghasdelegation          << GRANITE >> => false
```

### Holocene Schedule

```k
    syntax Schedule ::= "HOLOCENE" [symbol(HOLOCENE_EVM), smtlib(schedule_HOLOCENE)]
 // --------------------------------------------------------------------------------
    rule Gzero    < HOLOCENE > => 0

    rule Gbase    < HOLOCENE > => 2
    rule Gverylow < HOLOCENE > => 3
    rule Glow     < HOLOCENE > => 5
    rule Gmid     < HOLOCENE > => 8
    rule Ghigh    < HOLOCENE > => 10

    rule Gexp      < HOLOCENE > => 10
    rule Gexpbyte  < HOLOCENE > => 50
    rule Gsha3     < HOLOCENE > => 30
    rule Gsha3word < HOLOCENE > => 6

    rule Gsload       < HOLOCENE > => 100
    rule Gsstoreset   < HOLOCENE > => 20000
    rule Gsstorereset < HOLOCENE > => 2900
    rule Rsstoreclear < HOLOCENE > => 4800

    rule Glog      < HOLOCENE > => 375
    rule Glogdata  < HOLOCENE > => 8
    rule Glogtopic < HOLOCENE > => 375

    rule Gcall        < HOLOCENE > => 700
    rule Gcallstipend < HOLOCENE > => 2300
    rule Gcallvalue   < HOLOCENE > => 9000
    rule Gnewaccount  < HOLOCENE > => 25000

    rule Gcreate       < HOLOCENE > => 32000
    rule Gcodedeposit  < HOLOCENE > => 200
    rule Gselfdestruct < HOLOCENE > => 5000
    rule Rselfdestruct < HOLOCENE > => 0

    rule Gmemory      < HOLOCENE > => 3
    rule Gquadcoeff   < HOLOCENE > => 512
    rule Gcopy        < HOLOCENE > => 3
    rule Gquaddivisor < HOLOCENE > => 3

    rule Gtransaction   < HOLOCENE > => 21000
    rule Gtxcreate      < HOLOCENE > => 53000
    rule Gtxdatazero    < HOLOCENE > => 4
    rule Gtxdatanonzero < HOLOCENE > => 16

    rule Gjumpdest    < HOLOCENE > => 1
    rule Gbalance     < HOLOCENE > => 700
    rule Gblockhash   < HOLOCENE > => 20
    rule Gextcodesize < HOLOCENE > => 700
    rule Gextcodecopy < HOLOCENE > => 700

    rule Gecadd       < HOLOCENE > => 150
    rule Gecmul       < HOLOCENE > => 6000
    rule Gecpairconst < HOLOCENE > => 45000
    rule Gecpaircoeff < HOLOCENE > => 34000
    rule Gfround      < HOLOCENE > => 1

    rule maxCodeSize < HOLOCENE > => 24576
    rule Rb          < HOLOCENE > => 0

    rule Gcoldsload             < HOLOCENE > => 2100
    rule Gcoldaccountaccess     < HOLOCENE > => 2600
    rule Gwarmstorageread       < HOLOCENE > => 100
    rule Gwarmstoragedirtystore < HOLOCENE > => 100

    rule Gpointeval < HOLOCENE > => 50000

    rule Gbls12g1add < HOLOCENE > => 0
    rule Gbls12g1mul < HOLOCENE > => 0
    rule Gbls12g2add < HOLOCENE > => 0
    rule Gbls12g2mul < HOLOCENE > => 0
    rule Gbls12PairingCheckMul < HOLOCENE > => 0
    rule Gbls12PairingCheckAdd < HOLOCENE > => 0
    rule Gbls12mapfptog1 < HOLOCENE > => 0
    rule Gbls12mapfp2tog2 < HOLOCENE > => 0

    rule Gaccessliststoragekey < HOLOCENE > => 1900
    rule Gaccesslistaddress    < HOLOCENE > => 2400

    rule maxInitCodeSize   < HOLOCENE > => 49152
    rule Ginitcodewordcost < HOLOCENE > => 2

    rule Rmaxquotient < HOLOCENE > => 5

    rule Gselfdestructnewaccount << HOLOCENE >> => true
    rule Gstaticcalldepth        << HOLOCENE >> => false
    rule Gemptyisnonexistent     << HOLOCENE >> => true
    rule Gzerovaluenewaccountgas << HOLOCENE >> => false
    rule Ghasrevert              << HOLOCENE >> => true
    rule Ghasreturndata          << HOLOCENE >> => true
    rule Ghasstaticcall          << HOLOCENE >> => true
    rule Ghasshift               << HOLOCENE >> => true
    rule Ghasdirtysstore         << HOLOCENE >> => true
    rule Ghassstorestipend       << HOLOCENE >> => true
    rule Ghascreate2             << HOLOCENE >> => true
    rule Ghasextcodehash         << HOLOCENE >> => true
    rule Ghasselfbalance         << HOLOCENE >> => true
    rule Ghaschainid             << HOLOCENE >> => true
    rule Ghasaccesslist          << HOLOCENE >> => true
    rule Ghasbasefee             << HOLOCENE >> => true
    rule Ghasrejectedfirstbyte   << HOLOCENE >> => true
    rule Ghasprevrandao          << HOLOCENE >> => true
    rule Ghasmaxinitcodesize     << HOLOCENE >> => true
    rule Ghaspushzero            << HOLOCENE >> => true
    rule Ghaswarmcoinbase        << HOLOCENE >> => true
    rule Ghaswithdrawals         << HOLOCENE >> => true
    rule Ghastransient           << HOLOCENE >> => true
    rule Ghasmcopy               << HOLOCENE >> => true
    rule Ghasbeaconroot          << HOLOCENE >> => true
    rule Ghaseip6780             << HOLOCENE >> => true
    rule Ghasblobbasefee         << HOLOCENE >> => true
    rule Ghasblobhash            << HOLOCENE >> => true
    rule Ghasbls12msmdiscount    << HOLOCENE >> => false
    rule Ghasdelegation          << HOLOCENE >> => false
```

### Isthmus Schedule

```k
    syntax Schedule ::= "ISTHMUS" [symbol(ISTHMUS_EVM), smtlib(schedule_ISTHMUS)]
 // -----------------------------------------------------------------------------

    rule Gzero    < ISTHMUS > => 0

    rule Gbase    < ISTHMUS > => 2
    rule Gverylow < ISTHMUS > => 3
    rule Glow     < ISTHMUS > => 5
    rule Gmid     < ISTHMUS > => 8
    rule Ghigh    < ISTHMUS > => 10

    rule Gexp      < ISTHMUS > => 10
    rule Gexpbyte  < ISTHMUS > => 50
    rule Gsha3     < ISTHMUS > => 30
    rule Gsha3word < ISTHMUS > => 6

    rule Gsload       < ISTHMUS > => 100
    rule Gsstoreset   < ISTHMUS > => 20000
    rule Gsstorereset < ISTHMUS > => 2900
    rule Rsstoreclear < ISTHMUS > => 4800

    rule Glog      < ISTHMUS > => 375
    rule Glogdata  < ISTHMUS > => 8
    rule Glogtopic < ISTHMUS > => 375

    rule Gcall        < ISTHMUS > => 700
    rule Gcallstipend < ISTHMUS > => 2300
    rule Gcallvalue   < ISTHMUS > => 9000
    rule Gnewaccount  < ISTHMUS > => 25000

    rule Gcreate       < ISTHMUS > => 32000
    rule Gcodedeposit  < ISTHMUS > => 200
    rule Gselfdestruct < ISTHMUS > => 5000
    rule Rselfdestruct < ISTHMUS > => 0

    rule Gmemory      < ISTHMUS > => 3
    rule Gquadcoeff   < ISTHMUS > => 512
    rule Gcopy        < ISTHMUS > => 3
    rule Gquaddivisor < ISTHMUS > => 3

    rule Gtransaction   < ISTHMUS > => 21000
    rule Gtxcreate      < ISTHMUS > => 53000
    rule Gtxdatazero    < ISTHMUS > => 4
    rule Gtxdatanonzero < ISTHMUS > => 16

    rule Gjumpdest    < ISTHMUS > => 1
    rule Gbalance     < ISTHMUS > => 700
    rule Gblockhash   < ISTHMUS > => 20
    rule Gextcodesize < ISTHMUS > => 700
    rule Gextcodecopy < ISTHMUS > => 700

    rule Gecadd       < ISTHMUS > => 150
    rule Gecmul       < ISTHMUS > => 6000
    rule Gecpairconst < ISTHMUS > => 45000
    rule Gecpaircoeff < ISTHMUS > => 34000
    rule Gfround      < ISTHMUS > => 1

    rule maxCodeSize < ISTHMUS > => 24576
    rule Rb          < ISTHMUS > => 0

    rule Gcoldsload             < ISTHMUS > => 2100
    rule Gcoldaccountaccess     < ISTHMUS > => 2600
    rule Gwarmstorageread       < ISTHMUS > => 100
    rule Gwarmstoragedirtystore < ISTHMUS > => 100

    rule Gpointeval < ISTHMUS > => 50000

    rule Gbls12g1add < ISTHMUS > => 375
    rule Gbls12g1mul < ISTHMUS > => 12000
    rule Gbls12g2add < ISTHMUS > => 600
    rule Gbls12g2mul < ISTHMUS > => 22500
    rule Gbls12PairingCheckMul < ISTHMUS > => 32600
    rule Gbls12PairingCheckAdd < ISTHMUS > => 37700
    rule Gbls12mapfptog1 < ISTHMUS > => 5500
    rule Gbls12mapfp2tog2 < ISTHMUS > => 23800

    rule Gaccessliststoragekey < ISTHMUS > => 1900
    rule Gaccesslistaddress    < ISTHMUS > => 2400

    rule maxInitCodeSize   < ISTHMUS > => 49152
    rule Ginitcodewordcost < ISTHMUS > => 2

    rule Rmaxquotient < ISTHMUS > => 5

    rule Gselfdestructnewaccount << ISTHMUS >> => true
    rule Gstaticcalldepth        << ISTHMUS >> => false
    rule Gemptyisnonexistent     << ISTHMUS >> => true
    rule Gzerovaluenewaccountgas << ISTHMUS >> => false
    rule Ghasrevert              << ISTHMUS >> => true
    rule Ghasreturndata          << ISTHMUS >> => true
    rule Ghasstaticcall          << ISTHMUS >> => true
    rule Ghasshift               << ISTHMUS >> => true
    rule Ghasdirtysstore         << ISTHMUS >> => true
    rule Ghassstorestipend       << ISTHMUS >> => true
    rule Ghascreate2             << ISTHMUS >> => true
    rule Ghasextcodehash         << ISTHMUS >> => true
    rule Ghasselfbalance         << ISTHMUS >> => true
    rule Ghaschainid             << ISTHMUS >> => true
    rule Ghasaccesslist          << ISTHMUS >> => true
    rule Ghasbasefee             << ISTHMUS >> => true
    rule Ghasrejectedfirstbyte   << ISTHMUS >> => true
    rule Ghasprevrandao          << ISTHMUS >> => true
    rule Ghasmaxinitcodesize     << ISTHMUS >> => true
    rule Ghaspushzero            << ISTHMUS >> => true
    rule Ghaswarmcoinbase        << ISTHMUS >> => true
    rule Ghaswithdrawals         << ISTHMUS >> => true
    rule Ghastransient           << ISTHMUS >> => true
    rule Ghasmcopy               << ISTHMUS >> => true
    rule Ghasbeaconroot          << ISTHMUS >> => true
    rule Ghaseip6780             << ISTHMUS >> => true
    rule Ghasblobbasefee         << ISTHMUS >> => true
    rule Ghasblobhash            << ISTHMUS >> => true
    rule Ghasbls12msmdiscount    << ISTHMUS >> => true
    rule Ghasdelegation          << ISTHMUS >> => true

endmodule
```
