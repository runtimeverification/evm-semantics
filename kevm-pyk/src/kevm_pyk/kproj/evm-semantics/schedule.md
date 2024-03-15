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

    syntax Bool ::= ScheduleFlag "<<" Schedule ">>" [function, total, private]
 // -----------------------------------------------------------------

    syntax ScheduleFlag ::= "Gselfdestructnewaccount" | "Gstaticcalldepth" | "Gemptyisnonexistent" | "Gzerovaluenewaccountgas"
                          | "Ghasrevert"              | "Ghasreturndata"   | "Ghasstaticcall"      | "Ghasshift"
                          | "Ghasdirtysstore"         | "Ghascreate2"      | "Ghasextcodehash"     | "Ghasselfbalance"
                          | "Ghassstorestipend"       | "Ghaschainid"      | "Ghasaccesslist"      | "Ghasbasefee"
                          | "Ghasrejectedfirstbyte"   | "Ghasprevrandao"   | "Ghasmaxinitcodesize" | "Ghaspushzero"
                          | "Ghaswarmcoinbase"        | "Ghasdelegatecall" | "Ghasmcopy"
 // ------------------------------------------------------------------------------------
```

### Schedule Constants

A `ScheduleConst` is a constant determined by the fee schedule.

```k
    syntax Int ::= ScheduleConst "<" Schedule ">" [function, total, private]
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

### Schedule Tuple

A `ScheduleTuple` is a tuple containing all of the fee schedule values for a particular `Schedule`.

```k
    syntax ScheduleTuple ::= schedule(
        Gzero: Int,         Gbase: Int,         Gverylow: Int,     Glow: Int,              Gmid: Int,               Ghigh: Int,            Gextcodesize: Int,
        Gextcodecopy: Int,  Gbalance: Int,      Gsload: Int,       Gjumpdest: Int,         Gsstoreset: Int,         Gsstorereset: Int,     Rsstoreclear: Int,
        Rselfdestruct: Int, Gselfdestruct: Int, Gcreate: Int,      Gcodedeposit: Int,      Gcall: Int,              Gcallvalue: Int,       Gcallstipend: Int,
        Gnewaccount: Int,   Gexp: Int,          Gexpbyte: Int,     Gmemory: Int,           Gtxcreate: Int,          Gtxdatazero: Int,      Gtxdatanonzero: Int,
        Gtransaction: Int,  Glog: Int,          Glogdata: Int,     Glogtopic: Int,         Gsha3: Int,              Gsha3word: Int,        Gcopy: Int,
        Gblockhash: Int,    Gquadcoeff: Int,    maxCodeSize: Int,  Rb: Int,                Gquaddivisor: Int,       Gecadd: Int,           Gecmul: Int,
        Gecpairconst: Int,  Gecpaircoeff: Int,  Gfround: Int,      Gcoldsload: Int,        Gcoldaccountaccess: Int, Gwarmstorageread: Int, Gaccesslistaddress: Int,
        Gaccessliststoragekey: Int,             Rmaxquotient: Int, Ginitcodewordcost: Int, maxInitCodeSize: Int,

        Gselfdestructnewaccount: Bool, Gstaticcalldepth: Bool, Gemptyisnonexistent: Bool, Gzerovaluenewaccountgas: Bool,
        Ghasrevert: Bool,              Ghasreturndata: Bool,   Ghasstaticcall: Bool,      Ghasshift: Bool,
        Ghasdirtysstore: Bool,         Ghascreate2: Bool,      Ghasextcodehash: Bool,     Ghasselfbalance: Bool,
        Ghassstorestipend: Bool,       Ghaschainid: Bool,      Ghasaccesslist: Bool,      Ghasbasefee: Bool,
        Ghasrejectedfirstbyte: Bool,   Ghasprevrandao: Bool,   Ghasmaxinitcodesize: Bool, Ghaspushzero: Bool,
        Ghaswarmcoinbase: Bool,        Ghasdelegatecall: Bool, Ghasmcopy: Bool
    ) [klabel(schedule), symbol, smtlib(schedule)]

    syntax ScheduleTuple ::= getSchedule(Schedule) [function, total]
 // ----------------------------------------------------------------

    rule getSchedule(S) => schedule(
        Gzero < S >,         Gbase < S >,         Gverylow < S >,     Glow < S >,              Gmid < S >,               Ghigh < S >,            Gextcodesize < S >,
        Gextcodecopy < S >,  Gbalance < S >,      Gsload < S >,       Gjumpdest < S >,         Gsstoreset < S >,         Gsstorereset < S >,     Rsstoreclear < S >,
        Rselfdestruct < S >, Gselfdestruct < S >, Gcreate < S >,      Gcodedeposit < S >,      Gcall < S >,              Gcallvalue < S >,       Gcallstipend < S >,
        Gnewaccount < S >,   Gexp < S >,          Gexpbyte < S >,     Gmemory < S >,           Gtxcreate < S >,          Gtxdatazero < S >,      Gtxdatanonzero < S >,
        Gtransaction < S >,  Glog < S >,          Glogdata < S >,     Glogtopic < S >,         Gsha3 < S >,              Gsha3word < S >,        Gcopy < S >,
        Gblockhash < S >,    Gquadcoeff < S >,    maxCodeSize < S >,  Rb < S >,                Gquaddivisor < S >,       Gecadd < S >,           Gecmul < S >,
        Gecpairconst < S >,  Gecpaircoeff < S >,  Gfround < S >,      Gcoldsload < S >,        Gcoldaccountaccess < S >, Gwarmstorageread < S >, Gaccesslistaddress < S >,
        Gaccessliststoragekey < S >,              Rmaxquotient < S >, Ginitcodewordcost < S >, maxInitCodeSize < S >,

        Gselfdestructnewaccount << S >>, Gstaticcalldepth << S >>, Gemptyisnonexistent << S >>, Gzerovaluenewaccountgas << S >>,
        Ghasrevert << S >>,              Ghasreturndata << S >>,   Ghasstaticcall << S >>,      Ghasshift << S >>,
        Ghasdirtysstore << S >>,         Ghascreate2 << S >>,      Ghasextcodehash << S >>,     Ghasselfbalance << S >>,
        Ghassstorestipend << S >>,       Ghaschainid << S >>,      Ghasaccesslist << S >>,      Ghasbasefee << S >>,
        Ghasrejectedfirstbyte << S >>,   Ghasprevrandao << S >>,   Ghasmaxinitcodesize << S >>, Ghaspushzero << S >>,
        Ghaswarmcoinbase << S >>,        Ghasdelegatecall << S >>, Ghasmcopy << S >>
    )
```

### Frontier Schedule

```k
    syntax Schedule ::= "FRONTIER" [klabel(FRONTIER_EVM), symbol, smtlib(schedule_FRONTIER)]
 // ----------------------------------------------------------------------------------------
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

    rule Gcoldsload         < FRONTIER > => 0
    rule Gcoldaccountaccess < FRONTIER > => 0
    rule Gwarmstorageread   < FRONTIER > => 0

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
    rule Ghasdelegatecall        << FRONTIER >> => false
    rule Ghasmcopy               << FRONTIER >> => false
```

### Homestead Schedule

```k
    syntax Schedule ::= "HOMESTEAD" [klabel(HOMESTEAD_EVM), symbol, smtlib(schedule_HOMESTEAD)]
 // -------------------------------------------------------------------------------------------
    rule Gtxcreate  < HOMESTEAD > => 53000
    rule SCHEDCONST < HOMESTEAD > => SCHEDCONST < FRONTIER > requires SCHEDCONST =/=K Gtxcreate

    rule Ghasdelegatecall << HOMESTEAD >> => true
    rule SCHEDFLAG << HOMESTEAD >> => SCHEDFLAG << FRONTIER >> requires SCHEDFLAG =/=K Ghasdelegatecall
```

### Tangerine Whistle Schedule

```k
    syntax Schedule ::= "TANGERINE_WHISTLE" [klabel(TANGERINE_WHISTLE_EVM), symbol, smtlib(schedule_TANGERINE_WHISTLE)]
 // -------------------------------------------------------------------------------------------------------------------
    rule Gbalance      < TANGERINE_WHISTLE > => 400
    rule Gsload        < TANGERINE_WHISTLE > => 200
    rule Gcall         < TANGERINE_WHISTLE > => 700
    rule Gselfdestruct < TANGERINE_WHISTLE > => 5000
    rule Gextcodesize  < TANGERINE_WHISTLE > => 700
    rule Gextcodecopy  < TANGERINE_WHISTLE > => 700

    rule SCHEDCONST    < TANGERINE_WHISTLE > => SCHEDCONST < HOMESTEAD >
      requires notBool      ( SCHEDCONST ==K Gbalance      orBool SCHEDCONST ==K Gsload       orBool SCHEDCONST ==K Gcall
                       orBool SCHEDCONST ==K Gselfdestruct orBool SCHEDCONST ==K Gextcodesize orBool SCHEDCONST ==K Gextcodecopy
                            )

    rule Gselfdestructnewaccount << TANGERINE_WHISTLE >> => true
    rule Gstaticcalldepth        << TANGERINE_WHISTLE >> => false
    rule SCHEDCONST              << TANGERINE_WHISTLE >> => SCHEDCONST << HOMESTEAD >>
      requires notBool      ( SCHEDCONST ==K Gselfdestructnewaccount orBool SCHEDCONST ==K Gstaticcalldepth )
```

### Spurious Dragon Schedule

```k
    syntax Schedule ::= "SPURIOUS_DRAGON" [klabel(SPURIOUS_DRAGON_EVM), symbol, smtlib(schedule_SPURIOUS_DRAGON)]
 // -------------------------------------------------------------------------------------------------------------
    rule Gexpbyte    < SPURIOUS_DRAGON > => 50
    rule maxCodeSize < SPURIOUS_DRAGON > => 24576

    rule SCHEDCONST  < SPURIOUS_DRAGON > => SCHEDCONST < TANGERINE_WHISTLE > requires SCHEDCONST =/=K Gexpbyte andBool SCHEDCONST =/=K maxCodeSize

    rule Gemptyisnonexistent     << SPURIOUS_DRAGON >> => true
    rule Gzerovaluenewaccountgas << SPURIOUS_DRAGON >> => false
    rule SCHEDCONST              << SPURIOUS_DRAGON >> => SCHEDCONST << TANGERINE_WHISTLE >>
      requires notBool      ( SCHEDCONST ==K Gemptyisnonexistent orBool SCHEDCONST ==K Gzerovaluenewaccountgas )
```

### Byzantium Schedule

```k
    syntax Schedule ::= "BYZANTIUM" [klabel(BYZANTIUM_EVM), symbol, smtlib(schedule_BYZANTIUM)]
 // -------------------------------------------------------------------------------------------
    rule Rb         < BYZANTIUM > => 3 *Int eth
    rule SCHEDCONST < BYZANTIUM > => SCHEDCONST < SPURIOUS_DRAGON >
      requires notBool ( SCHEDCONST ==K Rb )

    rule Ghasrevert     << BYZANTIUM >> => true
    rule Ghasreturndata << BYZANTIUM >> => true
    rule Ghasstaticcall << BYZANTIUM >> => true
    rule SCHEDFLAG      << BYZANTIUM >> => SCHEDFLAG << SPURIOUS_DRAGON >>
      requires notBool ( SCHEDFLAG ==K Ghasrevert orBool SCHEDFLAG ==K Ghasreturndata orBool SCHEDFLAG ==K Ghasstaticcall )
```

### Constantinople Schedule

```k
    syntax Schedule ::= "CONSTANTINOPLE" [klabel(CONSTANTINOPLE_EVM), symbol, smtlib(schedule_CONSTANTINOPLE)]
 // ----------------------------------------------------------------------------------------------------------
    rule Rb         < CONSTANTINOPLE > => 2 *Int eth
    rule SCHEDCONST < CONSTANTINOPLE > => SCHEDCONST < BYZANTIUM >
      requires notBool ( SCHEDCONST ==K Rb )

    rule Ghasshift       << CONSTANTINOPLE >> => true
    rule Ghasdirtysstore << CONSTANTINOPLE >> => true
    rule Ghascreate2     << CONSTANTINOPLE >> => true
    rule Ghasextcodehash << CONSTANTINOPLE >> => true
    rule SCHEDFLAG       << CONSTANTINOPLE >> => SCHEDFLAG << BYZANTIUM >>
      requires notBool ( SCHEDFLAG ==K Ghasshift orBool SCHEDFLAG ==K Ghasdirtysstore orBool SCHEDFLAG ==K Ghascreate2 orBool SCHEDFLAG ==K Ghasextcodehash )
```

### Petersburg Schedule

```k
    syntax Schedule ::= "PETERSBURG" [klabel(PETERSBURG_EVM), symbol, smtlib(schedule_PETERSBURG)]
 // ----------------------------------------------------------------------------------------------
    rule SCHEDCONST < PETERSBURG > => SCHEDCONST < CONSTANTINOPLE >

    rule Ghasdirtysstore << PETERSBURG >> => false
    rule SCHEDFLAG       << PETERSBURG >> => SCHEDFLAG << CONSTANTINOPLE >>
      requires notBool ( SCHEDFLAG ==K Ghasdirtysstore )
```

### Istanbul Schedule

```k
    syntax Schedule ::= "ISTANBUL" [klabel(ISTANBUL_EVM), symbol, smtlib(schedule_ISTANBUL)]
 // ----------------------------------------------------------------------------------------
    rule Gecadd         < ISTANBUL > => 150
    rule Gecmul         < ISTANBUL > => 6000
    rule Gecpairconst   < ISTANBUL > => 45000
    rule Gecpaircoeff   < ISTANBUL > => 34000
    rule Gtxdatanonzero < ISTANBUL > => 16
    rule Gsload         < ISTANBUL > => 800
    rule Gbalance       < ISTANBUL > => 700
    rule SCHEDCONST     < ISTANBUL > => SCHEDCONST < PETERSBURG >
      requires notBool ( SCHEDCONST ==K Gecadd
                  orBool SCHEDCONST ==K Gecmul
                  orBool SCHEDCONST ==K Gecpairconst
                  orBool SCHEDCONST ==K Gecpaircoeff
                  orBool SCHEDCONST ==K Gtxdatanonzero
                  orBool SCHEDCONST ==K Gsload
                  orBool SCHEDCONST ==K Gbalance
                       )

    rule Ghasselfbalance   << ISTANBUL >> => true
    rule Ghasdirtysstore   << ISTANBUL >> => true
    rule Ghassstorestipend << ISTANBUL >> => true
    rule Ghaschainid       << ISTANBUL >> => true
    rule SCHEDFLAG         << ISTANBUL >> => SCHEDFLAG << PETERSBURG >>
      requires notBool ( SCHEDFLAG ==K Ghasselfbalance
                  orBool SCHEDFLAG ==K Ghasdirtysstore
                  orBool SCHEDFLAG ==K Ghassstorestipend
                  orBool SCHEDFLAG ==K Ghaschainid
                       )
```

### Berlin Schedule

```k
    syntax Schedule ::= "BERLIN" [klabel(BERLIN_EVM), symbol, smtlib(schedule_BERLIN)]
 // ----------------------------------------------------------------------------------
    rule Gcoldsload            < BERLIN > => 2100
    rule Gcoldaccountaccess    < BERLIN > => 2600
    rule Gwarmstorageread      < BERLIN > => 100
    rule Gsload                < BERLIN > => Gwarmstorageread < BERLIN >
    rule Gsstorereset          < BERLIN > => 5000 -Int Gcoldsload < BERLIN >
    rule Gquaddivisor          < BERLIN > => 3
    rule Gaccessliststoragekey < BERLIN > => 1900
    rule Gaccesslistaddress    < BERLIN > => 2400

    rule SCHEDCONST            < BERLIN > => SCHEDCONST < ISTANBUL >
      requires notBool ( SCHEDCONST ==K Gcoldsload
                  orBool SCHEDCONST ==K Gcoldaccountaccess
                  orBool SCHEDCONST ==K Gwarmstorageread
                  orBool SCHEDCONST ==K Gsload
                  orBool SCHEDCONST ==K Gsstorereset
                  orBool SCHEDCONST ==K Gquaddivisor
                  orBool SCHEDCONST ==K Gaccessliststoragekey
                  orBool SCHEDCONST ==K Gaccesslistaddress
                       )

    rule Ghasaccesslist << BERLIN >> => true
    rule SCHEDFLAG      << BERLIN >> => SCHEDFLAG << ISTANBUL >>
      requires notBool ( SCHEDFLAG ==K Ghasaccesslist )
```

### London Schedule

```k
    syntax Schedule ::= "LONDON" [klabel(LONDON_EVM), symbol, smtlib(schedule_LONDON)]
 // ----------------------------------------------------------------------------------
    rule Rselfdestruct < LONDON > => 0
    rule Rsstoreclear  < LONDON > => Gsstorereset < LONDON > +Int Gaccessliststoragekey < LONDON >
    rule Rmaxquotient  < LONDON > => 5
    rule SCHEDCONST    < LONDON > => SCHEDCONST < BERLIN >
      requires notBool ( SCHEDCONST ==K Rselfdestruct
                  orBool SCHEDCONST ==K Rsstoreclear
                  orBool SCHEDCONST ==K Rmaxquotient
                       )

    rule Ghasbasefee           << LONDON >> => true
    rule Ghasrejectedfirstbyte << LONDON >> => true
    rule SCHEDFLAG             << LONDON >> => SCHEDFLAG << BERLIN >>
      requires notBool ( SCHEDFLAG ==K Ghasbasefee
                  orBool SCHEDFLAG ==K Ghasrejectedfirstbyte
                       )
```

### Merge Schedule

```k
    syntax Schedule ::= "MERGE" [klabel(MERGE_EVM), symbol, smtlib(schedule_MERGE)]
 // -------------------------------------------------------------------------------
    rule Rb         < MERGE > => 0
    rule SCHEDCONST < MERGE > => SCHEDCONST < LONDON >
      requires notBool SCHEDCONST ==K Rb

    rule Ghasprevrandao << MERGE >> => true
    rule SCHEDFLAG      << MERGE >> => SCHEDFLAG << LONDON >>
      requires notBool SCHEDFLAG ==K Ghasprevrandao
```

### Shanghai Schedule

```k
    syntax Schedule ::= "SHANGHAI" [klabel(SHANGHAI_EVM), symbol, smtlib(schedule_SHANGHAI)]
 // ----------------------------------------------------------------------------------------
    rule maxInitCodeSize   < SHANGHAI > => 2 *Int maxCodeSize < SHANGHAI >
    rule Ginitcodewordcost < SHANGHAI > => 2
    rule SCHEDCONST        < SHANGHAI > => SCHEDCONST < MERGE >
      requires notBool ( SCHEDCONST ==K maxInitCodeSize
                  orBool SCHEDCONST ==K Ginitcodewordcost
                       )

    rule Ghasmaxinitcodesize << SHANGHAI >> => true
    rule Ghaspushzero        << SHANGHAI >> => true
    rule Ghaswarmcoinbase    << SHANGHAI >> => true
    rule SCHEDFLAG           << SHANGHAI >> => SCHEDFLAG << MERGE >>
      requires notBool ( SCHEDFLAG ==K Ghasmaxinitcodesize
                  orBool SCHEDFLAG ==K Ghaspushzero
                  orBool SCHEDFLAG ==K Ghaswarmcoinbase
                       )
```

### Cancuin Schedule

```k
    syntax Schedule ::= "CANCUN" [klabel(CANCUN_EVM), symbol, smtlib(schedule_CANCUN)]
 // ----------------------------------------------------------------------------------
    rule SCHEDCONST < CANCUN > => SCHEDCONST < SHANGHAI >

    rule Ghasmcopy << CANCUN >> => true
    rule SCHEDFLAG << CANCUN >> => SCHEDFLAG << SHANGHAI >>
      requires notBool ( SCHEDFLAG ==K Ghasmcopy
                       )
endmodule
```
