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
                          | "Ghasrejectedfirstbyte"   | "Ghasprevrandao"
 // --------------------------------------------------------------------
```

### Schedule Constants

A `ScheduleConst` is a constant determined by the fee schedule.

```k
    syntax Int ::= ScheduleConst "<" Schedule ">" [function, total]
 // ---------------------------------------------------------------

    syntax ScheduleConst ::= "Gzero"            | "Gbase"              | "Gverylow"      | "Glow"          | "Gmid"        | "Ghigh"
                           | "Gextcodesize"     | "Gextcodecopy"       | "Gbalance"      | "Gsload"        | "Gjumpdest"   | "Gsstoreset"
                           | "Gsstorereset"     | "Rsstoreclear"       | "Rselfdestruct" | "Gselfdestruct" | "Gcreate"     | "Gcodedeposit"  | "Gcall"
                           | "Gcallvalue"       | "Gcallstipend"       | "Gnewaccount"   | "Gexp"          | "Gexpbyte"    | "Gmemory"       | "Gtxcreate"
                           | "Gtxdatazero"      | "Gtxdatanonzero"     | "Gtransaction"  | "Glog"          | "Glogdata"    | "Glogtopic"     | "Gsha3"
                           | "Gsha3word"        | "Gcopy"              | "Gblockhash"    | "Gquadcoeff"    | "maxCodeSize" | "Rb"            | "Gquaddivisor"
                           | "Gecadd"           | "Gecmul"             | "Gecpairconst"  | "Gecpaircoeff"  | "Gfround"     | "Gcoldsload"    | "Gcoldaccountaccess"
                           | "Gwarmstorageread" | "Gaccesslistaddress" | "Gaccessliststoragekey"           | "Rmaxquotient"
 // -----------------------------------------------------------------------------------------------------------------------
```

### Default Schedule

```k
    syntax Schedule ::= "DEFAULT" [klabel(DEFAULT_EVM), symbol, smtlib(schedule_DEFAULT)]
 // -------------------------------------------------------------------------------------
    rule Gzero    < DEFAULT > => 0
    rule Gbase    < DEFAULT > => 2
    rule Gverylow < DEFAULT > => 3
    rule Glow     < DEFAULT > => 5
    rule Gmid     < DEFAULT > => 8
    rule Ghigh    < DEFAULT > => 10

    rule Gexp      < DEFAULT > => 10
    rule Gexpbyte  < DEFAULT > => 10
    rule Gsha3     < DEFAULT > => 30
    rule Gsha3word < DEFAULT > => 6

    rule Gsload       < DEFAULT > => 50
    rule Gsstoreset   < DEFAULT > => 20000
    rule Gsstorereset < DEFAULT > => 5000
    rule Rsstoreclear < DEFAULT > => 15000

    rule Glog      < DEFAULT > => 375
    rule Glogdata  < DEFAULT > => 8
    rule Glogtopic < DEFAULT > => 375

    rule Gcall        < DEFAULT > => 40
    rule Gcallstipend < DEFAULT > => 2300
    rule Gcallvalue   < DEFAULT > => 9000
    rule Gnewaccount  < DEFAULT > => 25000

    rule Gcreate       < DEFAULT > => 32000
    rule Gcodedeposit  < DEFAULT > => 200
    rule Gselfdestruct < DEFAULT > => 0
    rule Rselfdestruct < DEFAULT > => 24000

    rule Gmemory      < DEFAULT > => 3
    rule Gquadcoeff   < DEFAULT > => 512
    rule Gcopy        < DEFAULT > => 3
    rule Gquaddivisor < DEFAULT > => 20

    rule Gtransaction   < DEFAULT > => 21000
    rule Gtxcreate      < DEFAULT > => 53000
    rule Gtxdatazero    < DEFAULT > => 4
    rule Gtxdatanonzero < DEFAULT > => 68

    rule Gjumpdest    < DEFAULT > => 1
    rule Gbalance     < DEFAULT > => 20
    rule Gblockhash   < DEFAULT > => 20
    rule Gextcodesize < DEFAULT > => 20
    rule Gextcodecopy < DEFAULT > => 20

    rule Gecadd       < DEFAULT > => 500
    rule Gecmul       < DEFAULT > => 40000
    rule Gecpairconst < DEFAULT > => 100000
    rule Gecpaircoeff < DEFAULT > => 80000
    rule Gfround      < DEFAULT > => 1

    rule maxCodeSize < DEFAULT > => 2 ^Int 32 -Int 1
    rule Rb          < DEFAULT > => 5 *Int (10 ^Int 18)

    rule Gcoldsload         < DEFAULT > => 0
    rule Gcoldaccountaccess < DEFAULT > => 0
    rule Gwarmstorageread   < DEFAULT > => 0

    rule Gaccessliststoragekey < DEFAULT > => 0
    rule Gaccesslistaddress    < DEFAULT > => 0

    rule Rmaxquotient < DEFAULT > => 2

    rule Gselfdestructnewaccount << DEFAULT >> => false
    rule Gstaticcalldepth        << DEFAULT >> => true
    rule Gemptyisnonexistent     << DEFAULT >> => false
    rule Gzerovaluenewaccountgas << DEFAULT >> => true
    rule Ghasrevert              << DEFAULT >> => false
    rule Ghasreturndata          << DEFAULT >> => false
    rule Ghasstaticcall          << DEFAULT >> => false
    rule Ghasshift               << DEFAULT >> => false
    rule Ghasdirtysstore         << DEFAULT >> => false
    rule Ghassstorestipend       << DEFAULT >> => false
    rule Ghascreate2             << DEFAULT >> => false
    rule Ghasextcodehash         << DEFAULT >> => false
    rule Ghasselfbalance         << DEFAULT >> => false
    rule Ghaschainid             << DEFAULT >> => false
    rule Ghasaccesslist          << DEFAULT >> => false
    rule Ghasbasefee             << DEFAULT >> => false
    rule Ghasrejectedfirstbyte   << DEFAULT >> => false
    rule Ghasprevrandao          << DEFAULT >> => false
```

### Frontier Schedule

```k
    syntax Schedule ::= "FRONTIER" [klabel(FRONTIER_EVM), symbol, smtlib(schedule_FRONTIER)]
 // ----------------------------------------------------------------------------------------
    rule Gtxcreate  < FRONTIER > => 21000
    rule SCHEDCONST < FRONTIER > => SCHEDCONST < DEFAULT > requires SCHEDCONST =/=K Gtxcreate

    rule SCHEDFLAG << FRONTIER >> => SCHEDFLAG << DEFAULT >>
```

### Homestead Schedule

```k
    syntax Schedule ::= "HOMESTEAD" [klabel(HOMESTEAD_EVM), symbol, smtlib(schedule_HOMESTEAD)]
 // -------------------------------------------------------------------------------------------
    rule SCHEDCONST < HOMESTEAD > => SCHEDCONST < DEFAULT >

    rule SCHEDFLAG << HOMESTEAD >> => SCHEDFLAG << DEFAULT >>
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

endmodule
```