Ethereum Simulations
====================

Ethereum is using the EVM to drive updates over the world state.
Actual execution of the EVM is defined in [the EVM file](evm.md).

```{.k .uiuck .rvk}
requires "evm.k"

module ETHEREUM-SIMULATION
    imports ETHEREUM
```

An Ethereum simulation is a list of Ethereum commands.
Some Ethereum commands take an Ethereum specification (eg. for an account or transaction).

```{.k .uiuck .rvk}
    syntax EthereumSimulation ::= ".EthereumSimulation"
                                | EthereumCommand EthereumSimulation
 // ----------------------------------------------------------------
    rule .EthereumSimulation => .
    rule ETC:EthereumCommand ETS:EthereumSimulation => ETC ~> ETS

    syntax EthereumSimulation ::= JSON
 // ----------------------------------
    rule JSONINPUT:JSON => run JSONINPUT success .EthereumSimulation

    syntax EthereumCommand ::= DistCommand JSON
 // -------------------------------------------
    rule DC:DistCommand DATA : { .JSONList } => .
    rule DC:DistCommand DATA : { KEY : VALUE , REST } => DC DATA : { KEY : VALUE } ~> DC DATA : { REST } requires REST =/=K .JSONList

    rule DC:DistCommand DATA : [ .JSONList ] => .
    rule DC:DistCommand DATA : [ { TEST } , REST ] => DC DATA : { TEST } ~> DC DATA : [ REST ]
```

For verification purposes, it's much easier to specify a program in terms of its op-codes and not the hex-encoding that the tests use.
To do so, we'll extend sort `JSON` with some EVM specific syntax, and provide a "pretti-fication" to the nicer input form.

```{.k .uiuck .rvk}
    syntax JSON ::= Word | WordStack | OpCodes | Map | Call | SubstateLogEntry
 // --------------------------------------------------------------------------
    rule DC:DistCommand "account" : { ACCTID: { KEY : VALUE , REST } } => DC "account" : { ACCTID : { KEY : VALUE } } ~> DC "account" : { ACCTID : { REST } } requires REST =/=K .JSONList

    rule DC:DistCommand "account" : { ((ACCTID:String) => #parseAddr(ACCTID)) : ACCT }
    rule DC:DistCommand "account" : { (ACCT:Word) : { "balance" : ((VAL:String)         => #parseWord(VAL)) } }
    rule DC:DistCommand "account" : { (ACCT:Word) : { "nonce"   : ((VAL:String)         => #parseWord(VAL)) } }
    rule DC:DistCommand "account" : { (ACCT:Word) : { "code"    : ((CODE:String)        => #dasmOpCodes(#parseByteStack(CODE))) } }
    rule DC:DistCommand "account" : { (ACCT:Word) : { "code"    : ((CODE:OpCodes)       => #asMapOpCodes(CODE)) } }
    rule DC:DistCommand "account" : { (ACCT:Word) : { "storage" : ({ STORAGE:JSONList } => #parseMap({ STORAGE })) } }

    syntax JSONList ::= #sortJSONList ( JSONList )            [function]
                      | #sortJSONList ( JSONList , JSONList ) [function, klabel(#sortJSONListAux)]
 // ----------------------------------------------------------------------------------------------
    rule #sortJSONList(JS) => #sortJSONList(JS, .JSONList)
    rule #sortJSONList(.JSONList, LS)            => LS
    rule #sortJSONList(((KEY : VAL) , REST), LS) => #insertJSONKey((KEY : VAL), #sortJSONList(REST, LS))

    syntax JSONList ::= #insertJSONKey ( JSON , JSONList ) [function]
 // -----------------------------------------------------------------
    rule #insertJSONKey( JS , .JSONList ) => JS , .JSONList
    rule #insertJSONKey( (KEY : VAL) , ((KEY' : VAL') , REST) ) => (KEY : VAL)   , (KEY' : VAL')              , REST  requires KEY <String KEY'
    rule #insertJSONKey( (KEY : VAL) , ((KEY' : VAL') , REST) ) => (KEY' : VAL') , #insertJSONKey((KEY : VAL) , REST) requires KEY >=String KEY'

    syntax Bool ::= #isSorted ( JSONList ) [function]
 // -------------------------------------------------
    rule #isSorted( .JSONList ) => true
    rule #isSorted( KEY : _ )   => true
    rule #isSorted( (KEY : _) , (KEY' : VAL) , REST ) => KEY <=String KEY' andThenBool #isSorted((KEY' : VAL) , REST)
```

### Driving Execution

-   `start` places `#next` on the `op` cell so that execution of the loaded state begin.
-   `flush` places `#finalize` on the `op` cell once it sees `#end` in the `op` cell, clearing any exceptions it finds.

```{.k .uiuck .rvk}
    syntax EthereumCommand ::= "start" | "flush"
 // --------------------------------------------
    rule <mode> NORMAL     </mode> <k> start => . ... </k> <op> . => #execute    </op>
    rule <mode> VMTESTS    </mode> <k> start => . ... </k> <op> . => #execute    </op>
    rule <mode> GASANALYZE </mode> <k> start => . ... </k> <op> . => #gasAnalyze </op>
    rule <k> flush => . ... </k> <op> #end => #finalize </op>
    rule <k> flush => . ... </k> <op> #exception => #finalize ~> #exception </op>
```

-   `exception` only clears from the `k` cell if there is an exception on the `op` cell.
-   `failure_` holds the name of a test that failed if a test does fail.

```{.k .uiuck .rvk}
    syntax EthereumCommand ::= "exception" | "failure" String | "success"
 // ---------------------------------------------------------
    rule <k> exception => . ... </k> <op> #exception ... </op>
    rule <k> success => . ... </k> <exit-code> _ => 0 </exit-code>
    rule failure _ => .
```

### Running Tests

-   `run` runs a given set of Ethereum tests (from the test-set).

```{.k .uiuck .rvk}
    syntax EthereumCommand ::= "run" JSON
 // -------------------------------------
    rule run { .JSONList } => .
    rule run { TESTID : (TEST:JSON) , TESTS }
      => run (TESTID : TEST)
      ~> #if #hasPost?( TEST ) #then .K #else exception #fi
      ~> clear
      ~> run { TESTS }

    syntax Bool ::= "#hasPost?" "(" JSON ")" [function]
 // ---------------------------------------------------
    rule #hasPost? ({ .JSONList }) => false
    rule #hasPost? ({ (KEY:String) : _ , REST }) => KEY ==String "post" orBool #hasPost? ({ REST })

    syntax Set ::= "#postKeys" [function]
 // -------------------------------------
    rule #postKeys => (SetItem("post") SetItem("expect") SetItem("export") SetItem("expet"))
```

Here we make sure fields that are pre-conditions are `load`ed first, and post-conditions are `check`ed last.

```{.k .uiuck .rvk}
    rule run TESTID : { KEY : (VAL:JSON) , REST } => load KEY : VAL ~> run TESTID : { REST }
      requires KEY in (SetItem("env") SetItem("pre"))

    rule run TESTID : { "//" : _ , REST } => run TESTID : { REST }

    rule run TESTID : { KEY : (VAL:JSON) , REST } => run TESTID : { REST } ~> check TESTID : { KEY : VAL }
      requires KEY in (SetItem("logs") SetItem("callcreates") SetItem("out") SetItem("gas") #postKeys)
```

The particular key `"exec"` should be processed last, to ensure that the pre/post-conditions are in place.
When it has finished loading it's state, it should `start ~> flush` to perform the execution.

```{.k .uiuck .rvk}
    rule run TESTID : { "exec" : (EXEC:JSON) , NEXT , REST } => run TESTID : { NEXT , "exec" : EXEC , REST }
    rule run TESTID : { "exec" : (EXEC:JSON) } => load "exec" : EXEC ~> start ~> flush
```

State Manipulation
------------------

### Clearing State

-   `clear` clears all the execution state of the machine.

```{.k .uiuck .rvk}
    syntax EthereumCommand ::= "clear"
 // ----------------------------------
    rule <k> clear => . ... </k>

         <analysis> _ => .Map </analysis>

         <op>         _ => .          </op>
         <output>     _ => .WordStack </output>
         <memoryUsed> _ => 0:Word     </memoryUsed>
         <callDepth>  _ => 0:Word     </callDepth>
         <callStack>  _ => .List      </callStack>
         <callLog>    _ => .Set       </callLog>

         <program>     _ => .Map       </program>
         <id>          _ => 0:Word     </id>
         <caller>      _ => 0:Word     </caller>
         <callData>    _ => .WordStack </callData>
         <callValue>   _ => 0:Word     </callValue>
         <wordStack>   _ => .WordStack </wordStack>
         <localMem>    _ => .Map       </localMem>
         <pc>          _ => 0:Word     </pc>
         <gas>         _ => 0:Word     </gas>
         <previousGas> _ => 0:Word     </previousGas>

         <selfDestruct> _ => .Set   </selfDestruct>
         <log>          _ => .Set   </log>
         <refund>       _ => 0:Word </refund>

         <gasPrice>     _ => 0:Word </gasPrice>
         <origin>       _ => 0:Word </origin>
         <gasLimit>     _ => 0:Word </gasLimit>
         <coinbase>     _ => 0:Word </coinbase>
         <timestamp>    _ => 0:Word </timestamp>
         <number>       _ => 0:Word </number>
         <previousHash> _ => 0:Word </previousHash>
         <difficulty>   _ => 0:Word </difficulty>

         <activeAccounts> _ => .Set </activeAccounts>
         <accounts>       _ => .Bag </accounts>
         <messages>       _ => .Bag </messages>
```

### Loading State

-   `mkAcct_` creates an account with the supplied ID (assuming it's already been chopped to 160 bits).

```{.k .uiuck .rvk}
    syntax EthereumCommand ::= "mkAcct" Word
 // ----------------------------------------
    rule <k> mkAcct ACCT => . ... </k> <op> . => #newAccount ACCT </op>
```

-   `load` loads an account or transaction into the world state.

```{.k .uiuck .rvk}
    syntax DistCommand ::= "load"
 // -----------------------------
    rule load "pre" : { (ACCTID:String) : ACCT } => mkAcct #parseAddr(ACCTID) ~> load "account" : { ACCTID : ACCT }

    rule <k> load "account" : { ACCT : { "balance" : (BAL:Word) } } => . ... </k>
         <account>
           <acctID> ACCT </acctID>
           <balance> _ => BAL </balance>
           ...
         </account>

    rule <k> load "account" : { ACCT : { "code" : (CODE:Map) } } => . ... </k>
         <account>
           <acctID> ACCT </acctID>
           <code> _ => CODE </code>
           ...
         </account>

    rule <k> load "account" : { ACCT : { "nonce" : (NONCE:Word) } } => . ... </k>
         <account>
           <acctID> ACCT </acctID>
           <acctMap> AM => AM [ "nonce" <- NONCE ] </acctMap>
           ...
         </account>

    rule <k> load "account" : { ACCT : { "storage" : (STORAGE:Map) } } => . ... </k>
         <account>
           <acctID> ACCT </acctID>
           <storage> _ => STORAGE </storage>
           ...
         </account>
```

Here we load the environmental information.

```{.k .uiuck .rvk}
    rule load "env" : { KEY : ((VAL:String) => #parseWord(VAL)) }
      requires KEY in (SetItem("currentTimestamp") SetItem("currentGasLimit") SetItem("currentNumber") SetItem("currentDifficulty"))
    rule load "env" : { KEY : ((VAL:String) => #parseHexWord(VAL)) }
      requires KEY in (SetItem("currentCoinbase") SetItem("previousHash"))
 // ----------------------------------------------------------------------
    rule <k> load "env" : { "currentCoinbase"   : (CB:Word)     } => . ... </k> <coinbase>     _ => CB     </coinbase>
    rule <k> load "env" : { "currentDifficulty" : (DIFF:Word)   } => . ... </k> <difficulty>   _ => DIFF   </difficulty>
    rule <k> load "env" : { "currentGasLimit"   : (GLIMIT:Word) } => . ... </k> <gasLimit>     _ => GLIMIT </gasLimit>
    rule <k> load "env" : { "currentNumber"     : (NUM:Word)    } => . ... </k> <number>       _ => NUM    </number>
    rule <k> load "env" : { "previousHash"      : (HASH:Word)   } => . ... </k> <previousHash> _ => HASH   </previousHash>
    rule <k> load "env" : { "currentTimestamp"  : (TS:Word)     } => . ... </k> <timestamp>    _ => TS     </timestamp>

    rule load "exec" : { KEY : ((VAL:String) => #parseWord(VAL)) }
      requires KEY in (SetItem("gas") SetItem("gasPrice") SetItem("value"))
    rule load "exec" : { KEY : ((VAL:String) => #parseHexWord(VAL)) }
      requires KEY in (SetItem("address") SetItem("caller") SetItem("origin"))
 // --------------------------------------------------------------------------
    rule <k> load "exec" : { "gasPrice" : (GPRICE:Word)   } => . ... </k> <gasPrice>  _ => GPRICE   </gasPrice>
    rule <k> load "exec" : { "gas"      : (GAVAIL:Word)   } => . ... </k> <gas>       _ => GAVAIL   </gas>
    rule <k> load "exec" : { "address"  : (ACCTTO:Word)   } => . ... </k> <id>        _ => ACCTTO   </id>
    rule <k> load "exec" : { "caller"   : (ACCTFROM:Word) } => . ... </k> <caller>    _ => ACCTFROM </caller>
    rule <k> load "exec" : { "gas"      : (GAVAIL:Word)   } => . ... </k> <gas>       _ => GAVAIL   </gas>
    rule <k> load "exec" : { "value"    : (VALUE:Word)    } => . ... </k> <callValue> _ => VALUE    </callValue>
    rule <k> load "exec" : { "origin"   : (ORIG:Word)     } => . ... </k> <origin>    _ => ORIG     </origin>

    rule load "exec" : { "data" : ((DATA:String)  => #parseByteStack(DATA)) }
    rule load "exec" : { "code" : ((CODE:String)  => #dasmOpCodes(#parseByteStack(CODE))) }
    rule load "exec" : { "code" : ((CODE:OpCodes) => #asMapOpCodes(CODE)) }
 // -----------------------------------------------------------------------
    rule <k> load "exec" : { "data" : (DATA:WordStack) } => . ... </k> <callData> _ => DATA </callData>
    rule <k> load "exec" : { "code" : (CODE:Map)       } => . ... </k> <program>  _ => CODE </program>
```

### Checking State

-   `check_` checks if an account/transaction appears in the world-state as stated.

```{.k .uiuck .rvk}
    syntax EthereumCommand ::= "check" JSON
 // ---------------------------------------
    rule #exception ~> check J:JSON => check J ~> #exception
    rule check DATA : { .JSONList } => .
    rule check DATA : { (KEY:String) : VALUE , REST } => check DATA : { KEY : VALUE } ~> check DATA : { REST }
      requires REST =/=K .JSONList andBool notBool DATA in (SetItem("callcreates") SetItem("logs"))

    rule check DATA : [ .JSONList ] => .
    rule check DATA : [ { TEST } , REST ] => check DATA : { TEST } ~> check DATA : [ REST ]

    rule check (KEY:String) : { JS:JSONList => #sortJSONList(JS) }
      requires KEY in (SetItem("logs") SetItem("callcreates")) andBool notBool #isSorted(JS)

    rule check TESTID : { KEY : POST } => check "account" : POST ~> failure TESTID requires KEY in #postKeys
    rule check "account" : { ACCTID: { KEY : VALUE , REST } } => check "account" : { ACCTID : { KEY : VALUE } } ~> check "account" : { ACCTID : { REST } } requires REST =/=K .JSONList
 // -----------------------------------------------------------------------------------------------------------------------------------------------------------------------------------
    rule check "account" : { ((ACCTID:String) => #parseAddr(ACCTID)) : ACCT }
    rule check "account" : { (ACCT:Word) : { "balance" : ((VAL:String)         => #parseWord(VAL)) } }
    rule check "account" : { (ACCT:Word) : { "nonce"   : ((VAL:String)         => #parseWord(VAL)) } }
    rule check "account" : { (ACCT:Word) : { "code"    : ((CODE:String)        => #dasmOpCodes(#parseByteStack(CODE))) } }
    rule check "account" : { (ACCT:Word) : { "code"    : ((CODE:OpCodes)       => #asMapOpCodes(CODE)) } }
    rule check "account" : { (ACCT:Word) : { "storage" : ({ STORAGE:JSONList } => #parseMap({ STORAGE })) } }

    rule <k> check "account" : { ACCT : { "balance" : (BAL:Word) } } => . ... </k>
         <account>
           <acctID> ACCT </acctID>
           <balance> BAL </balance>
           ...
         </account>

    rule <k> check "account" : { ACCT : { "nonce" : (NONCE:Word) } } => . ... </k>
         <account>
           <acctID> ACCT </acctID>
           <acctMap> "nonce" |-> NONCE </acctMap>
           ...
         </account>

    rule <k> check "account" : { ACCT : { "storage" : (STORAGE:Map) } } => . ... </k>
         <account>
           <acctID> ACCT </acctID>
           <storage> STORAGE </storage>
           ...
         </account>

    rule <k> check "account" : { ACCT : { "code" : (CODE:Map) } } => . ... </k>
         <account>
           <acctID> ACCT </acctID>
           <code> CODE </code>
           ...
         </account>
```

Here we check the other post-conditions associated with an EVM test.

```{.k .uiuck .rvk}
    rule check TESTID : { "out" : OUT } => check "out" : OUT ~> failure TESTID
 // --------------------------------------------------------------------------
    rule check "out" : ((OUT:String) => #parseByteStack(OUT))
    rule <k> check "out" : OUT => . ... </k> <output> OUT </output>

    rule check TESTID : { "logs" : LOGS } => check "logs" : LOGS ~> failure TESTID
 // ------------------------------------------------------------------------------
    rule check "logs" : { ("address" : (ACCT:String)) , ("bloom" : (BLOOM:String)) , ("data" : (DATA:String)) , ("topics" : (TOPICS:JSON)) , .JSONList }
      => check "logs" : { #parseAddr(ACCT) | #parseWordStack(TOPICS) | #parseByteStack(DATA) }
    rule <k> check "logs" : SLE:SubstateLogEntry => . ... </k> <log> SL </log> requires SLE in SL

    rule check TESTID : { "gas" : GLEFT } => check "gas" : GLEFT ~> failure TESTID
 // ------------------------------------------------------------------------------
    rule check "gas" : ((GLEFT:String) => #parseWord(GLEFT))
    rule <k> check "gas" : GLEFT => . ... </k> <gas> GLEFT </gas>
```

```{.k .uiuck .rvk}
    rule check TESTID : { "callcreates" : CCREATES } => check "callcreates" : CCREATES ~> failure TESTID
 // ----------------------------------------------------------------------------------------------------
    rule check "callcreates" : { ("data" : (DATA:String)) , ("destination" : (ACCTTO:String)) , ("gasLimit" : (GLIMIT:String)) , ("value" : (VAL:String)) , .JSONList }
      => check "callcreates" : { #parseAddr(ACCTTO) | #parseWord(GLIMIT) | #parseWord(VAL) | #parseByteStack(DATA) }
    rule <k> check "callcreates" : C:Call => . ... </k> <callLog> CL </callLog> requires C in CL
endmodule
```
