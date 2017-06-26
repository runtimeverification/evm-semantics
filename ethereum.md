Ethereum Simulations
====================

Ethereum is using the EVM to drive updates over the world state.
Actual execution of the EVM is defined in [the EVM file](evm.md).

```k
requires "evm.k"

module ETHEREUM-SIMULATION
    imports ETHEREUM

```

An Ethereum simulation is a list of Ethereum commands.
Some Ethereum commands take an Ethereum specification (eg. for an account or transaction).

```k
    syntax EthereumSimulation ::= ".EthereumSimulation"
                                | EthereumCommand EthereumSimulation
 // ----------------------------------------------------------------
    rule .EthereumSimulation => .
    rule ETC:EthereumCommand ETS:EthereumSimulation => ETC ~> ETS

    syntax EthereumCommand ::= EthereumSpecCommand JSON
                             | "{" EthereumSimulation "}"
 // -----------------------------------------------------
    rule <k> { ES:EthereumSimulation } => ES ... </k>

    syntax EthereumSimulation ::= JSON
 // ----------------------------------
    rule JSONINPUT:JSON => run JSONINPUT success .EthereumSimulation
```

Pretty Ethereum Input
---------------------

For verification purposes, it's much easier to specify a program in terms of its op-codes and not the hex-encoding that the tests use.
To do so, we'll extend sort `JSON` with some EVM specific syntax.

```k
    syntax JSON ::= Word | WordStack | OpCodes | Map | Call
 // -------------------------------------------------------
```

Primitive Commands
------------------

### Clearing State

-   `clear` clears all the execution state of the machine.

```k
    syntax EthereumCommand ::= "clear"
 // ----------------------------------
    rule <k> clear => . ... </k>

         <op>         _ => .          </op>
         <output>     _ => .WordStack </output>
         <memoryUsed> _ => 0:Word     </memoryUsed>
         <callDepth>  _ => 0:Word     </callDepth>
         <callLog>    _ => .CallLog   </callLog>

         <program>   _ => .Map       </program>
         <id>        _ => 0:Word     </id>
         <caller>    _ => 0:Word     </caller>
         <callData>  _ => .WordStack </callData>
         <callValue> _ => 0:Word     </callValue>
         <wordStack> _ => .WordStack </wordStack>
         <localMem>  _ => .Map       </localMem>
         <pc>        _ => 0:Word     </pc>
         <gas>       _ => 0:Word     </gas>

         <selfDestruct> _ => .Set         </selfDestruct>
         <log>          _ => .SubstateLog </log>
         <refund>       _ => 0:Word       </refund>

         <gasPrice>   _ => 0:Word </gasPrice>
         <origin>     _ => 0:Word </origin>
         <gasLimit>   _ => 0:Word </gasLimit>
         <coinbase>   _ => 0:Word </coinbase>
         <timestamp>  _ => 0:Word </timestamp>
         <number>     _ => 0:Word </number>
         <difficulty> _ => 0:Word </difficulty>

         <activeAccounts> _ => .Set </activeAccounts>
         <accounts>       _ => .Bag </accounts>
         <messages>       _ => .Bag </messages>
```

### Loading State

-   `mkAcct_` creates an account with the supplied ID.
-   `load_` loads an account or transaction into the world state.

```k
    syntax EthereumSpecCommand ::= "mkAcct"
 // ---------------------------------------
    rule <k> mkAcct (ACCTID:String) => . ... </k> <op> . => #newAccount #parseHexWord(ACCTID) </op>

    syntax EthereumSpecCommand ::= "load"
 // -------------------------------------
    rule load DATA : { .JSONList } => .
    rule load DATA : { (KEY:String) : VAL , REST } => load DATA : { KEY : VAL } ~> load DATA : { REST } requires REST =/=K .JSONList
```

Here we load the relevant information for accounts.

```k
    rule load "pre" : { (ACCTID:String) : ACCT } => mkAcct ACCTID ~> load "account" : { ACCTID : ACCT }
 // ---------------------------------------------------------------------------------------------------
    rule load "account" : { .JSONList } => .
    rule load "account" : { ACCTID : { (KEY:String) : VAL , REST } } => load "account" : { ACCTID : { KEY : VAL } } ~> load "account" : { ACCTID : { REST } } requires REST =/=K .JSONList

    rule load "account" : { ACCTID : { "balance" : ((BAL:String) => #parseHexWord(BAL)) } }
    rule <k> load "account" : { ACCTID : { "balance" : (BAL:Word) } } => . ... </k>
         <account>
           <acctID> ACCT </acctID>
           <balance> _ => BAL </balance>
           ...
         </account>
      requires #addr(#parseHexWord(ACCTID)) ==K ACCT

    rule load "account" : { ACCTID : { "code" : ((CODE:String) => #dasmOpCodes(#parseByteStack(CODE))) } }
    rule load "account" : { ACCTID : { "code" : ((CODE:OpCodes) => #asMapOpCodes(CODE)) } }
    rule <k> load "account" : { ACCTID : { "code" : (CODE:Map) } } => . ... </k>
         <account>
           <acctID> ACCT </acctID>
           <code> _ => CODE </code>
           ...
         </account>
      requires #addr(#parseHexWord(ACCTID)) ==K ACCT

    rule load "account" : { ACCTID : { "nonce" : ((NONCE:String) => #parseHexWord(NONCE)) } }
    rule <k> load "account" : { ACCTID : { "nonce" : (NONCE:Word) } } => . ... </k>
         <account>
           <acctID> ACCT </acctID>
           <acctMap> AM => AM [ "nonce" <- NONCE ] </acctMap>
           ...
         </account>
      requires #addr(#parseHexWord(ACCTID)) ==K ACCT

    rule load "account" : { ACCTID : { "storage" : ((STORAGE:JSON) => #parseMap(STORAGE)) } } requires notBool isMap(STORAGE)
    rule <k> load "account" : { ACCTID : { "storage" : (STORAGE:Map) } } => . ... </k>
         <account>
           <acctID> ACCT </acctID>
           <storage> _ => STORAGE </storage>
           ...
         </account>
      requires #addr(#parseHexWord(ACCTID)) ==K ACCT
```

Here we load the environmental information.

```k
    rule load "env" : { KEY : ((VAL:String) => #parseHexWord(VAL)) }
 // ----------------------------------------------------------------
    rule <k> load "env" : { "currentCoinbase"   : (CB:Word)     } => . ... </k> <coinbase>   _ => CB     </coinbase>
    rule <k> load "env" : { "currentDifficulty" : (DIFF:Word)   } => . ... </k> <difficulty> _ => DIFF   </difficulty>
    rule <k> load "env" : { "currentGasLimit"   : (GLIMIT:Word) } => . ... </k> <gasLimit>   _ => GLIMIT </gasLimit>
    rule <k> load "env" : { "currentNumber"     : (NUM:Word)    } => . ... </k> <number>     _ => NUM    </number>
    rule <k> load "env" : { "currentTimestamp"  : (TS:Word)     } => . ... </k> <timestamp>  _ => TS     </timestamp>

    rule load "exec" : { KEY : ((VAL:String) => #parseHexWord(VAL)) }
      requires KEY in (SetItem("address") SetItem("caller") SetItem("gas") SetItem("gasPrice") SetItem("value") SetItem("origin"))
 // ------------------------------------------------------------------------------------------------------------------------------
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

### Driving Execution

-   `start` places `#next` on the `op` cell so that execution of the loaded state begin.
-   `flush` places `#finalize` on the `op` cell once it sees `#end` in the `op` cell.
    If it sees an exception on the top of the cell, it simply clears.

```k
    syntax EthereumCommand ::= "start" | "flush"
 // --------------------------------------------
    rule <k> start => . ... </k> <op> . => #next </op>
    rule <k> flush => . ... </k> <op> #end        => #finalize </op>
    rule <k> flush => . ... </k> <op> #exception  => .         </op>
```

### Checking State

-   `check_` checks if an account/transaction appears in the world-state as stated.

```k
    syntax EthereumSpecCommand ::= "check"
 // --------------------------------------
    rule check DATA : { .JSONList } => .
    rule check DATA : { (KEY:String) : VALUE , REST } => check DATA : { KEY : VALUE } ~> check DATA : { REST } requires REST =/=K .JSONList

    rule check DATA : [ .JSONList ] => .
    rule check DATA : [ { TEST } , REST ] => check DATA : { TEST } ~> check DATA : [ REST ]
```

There seem to be some typos/inconsistencies in the test set requiring us to handle the cases of `"expect"` and `"export"`.

```k
    rule check TESTID : { "expect" : POST } => check "post" : POST ~> failure TESTID
    rule check TESTID : { "export" : POST } => check "post" : POST ~> failure TESTID
    rule check TESTID : { "post"   : POST } => check "post" : POST ~> failure TESTID
    rule check "post" : { (ACCTID:String) : ACCT } => check ACCTID : ACCT
 // ---------------------------------------------------------------------
    rule check ACCTID : { "balance" : ((BAL:String) => #parseHexWord(BAL)) }
    rule <k> check ACCTID : { "balance" : (BAL:Word) } => . ... </k>
         <account>
           <acctID> ACCT </acctID>
           <balance> BAL </balance>
           ...
         </account>
      requires #addr(#parseHexWord(ACCTID)) ==K ACCT

    rule check ACCTID : { "nonce" : ((NONCE:String) => #parseHexWord(NONCE)) }
    rule <k> check ACCTID : { "nonce" : (NONCE:Word) } => . ... </k>
         <account>
           <acctID> ACCT </acctID>
           <acctMap> "nonce" |-> NONCE </acctMap>
           ...
         </account>
      requires #addr(#parseHexWord(ACCTID)) ==K ACCT

    rule check ACCTID : { "storage" : ((STORAGE:JSON) => #parseMap(STORAGE)) } requires notBool isMap(STORAGE)
    rule <k> check ACCTID : { "storage" : (STORAGE:Map) } => . ... </k>
         <account>
           <acctID> ACCT </acctID>
           <storage> STORAGE </storage>
           ...
         </account>
      requires #addr(#parseHexWord(ACCTID)) ==K ACCT

    rule check ACCTID : { "code" : ((CODE:String) => #dasmOpCodes(#parseByteStack(CODE))) }
    rule check ACCTID : { "code" : ((CODE:OpCodes) => #asMapOpCodes(CODE)) }
    rule <k> check ACCTID : { "code" : (CODE:Map) } => . ... </k>
         <account>
           <acctID> ACCT </acctID>
           <code> CODE </code>
           ...
         </account>
      requires #addr(#parseHexWord(ACCTID)) ==K ACCT
```

TODO: `check` on `"callcreates"` ignores the `"gasLimit"` field.

```k
    rule check TESTID : { "callcreates" : CCREATES } => check "callcreates" : CCREATES ~> failure TESTID
 // ----------------------------------------------------------------------------------------------------
    rule check "callcreates" : { "value" : VAL , "destination" : ACCTTO , "gasLimit" : GLIMIT , "data" : DATA }
      => check "callcreates" : { #addr(#parseHexWord(ACCTTO)) | #parseHexWord(VAL) | #parseByteStack(DATA) }
    rule <k> check "callcreates" : C:Call => . ... </k> <callLog> CL </callLog> requires C in CL

    rule check TESTID : { "out" : OUT } => check "out" : OUT ~> failure TESTID
 // --------------------------------------------------------------------------
    rule check "out" : ((OUT:String) => #parseByteStack(OUT))
    rule <k> check "out" : OUT => . ... </k> <output> OUT </output>
```

TODO: `check` on `"gas"` and `"logs"` is dropped.

```k
    rule check TESTID : { "gas" : GLEFT } => check "gas" : GLEFT ~> failure TESTID
 // ------------------------------------------------------------------------------
    rule check "gas" : ((GLEFT:String) => #parseHexWord(GLEFT))
    rule check "gas" : GLEFT => .

    rule check TESTID : { "logs" : LOGS } => check "logs" : LOGS ~> failure TESTID
 // ------------------------------------------------------------------------------
    rule check "logs" : LOGS => .
```

### Running Tests

-   `run` runs a given set of Ethereum tests (from the test-set).

```k
    syntax EthereumCommand ::= "success" | "exception" String | "failure" String
 // ----------------------------------------------------------------------------
    rule <k> exception _ => . ... </k> <op> #exception ... </op>
    rule <k> success   => . ... </k> <exit-code> _ => 0 </exit-code>
    rule failure _ => .

    syntax EthereumSpecCommand ::= "run"
 // ------------------------------------
    rule run { .JSONList } => .
    rule run { TESTID : (TEST:JSON)
             , TESTS
             }
      =>    run (TESTID : TEST)
         ~> clear
         ~> run { TESTS }
```

Here we make sure fields that are pre-conditions are `load`ed first, and post-conditions are `check`ed last.

```k
    rule run TESTID : { KEY : (VAL:JSON) , REST } => load KEY : VAL ~> run TESTID : { REST }
      requires KEY in (SetItem("env") SetItem("pre"))

    rule run TESTID : { KEY : (VAL:JSON) , REST } => run TESTID : { REST } ~> check TESTID : { KEY : VAL }
      requires KEY in (SetItem("logs") SetItem("callcreates") SetItem("out") SetItem("post") SetItem("expect") SetItem("gas"))
```

The particular key `"exec"` should be processed last, to ensure that the pre/post-conditions are in place.
When it has finished loading it's state, it should `start ~> flush` to perform the execution.

```k
    rule run TESTID : { "exec" : (EXEC:JSON) , NEXT , REST } => run TESTID : { NEXT , "exec" : EXEC , REST }
    rule run TESTID : { "exec" : (EXEC:JSON) } => load "exec" : EXEC ~> start ~> flush
endmodule
```
