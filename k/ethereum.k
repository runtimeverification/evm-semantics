// Ethereum Simulations
// ====================

// Ethereum is using the EVM to drive updates over the world state. Actual
// execution of the EVM is defined in [the EVM file](evm.md).


requires "evm.k"

module ETHEREUM-SIMULATION
    imports ETHEREUM


// An Ethereum simulation is a list of Ethereum commands. Some Ethereum commands
// take an Ethereum specification (eg. for an account or transaction).


    syntax EthereumSimulation ::= ".EthereumSimulation"
                                | EthereumCommand EthereumSimulation
 // ----------------------------------------------------------------
    rule .EthereumSimulation => .
    rule ETC:EthereumCommand ETS:EthereumSimulation => ETC ~> ETS

    syntax EthereumSimulation ::= JSON
 // ----------------------------------
    rule JSONINPUT:JSON => run JSONINPUT .EthereumSimulation

    syntax EthereumCommand ::= DistCommand JSON
 // -------------------------------------------
    rule DC:DistCommand DATA : { .JSONList } => .
    rule DC:DistCommand DATA : { KEY : VALUE , REST } => DC DATA : { KEY : VALUE } ~> DC DATA : { REST } requires REST =/=K .JSONList

    rule DC:DistCommand DATA : [ .JSONList ] => .
    rule DC:DistCommand DATA : [ { TEST } , REST ] => DC DATA : { TEST } ~> DC DATA : [ REST ]


// For verification purposes, it's much easier to specify a program in terms of its
// op-codes and not the hex-encoding that the tests use. To do so, we'll extend
// sort `JSON` with some EVM specific syntax, and provide a "pretti-fication" to
// the nicer input form.


    syntax JSON ::= Word | WordStack | OpCodes | Map | Call
 // -------------------------------------------------------
    rule DC:DistCommand "account" : { ACCTID: { KEY : VALUE , REST } } => DC "account" : { ACCTID : { KEY : VALUE } } ~> DC "account" : { ACCTID : { REST } } requires REST =/=K .JSONList

    rule DC:DistCommand "account" : { ((ACCTID:String) => #addr(#parseHexWord(ACCTID))) : ACCT }
    rule DC:DistCommand "account" : { (ACCT:Word) : { "balance" : ((VAL:String)   => #parseHexWord(VAL)) } }
    rule DC:DistCommand "account" : { (ACCT:Word) : { "nonce"   : ((VAL:String)   => #parseHexWord(VAL)) } }
    rule DC:DistCommand "account" : { (ACCT:Word) : { "code"    : ((CODE:String)  => #dasmOpCodes(#parseByteStack(CODE))) } }
    rule DC:DistCommand "account" : { (ACCT:Word) : { "code"    : ((CODE:OpCodes) => #asMapOpCodes(CODE)) } }
    rule DC:DistCommand "account" : { (ACCT:Word) : { "storage" : ((STORAGE:JSON) => #parseMap(STORAGE)) } }


// ### Driving Execution

// -   `start` places `#next` on the `op` cell so that execution of the loaded
//     state begin.
// -   `flush` places `#finalize` on the `op` cell once it sees `#end` in the `op`
//     cell. If it sees an exception on the top of the cell, it simply clears.


    syntax EthereumCommand ::= "start" | "flush"
 // --------------------------------------------
    rule <k> start => . ... </k> <op> . => #next </op>
    rule <k> flush => . ... </k> <op> #end        => #finalize </op>
    rule <k> flush => . ... </k> <op> #exception  => .         </op>


// -   `exception` only clears from the `k` cell if there is an exception on the
//     `op` cell.
// -   `failure_` holds the name of a test that failed if a test does fail.


    syntax EthereumCommand ::= "exception" | "failure" String
 // ---------------------------------------------------------
    rule <k> exception _ => . ... </k> <op> #exception ... </op>
    rule failure _ => .


// ### Running Tests

// -   `run` runs a given set of Ethereum tests (from the test-set).


    syntax EthereumCommand ::= "run" JSON
 // -------------------------------------
    rule run { .JSONList } => .
    rule run { TESTID : (TEST:JSON) , TESTS } => run (TESTID : TEST) ~> clear ~> run { TESTS }


// Here we make sure fields that are pre-conditions are `load`ed first, and
// post-conditions are `check`ed last.


    rule run TESTID : { KEY : (VAL:JSON) , REST } => load KEY : VAL ~> run TESTID : { REST }
      requires KEY in (SetItem("env") SetItem("pre"))

    rule run TESTID : { KEY : (VAL:JSON) , REST } => run TESTID : { REST } ~> check TESTID : { KEY : VAL }
      requires KEY in (SetItem("logs") SetItem("callcreates") SetItem("out") SetItem("post") SetItem("expect") SetItem("gas"))


// The particular key `"exec"` should be processed last, to ensure that the
// pre/post-conditions are in place. When it has finished loading it's state, it
// should `start ~> flush` to perform the execution.


    rule run TESTID : { "exec" : (EXEC:JSON) , NEXT , REST } => run TESTID : { NEXT , "exec" : EXEC , REST }
    rule run TESTID : { "exec" : (EXEC:JSON) } => load "exec" : EXEC ~> start ~> flush


// State Manipulation
// ------------------

// ### Clearing State

// -   `clear` clears all the execution state of the machine.


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


// ### Loading State

// -   `mkAcct_` creates an account with the supplied ID (assuming it's already
//     been chopped to 160 bits).


    syntax EthereumCommand ::= "mkAcct" Word
 // ----------------------------------------
    rule <k> mkAcct ACCT => . ... </k> <op> . => #newAccount ACCT </op>


// -   `load` loads an account or transaction into the world state.


    syntax DistCommand ::= "load"
 // -----------------------------
    rule load "pre" : { (ACCTID:String) : ACCT } => mkAcct #addr(#parseHexWord(ACCTID)) ~> load "account" : { ACCTID : ACCT }

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


// Here we load the environmental information.


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


// ### Checking State

// -   `check_` checks if an account/transaction appears in the world-state
//     as stated.


    syntax DistCommand ::= "check"
 // --------------------------------------
    rule check DATA : { .JSONList } => .
    rule check DATA : { (KEY:String) : VALUE , REST } => check DATA : { KEY : VALUE } ~> check DATA : { REST } requires REST =/=K .JSONList

    rule check DATA : [ .JSONList ] => .
    rule check DATA : [ { TEST } , REST ] => check DATA : { TEST } ~> check DATA : [ REST ]


// There seem to be some typos/inconsistencies in the test set requiring us to
// handle the cases of `"expect"` and `"export"`.


    rule check TESTID : { "expect" : POST } => check "account" : POST ~> failure TESTID
    rule check TESTID : { "export" : POST } => check "account" : POST ~> failure TESTID
    rule check TESTID : { "post"   : POST } => check "account" : POST ~> failure TESTID
 // -------------------------------------------------------------------------------------
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


// TODO: `check` on `"callcreates"` ignores the `"gasLimit"` field.


    rule check TESTID : { "callcreates" : CCREATES } => check "callcreates" : CCREATES ~> failure TESTID
 // ----------------------------------------------------------------------------------------------------
    rule check "callcreates" : { "value" : VAL , "destination" : ACCTTO , "gasLimit" : GLIMIT , "data" : DATA }
      => check "callcreates" : { #addr(#parseHexWord(ACCTTO)) | #parseHexWord(VAL) | #parseByteStack(DATA) }
    rule <k> check "callcreates" : C:Call => . ... </k> <callLog> CL </callLog> requires C in CL

    rule check TESTID : { "out" : OUT } => check "out" : OUT ~> failure TESTID
 // --------------------------------------------------------------------------
    rule check "out" : ((OUT:String) => #parseByteStack(OUT))
    rule <k> check "out" : OUT => . ... </k> <output> OUT </output>


// TODO: `check` on `"gas"` and `"logs"` is dropped.


    rule check TESTID : { "gas" : GLEFT } => check "gas" : GLEFT ~> failure TESTID
 // ------------------------------------------------------------------------------
    rule check "gas" : ((GLEFT:String) => #parseHexWord(GLEFT))
    rule check "gas" : GLEFT => .

    rule check TESTID : { "logs" : LOGS } => check "logs" : LOGS ~> failure TESTID
 // ------------------------------------------------------------------------------
    rule check "logs" : LOGS => .
endmodule

