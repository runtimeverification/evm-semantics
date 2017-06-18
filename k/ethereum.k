// Ethereum Simulations
// ====================

// Ethereum is using the EVM to drive updates over the world state. Actual
// execution of the EVM is defined in [the EVM file](evm.md).


requires "evm.k"
requires "evm-dasm.k"

module ETHEREUM-SIMULATION
    imports ETHEREUM
    imports EVM-DASM

    configuration initEthereumCell
                  <k> $PGM:EthereumSimulation </k>


// An Ethereum simulation is a list of Ethereum commands. Some Ethereum commands
// take an Ethereum specification (eg. for an account or transaction).


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


// Primitive Commands
// ------------------

// ### Clearing State

// -   `clear` clears all the execution state of the machine.


    syntax EthereumCommand ::= "clear"
 // ----------------------------------
    rule <k> clear => . ... </k>
         <currOps> COPS      => .Set  </currOps>
         <prevOps> ... (.Set => COPS) </prevOps>

         <op>         _ => .          </op>
         <output>     _ => .WordStack </output>
         <memoryUsed> _ => 0:Word     </memoryUsed>
         <callStack>  _ => .CallStack </callStack>

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

// -   `mkAcct_` creates an account with the supplied ID.
// -   `load_` loads an account or transaction into the world state.


    syntax EthereumSpecCommand ::= "mkAcct"
 // ---------------------------------------
    rule <k> mkAcct ACCTID => . ... </k> <op> . => #newAccount #parseHexWord(ACCTID) </op>

    syntax EthereumSpecCommand ::= "load"
 // -------------------------------------
    rule load DATA : { .JSONList }        => .
    rule load DATA : { KEY : VAL , REST } => load DATA : { KEY : VAL } ~> load DATA : { REST } requires REST =/=K .JSONList


// Here we load the relevant information for accounts.


    rule load "pre" : { ACCTID : ACCT } => mkAcct ACCTID ~> load "account" : { ACCTID : ACCT }

    rule load "account" : { .JSONList } => .
    rule load "account" : { ACCTID : { KEY : VAL , REST } } => load "account" : { ACCTID : { KEY : VAL } } ~> load "account" : { ACCTID : { REST } } requires REST =/=K .JSONList

    rule <k> load "account" : { ACCTID : { "balance" : (BAL:String) } } => . ... </k>
         <account>
           <acctID> ACCT </acctID>
           <balance> _ => #parseHexWord(BAL) </balance>
           ...
         </account>
      requires #addr(#parseHexWord(ACCTID)) ==K ACCT

    rule <k> load "account" : { ACCTID : { "code" : (CODE:String) } } => . ... </k>
         <account>
           <acctID> ACCT </acctID>
           <code> _ => #asMap(#dasmOpCodes(#parseByteStack(CODE))) </code>
           ...
         </account>
      requires #addr(#parseHexWord(ACCTID)) ==K ACCT

    rule <k> load "account" : { ACCTID : { "nonce" : (NONCE:String) } } => . ... </k>
         <account>
           <acctID> ACCT </acctID>
           <acctMap> AM => AM [ "nonce" <- #parseHexWord(NONCE) ] </acctMap>
           ...
         </account>
      requires #addr(#parseHexWord(ACCTID)) ==K ACCT

    rule <k> load "account" : { ACCTID : { "storage" : (STORAGE:JSON) } } => . ... </k>
         <account>
           <acctID> ACCT </acctID>
           <storage> _ => #parseMap(STORAGE) </storage>
           ...
         </account>
      requires #addr(#parseHexWord(ACCTID)) ==K ACCT


// Here we load the environmental information.


    rule <k> load "gas" : GAVAIL => . ... </k> <gas> _ => #parseHexWord(GAVAIL) </gas>

    rule <k> load "env" : { "currentCoinbase"   : (CB:String)     } => . ... </k> <coinbase>   _ => #parseHexWord(CB)     </coinbase>
    rule <k> load "env" : { "currentDifficulty" : (DIFF:String)   } => . ... </k> <difficulty> _ => #parseHexWord(DIFF)   </difficulty>
    rule <k> load "env" : { "currentGasLimit"   : (GLIMIT:String) } => . ... </k> <gasLimit>   _ => #parseHexWord(GLIMIT) </gasLimit>
    rule <k> load "env" : { "currentNumber"     : (NUM:String)    } => . ... </k> <number>     _ => #parseHexWord(NUM)    </number>
    rule <k> load "env" : { "currentTimestamp"  : (TS:String)     } => . ... </k> <timestamp>  _ => #parseHexWord(TS)     </timestamp>

    rule <k> load "exec" : { "address"  : (ACCTTO:String)   } => . ... </k> <id>        _ => #parseHexWord(ACCTTO)                       </id>
    rule <k> load "exec" : { "caller"   : (ACCTFROM:String) } => . ... </k> <caller>    _ => #parseHexWord(ACCTFROM)                     </caller>
    rule <k> load "exec" : { "data"     : (DATA:String)     } => . ... </k> <callData>  _ => #parseByteStack(DATA)                       </callData>
    rule <k> load "exec" : { "gas"      : (GAVAIL:String)   } => . ... </k> <gas>       _ => #parseHexWord(GAVAIL)                       </gas>
    rule <k> load "exec" : { "gasPrice" : (GPRICE:String)   } => . ... </k> <gasPrice>  _ => #parseHexWord(GPRICE)                       </gasPrice>
    rule <k> load "exec" : { "value"    : (VALUE:String)    } => . ... </k> <callValue> _ => #parseHexWord(VALUE)                        </callValue>
    rule <k> load "exec" : { "origin"   : (ORIG:String)     } => . ... </k> <origin>    _ => #parseHexWord(ORIG)                         </origin>
    rule <k> load "exec" : { "code"     : (CODE:String)     } => . ... </k> <program>   _ => #asMap(#dasmOpCodes(#parseByteStack(CODE))) </program>


// ### Driving Execution

// -   `start` places `#next` on the `op` cell so that execution of the loaded
//     state begin.
// -   `flush` places `#finalize` on the `op` cell once it sees `#endOfProgram` in
//     the `op` cell. If it sees an exception on the top of the cell, it
//     simply clears.


    syntax EthereumCommand ::= "start" | "flush"
 // --------------------------------------------
    rule <k> start => . ... </k> <op> . => #next </op>
    rule <k> flush => . ... </k> <op> #endOfProgram => #finalize ... </op>
    rule <k> flush => . ... </k> <op> #txFinished   => #finalize ... </op>
    rule <k> flush => . ... </k> <op> EX:Exception  => .         ... </op>


// ### Checking State

// -   `check_` checks if an account/transaction appears in the world-state
//     as stated.


    syntax EthereumSpecCommand ::= "check"
 // --------------------------------------
    rule check DATA : { .JSONList } => .
    rule check DATA : { KEY : VALUE , REST } => check DATA : { KEY : VALUE } ~> check DATA : { REST } requires REST =/=K .JSONList

    rule check "post" : { ACCTID : ACCT } => check ACCTID : ACCT
    rule check TESTID : { "post" : POST } => check "post" : POST ~> failure TESTID
    rule check TESTID : { "out"  : OUT  } => check "out"  : OUT  ~> failure TESTID

    rule <k> check ACCTID : { "balance" : (VAL:String) } => . ... </k>
         <account>
           <acctID> ACCT </acctID>
           <balance> BAL </balance>
           ...
         </account>
      requires #addr(#parseHexWord(ACCTID)) ==K ACCT andBool #parseHexWord(VAL) ==K BAL

    rule <k> check ACCTID : { "nonce" : (VAL:String) } => . ... </k>
         <account>
           <acctID> ACCT </acctID>
           <acctMap> "nonce" |-> NONCE </acctMap>
           ...
         </account>
      requires #addr(#parseHexWord(ACCTID)) ==K ACCT andBool #parseHexWord(VAL) ==K NONCE

    rule <k> check ACCTID : { "storage" : (STG:JSON) } => . ... </k>
         <account>
           <acctID> ACCT </acctID>
           <storage> STORAGE </storage>
           ...
         </account>
      requires #addr(#parseHexWord(ACCTID)) ==K ACCT andBool #parseMap(STG) ==K STORAGE

    rule <k> check ACCTID : { "code" : (PGM:String) } => . ... </k>
         <account>
           <acctID> ACCT </acctID>
           <code> CODE </code>
           ...
         </account>
      requires #addr(#parseHexWord(ACCTID)) ==K ACCT andBool #asMap(#dasmOpCodes(#parseByteStack(PGM))) ==K CODE

    rule <k> check "out" : (OUT:String) => . ... </k>
         <output> CURROUT </output>
      requires #parseByteStack(OUT) ==K CURROUT


// ### Running Tests

// -   `run` runs a given set of Ethereum tests (from the test-set).


    syntax EthereumCommand ::= "success" | "exception" String | "failure" String
 // ----------------------------------------------------------------------------
    rule <k> success     => . ... </k> <currOps> _ => .Set </currOps> <prevOps> _ => .Set </prevOps>
    rule <k> exception _ => . ... </k> <op> EX:Exception ... </op>
    rule failure _ => .

    syntax EthereumSpecCommand ::= "run"
 // ------------------------------------
    rule run { .JSONList } => .
    rule run { TESTID : (TEST:JSON)
             , TESTS
             }
      =>
         { run (TESTID : TEST)
           clear
           run { TESTS }
           .EthereumSimulation
         }

    rule JSONINPUT:JSON => run JSONINPUT success .EthereumSimulation


// TODO: The fields "callcreates" and "logs" should be dealt with properly.


    rule run TESTID : { "callcreates" : (CCREATES:JSON) , REST } => run TESTID : { REST }
    rule run TESTID : { "logs"        : (LOGS:JSON)     , REST } => run TESTID : { REST }
    rule run TESTID : { "out"         : (OUT:JSON)      , REST } => run TESTID : { REST } ~> check TESTID : { "out"  : OUT }
    rule run TESTID : { "post"        : (POST:JSON)     , REST } => run TESTID : { REST } ~> check TESTID : { "post" : POST }
    rule run TESTID : { "expect"      : (EXPECT:JSON)   , REST } => run TESTID : { REST } ~> check TESTID : { "post" : EXPECT }


// Here we pull apart a test into the sequence of `EthereumCommand` to run for it.


    rule run TESTID : { "env"  : (ENV:JSON)         , REST } => load "env" : ENV      ~> run TESTID : { REST }
    rule run TESTID : { "gas"  : (CURRGAS:String)   , REST } => load "gas" : CURRGAS  ~> run TESTID : { REST }
    rule run TESTID : { "pre"  : (PRE:JSON)         , REST } => load "pre" : PRE      ~> run TESTID : { REST }
    rule run TESTID : { "exec" : (EXEC:JSON) , NEXT , REST } => run TESTID : { NEXT , "exec" : EXEC , REST }

    rule run TESTID : { "exec" : (EXEC:JSON) } => run "exec" : EXEC ~> start ~> flush
    rule run "exec" : { .JSONList } => .
    rule run "exec" : { KEY    : VALUE             } => load "exec" : { KEY : VALUE }
    rule run "exec" : { KEY    : VALUE , REST      } => load "exec" : { KEY : VALUE } ~> run  "exec" : { REST }          requires REST =/=K .JSONList andBool KEY =/=K "code"
    rule run "exec" : { "code" : CODE  , REST      } => run  "exec" : { REST }        ~> load "exec" : { "code" : CODE } requires REST =/=K .JSONList
endmodule

