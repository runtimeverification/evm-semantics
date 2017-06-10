// Ethereum
// ========

// Ethereum is using the EVM to drive updates over the world state.


requires "evm.k"
requires "evm-dasm.k"

module ETHEREUM
    imports EVM
    imports EVM-DASM

    configuration <ethereum>

                    <k> $PGM:EthereumSimulation </k>

                    initEvmCell

                    <accounts>
                      <account multiplicity="*">
                        <acctID>  .AcctID </acctID>
                        <balance> .Value  </balance>
                        <code>    .Code   </code>
                        <storage> .Map    </storage>
                        <acctMap> .Map    </acctMap>
                      </account>
                    </accounts>

                    <messages>
                      <message multiplicity="*">
                        <msgID>  .MsgID   </msgID>
                        <to>     .AcctID  </to>
                        <from>   .AcctID  </from>
                        <amount> .Value   </amount>
                        <data>   .Map     </data>
                      </message>
                    </messages>

                  </ethereum>

    syntax AcctID ::= Word | ".AcctID"
    syntax Code   ::= Map  | ".Code"
    syntax MsgID  ::= Word | ".MsgID"
    syntax Value  ::= Word | ".Value"

    rule <op> BALANCE ACCT => BAL ~> #push ... </op>
         <account>
           <acctID> ACCT </acctID>
           <balance> BAL </balance>
           ...
         </account>

    rule <op> SLOAD INDEX => VALUE ~> #push ... </op>
         <id> ACCT </id>
         <account>
           <acctID> ACCT </acctID>
           <storage> ... INDEX |-> VALUE ... </storage>
           ...
         </account>

    rule <op> SSTORE INDEX VALUE => . ... </op>
         <id> ACCT </id>
         <account>
           <acctID> ACCT </acctID>
           <storage> STORAGE => STORAGE [ INDEX <- VALUE ] </storage>
           ...
         </account>


// TODO: Calculating gas for `SELFDESTRUCT` needs to take into account the cost of
// creating an account if the recipient address doesn't exist yet. Should it also
// actually create the recipient address if not? Perhaps `#transfer` can take that
// into account automatically for us?


    rule <op> SELFDESTRUCT ACCTTO => . ... </op>
         <id> ACCT </id>
         <selfDestruct> SD </selfDestruct>
         <account>
           <acctID> ACCT </acctID>
           <balance> BALFROM => 0 </balance>
           ...
         </account>
         <account>
           <acctID> ACCTTO </acctID>
           <balance> BALTO => BALTO +Word BALFROM </balance>
           ...
         </account>
      requires ACCT in SD

    rule <op> SELFDESTRUCT ACCTTO => . ... </op>
         <id> ACCT </id>
         <selfDestruct> SD => ACCT : SD               </selfDestruct>
         <refund>       RF => RF +Word Rself-destruct </refund>
         <account>
           <acctID> ACCT </acctID>
           <balance> BALFROM => 0 </balance>
           ...
         </account>
         <account>
           <acctID> ACCTTO </acctID>
           <balance> BALTO => BALTO +Word BALFROM </balance>
           ...
         </account>
      requires notBool (ACCT in SD)


// Ethereum Simulations
// ====================

// An Ethereum simulation is a list of Ethereum commands. Some Ethereum commands
// take an Ethereum specification (eg. for an account or transaction).


    syntax EthereumSimulation ::= ".EthereumSimulation"
                                | EthereumCommand EthereumSimulation
 // ----------------------------------------------------------------
    rule .EthereumSimulation => .
    rule ETC:EthereumCommand ETS:EthereumSimulation => ETC ~> ETS

    syntax EthereumCommand ::= EthereumSpecCommand EthereumSpec
                             | EthereumSpecCommand JSON


// -   `account ...` corresponds to the specification of an account on the network.
// -   `transaction ...` corresponds to the specification of a transaction on
//     the network.

// TODO: These rules for making sure the account is in normal form won't fire, how
// can we make them?


    syntax Storage ::= WordStack | Map
    syntax Program ::= OpCodes   | Map

    syntax EthereumSpec ::= "account" ":" "-" "id"      ":" AcctID
                                          "-" "nonce"   ":" Word
                                          "-" "balance" ":" Word
                                          "-" "program" ":" Program
                                          "-" "storage" ":" Storage
 // ---------------------------------------------------------------
    rule account : - id      : ACCTID
                   - nonce   : NONCE
                   - balance : BAL
                   - program : CODE
                   - storage : (STORAGE:WordStack => #asMap(STORAGE))
    rule account : - id      : ACCTID
                   - nonce   : NONCE
                   - balance : BAL
                   - program : (CODE:OpCodes => #asMap(CODE))
                   - storage : STORAGE

    syntax EthereumSpec ::= "transaction" ":" "-" "id"       ":" MsgID
                                              "-" "to"       ":" AcctID
                                              "-" "from"     ":" AcctID
                                              "-" "value"    ":" Word
                                              "-" "data"     ":" Word
                                              "-" "gasPrice" ":" Word
                                              "-" "gasLimit" ":" Word
 // -----------------------------------------------------------------


// -   `clear` clears all the execution state of the machine back to empty.


    syntax EthereumCommand ::= "clear"
 // ----------------------------------
    rule <k> clear => . ... </k>
         <currOps> COPS      => .Set  </currOps>
         <prevOps> ... (.Set => COPS) </prevOps>

         <op>           _ => .            </op>
         <id>           _ => 0:Word       </id>
         <wordStack>    _ => .WordStack   </wordStack>
         <localMem>     _ => .Map         </localMem>
         <program>      _ => .Map         </program>
         <pc>           _ => 0:Word       </pc>
         <gas>          _ => 0:Word       </gas>
         <caller>       _ => 0:Word       </caller>
         <callStack>    _ => .CallStack   </callStack>
         <selfDestruct> _ => .WordStack   </selfDestruct>
         <log>          _ => .SubstateLog </log>
         <refund>       _ => 0:Word       </refund>
         <gasPrice>     _ => 0:Word       </gasPrice>
         <gasLimit>     _ => 0:Word       </gasLimit>
         <coinbase>     _ => 0:Word       </coinbase>
         <timestamp>    _ => 0:Word       </timestamp>
         <number>       _ => 0:Word       </number>
         <difficulty>   _ => 0:Word       </difficulty>
         <origin>       _ => 0:Word       </origin>
         <callValue>    _ => 0:Word       </callValue>
         <accounts>     _ => .Bag         </accounts>
         <messages>     _ => .Bag         </messages>


// -   `load_` loads an account or transaction into the world state.


    syntax EthereumSpecCommand ::= "load"
 // -------------------------------------
    rule <k> ( load account : - id      : ACCTID
                              - nonce   : NONCE
                              - balance : BAL
                              - program : (PGM:Map)
                              - storage : (STORAGE:Map)
            => .
             )
             ...
         </k>
         <accounts>
            ( .Bag
           => <account>
                <acctID>  ACCTID            </acctID>
                <balance> BAL               </balance>
                <code>    PGM               </code>
                <storage> STORAGE           </storage>
                <acctMap> "nonce" |-> NONCE </acctMap>
              </account>
            )
            ...
         </accounts>
      requires word2Bool(BAL >=Word 0)

    rule <k> ( load transaction : - id       : TXID
                                  - to       : ACCTTO
                                  - from     : ACCTFROM
                                  - value    : VALUE
                                  - data     : DATA
                                  - gasPrice : GPRICE
                                  - gasLimit : GLIMIT
            => .
             )
             ...
         </k>
         <messages>
            ( .Bag
           => <message>
                <msgID>  TXID     </msgID>
                <to>     ACCTTO   </to>
                <from>   ACCTFROM </from>
                <amount> VALUE    </amount>
                <data>   "data"     |-> DATA
                         "gasPrice" |-> GPRICE
                         "gasLimit" |-> GLIMIT
                </data>
              </message>
            )
            ...
         </messages>
      requires word2Bool(VALUE >=Word 0)

    rule <k> ( load "gas" : CURRGAS => . ) ... </k>
         <gas> _ => #parseHexWord(CURRGAS) </gas>


// -   `check_` checks if an account/transaction appears in the world-state
//     as stated.


    syntax EthereumSpecCommand ::= "check"
 // --------------------------------------
    rule <k> ( check account : - id      : ACCT
                               - nonce   : NONCE
                               - balance : BAL
                               - program : (PGM:Map)
                               - storage : (STORAGE:Map)
            =>
             .
             )
             ...
         </k>
         <account>
           <acctID>  ACCT              </acctID>
           <balance> BAL               </balance>
           <code>    CODE              </code>
           <storage> ACCTSTORAGE       </storage>
           <acctMap> "nonce" |-> NONCE </acctMap>
         </account>
      requires PGM ==K CODE andBool STORAGE ==K ACCTSTORAGE

    rule <k> ( check ( transaction : - id       : TXID
                                     - to       : ACCTTO
                                     - from     : ACCTFROM
                                     - value    : VALUE
                                     - data     : DATA
                                     - gasPrice : GPRICE
                                     - gasLimit : GLIMIT
                     )
            =>
             .
             )
             ...
         </k>
         <message>
           <msgID>  TXID     </msgID>
           <to>     ACCTTO   </to>
           <from>   ACCTFROM </from>
           <amount> VALUE    </amount>
           <data>   "data"     |-> DATA
                    "gasPrice" |-> GPRICE
                    "gasLimit" |-> GLIMIT
           </data>
         </message>


// JSON Encoded
// ------------

// Most of the test-set is encoded in JSON. Here we provide a decoder for that.

// TODO: Should JSON enconding stuff be moved to `evm-dasm.md`? TODO: Parsing the
// storage needs to actually happen (not calling `#parseWordStack`).

// -   `#acctFromJSON` returns our nice representation of EVM programs given the
//     JSON encoding.
// -   `#txFromJSON` does the same for transactions.


    syntax EthereumSpec ::= #acctFromJSON ( JSON ) [function]
 // ---------------------------------------------------------
    rule #acctFromJSON ( ACCTID : { "balance" : (BAL:String)
                                  , "code"    : (CODE:String)
                                  , "nonce"   : (NONCE:String)
                                  , "storage" : (STORAGE:JSON)
                                  }
                       )
      => account : - id      : #parseHexWord(ACCTID)
                   - nonce   : #parseHexWord(NONCE)
                   - balance : #parseHexWord(BAL)
                   - program : #asMap(#dasmOpCodes(#parseWordStack(CODE)))
                   - storage : #asMap(#parseMap(STORAGE))


// Here we define `load_` over the various relevant primitives that appear in the
// EVM tests.


    rule <k> ( load ( "env" : { "currentCoinbase"   : (CB:String)
                              , "currentDifficulty" : (DIFF:String)
                              , "currentGasLimit"   : (GLIMIT:String)
                              , "currentNumber"     : (NUM:String)
                              , "currentTimestamp"  : (TS:String)
                              }
                    )
            =>
             .
             )
             ...
         </k>
         <gasLimit>   _ => #parseHexWord(GLIMIT) </gasLimit>
         <coinbase>   _ => #parseHexWord(CB)     </coinbase>
         <timestamp>  _ => #parseHexWord(TS)     </timestamp>
         <number>     _ => #parseHexWord(NUM)    </number>
         <difficulty> _ => #parseHexWord(DIFF)   </difficulty>

    rule <k> ( load "pre" : { .JSONList } => . ) ... </k>
    rule <k> ( load "pre" : { ACCTID : ACCT
                            , ACCTS
                            }
             )
            =>
             ( load #acctFromJSON( ACCTID : ACCT )
            ~> load "pre" : { ACCTS }
             )
             ...
         </k>


// Here we define `check_` over the "post" part of the EVM test.


    rule <k> ( check "post" : { .JSONList } ~> failure TESTID => . ) ... </k>
    rule <k> ( check "post" : { ACCTID : ACCT
                              , ACCTS
                              }
             )
            =>
             ( check #acctFromJSON( ACCTID : ACCT )
            ~> check "post" : { ACCTS }
             )
             ...
         </k>


// -   `run` runs a given set of Ethereum tests (from the test-set)


    syntax EthereumSpecCommand ::= "run" | "failure" String
 // -------------------------------------------------------
    rule <k> run { .JSONList } => . ... </k>
    rule <k> ( run { TESTID : (TEST:JSON)
                   , TESTS
                   }
            => #testFromJSON( TESTID : TEST )
            ~> failure TESTID
            ~> clear
            ~> run { TESTS }
             )
             ...
         </k>

    syntax EthereumSimulation ::= JSON
 // ----------------------------------
    rule <k> JSONINPUT:JSON => run JSONINPUT .EthereumSimulation </k>


// -   `#testFromJSON` is used to convert a JSON encoded test to the sequence of
//     EVM drivers it corresponds to.


    syntax KItem ::= #testFromJSON ( JSON ) [function]
 // --------------------------------------------------
    rule #testFromJSON ( TESTID : { "callcreates" : (CCREATES:JSON)     // unused
                                  , "env"         : (ENV:JSON)
                                  , "exec"        : (EXEC:JSON)
                                  , "gas"         : (CURRGAS:String)
                                  , "logs"        : (LOGS:JSON)         // unused
                                  , "out"         : (OUTPUT:String)     // unused
                                  , "post"        : (POST:JSON)
                                  , "pre"         : (PRE:JSON)
                                  }
                       )
      =>  ( load  "env"  : ENV
         ~> load  "pre"  : PRE
         ~> load  "gas"  : CURRGAS
         ~> run   "exec" : EXEC
         ~> check "post" : POST
          )

    rule <k> ( run "exec" : { "address"  : (ACCTTO:String)
                          , "caller"   : (ACCTFROM:String)
                          , "code"     : (CODE:String)
                          , "data"     : (DATA:String)                  // unused
                          , "gas"      : (GAVAIL:String)
                          , "gasPrice" : (GPRICE:String)
                          , "origin"   : (ORIG:String)
                          , "value"    : (VAL:String)                   // unused
                          }
            =>
             .
             )
          ...
         </k>
         <id>       _ => #parseHexWord(ACCTTO)                       </id>
         <caller>   _ => #parseHexWord(ACCTFROM)                     </caller>
         <origin>   _ => #parseHexWord(ORIG)                         </origin>
         <gas>      _ => #parseHexWord(GAVAIL)                       </gas>
         <gasPrice> _ => #parseHexWord(GPRICE)                       </gasPrice>
         <program>  _ => #asMap(#dasmOpCodes(#parseWordStack(CODE))) </program>
endmodule

