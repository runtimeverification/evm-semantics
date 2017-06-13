Ethereum
========

Ethereum is using the EVM to drive updates over the world state.
Actual execution of the EVM is defined in [the EVM file](evm.md).

```k
requires "evm.k"
requires "evm-dasm.k"

module ETHEREUM-SIMULATION
    imports ETHEREUM
    imports EVM-DASM

    configuration initEthereumCell
                  <k> $PGM:EthereumSimulation </k>
```

Ethereum Simulations
====================

An Ethereum simulation is a list of Ethereum commands.
Some Ethereum commands take an Ethereum specification (eg. for an account or transaction).

```k
    syntax EthereumSimulation ::= ".EthereumSimulation"
                                | EthereumCommand EthereumSimulation
 // ----------------------------------------------------------------
    rule .EthereumSimulation => .
    rule ETC:EthereumCommand ETS:EthereumSimulation => ETC ~> ETS

    syntax EthereumCommand ::= EthereumSpecCommand EthereumSpec
                             | EthereumSpecCommand JSON
```

-   `account ...` corresponds to the specification of an account on the network.
-   `transaction ...` corresponds to the specification of a transaction on the network.

TODO: These rules for making sure the account is in normal form won't fire, how can we make them?

```k
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
```

-   `clear` clears all the execution state of the machine back to empty.

```k
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
```

-   `load_` loads an account or transaction into the world state.

```k
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
```

-   `check_` checks if an account/transaction appears in the world-state as stated.

```k
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
           <code>    PGM               </code>
           <storage> STORAGE           </storage>
           <acctMap> "nonce" |-> NONCE </acctMap>
         </account>

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
```

JSON Encoded
------------

Most of the test-set is encoded in JSON.
Here we provide a decoder for that.

TODO: Should JSON enconding stuff be moved to `evm-dasm.md`?

-   `#acctFromJSON` returns our nice representation of EVM programs given the JSON encoding.
-   `#txFromJSON` does the same for transactions.

```k
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
                   - program : #dasmOpCodes(#parseWordStack(CODE))
                   - storage : #parseMap(STORAGE)
```

Here we define `load_` over the various relevant primitives that appear in the EVM tests.

```k
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
```

Here we define `check_` over the "post" part of the EVM test.

```k
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
```

-   `run` runs a given set of Ethereum tests (from the test-set)

```k
    syntax EthereumSpecCommand ::= "run"
 // ------------------------------------
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
    syntax EthereumCommand    ::= "success" | "failure" String
 // ----------------------------------------------------------
    rule <k> JSONINPUT:JSON => run JSONINPUT success .EthereumSimulation </k>
```

-   `#testFromJSON` is used to convert a JSON encoded test to the sequence of EVM drivers it corresponds to.

```k
    syntax KItem ::= #testFromJSON ( JSON ) [function]
 // --------------------------------------------------
    rule #testFromJSON ( TESTID : { "callcreates" : (CCREATES:JSON)     // UNUSED
                                  , "env"         : (ENV:JSON)
                                  , "exec"        : (EXEC:JSON)
                                  , "gas"         : (CURRGAS:String)
                                  , "logs"        : (LOGS:JSON)         // UNUSED
                                  , "out"         : (OUTPUT:String)     // UNUSED
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
                            , "data"     : (DATA:String)
                            , "gas"      : (GAVAIL:String)
                            , "gasPrice" : (GPRICE:String)
                            , "origin"   : (ORIG:String)
                            , "value"    : (VALUE:String)
                            }
            =>
             .
             )
          ...
         </k>
         <id>        _ => #parseHexWord(ACCTTO)                       </id>
         <caller>    _ => #parseHexWord(ACCTFROM)                     </caller>
         <callData>  _ => #parseWordStack(DATA)                       </callData>
         <callValue> _ => #parseHexWord(VALUE)                        </callValue>
         <origin>    _ => #parseHexWord(ORIG)                         </origin>
         <gas>       _ => #parseHexWord(GAVAIL)                       </gas>
         <gasPrice>  _ => #parseHexWord(GPRICE)                       </gasPrice>
         <program>   _ => #asMap(#dasmOpCodes(#parseWordStack(CODE))) </program>
endmodule
```
