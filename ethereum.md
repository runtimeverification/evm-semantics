Ethereum
========

Ethereum is using the EVM to drive updates over the world state.

```k
requires "evm.k"
requires "evm-dasm.k"
requires "world-state.k"

module ETHEREUM
    imports EVM
    imports WORLD-STATE
    imports EVM-DASM

    configuration <ethereum>
                    <k> $PGM:EthereumSimulation </k>
                    initEvmCell
                    initWorldStateCell
                  </ethereum>

    syntax AcctID ::= Word
    syntax Code   ::= Map
    syntax MsgID  ::= Word
    syntax Value  ::= Word

    syntax InternalOp ::= "#pushResponse"
 // -------------------------------------
    rule <op> #pushResponse => RESPONSE ~> #push ... </op>
         <control> #response RESPONSE => .Control </control>

    rule <op> BALANCE ACCT => BAL ~> #push ... </op>
         <account>
           <acctID> ACCT </acctID>
           <balance> BAL </balance>
           ...
         </account>

    rule <op> SLOAD INDEX => #pushResponse ... </op>
         <id> ACCT </id>
         <control> .Control => #getAccountStorage ACCT INDEX </control>

    rule <op> SSTORE INDEX VALUE => . ... </op>
         <id> ACCT </id>
         <control> .Control => #setAccountStorage ACCT INDEX VALUE </control>
```

TODO: Calculating gas for `SELFDESTRUCT` needs to take into account the cost of creating an account if the recipient address doesn't exist yet. Should it also actually create the recipient address if not? Perhaps `#transfer` can take that into account automatically for us?

```k
    rule <op> SELFDESTRUCT ACCTTO => . ... </op>
         <id> ACCT </id>
         <selfDestruct> SD </selfDestruct>
         <control> .Control => #transfer ACCT ACCTTO ALL </control>
      requires ACCT in SD

    rule <op> SELFDESTRUCT ACCTTO => . ... </op>
         <id> ACCT </id>
         <selfDestruct> SD => ACCT : SD               </selfDestruct>
         <refund>       RF => RF +Word Rself-destruct </refund>
         <control> .Control => #transfer ACCT ACCTTO ALL </control>
      requires notBool (ACCT in SD)
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

TODO: I don't like how we have to accept both `WordStack` and `Map` in the pretty format, but some tests don't have values for intermediate places in the memory.

```k
    syntax Storage ::= WordStack | Map
    syntax Program ::= OpCodes   | Map

    syntax EthereumSpec ::= "account" ":" "-" "id"      ":" AcctID
                                          "-" "nonce"   ":" Word
                                          "-" "balance" ":" Word
                                          "-" "program" ":" Program
                                          "-" "storage" ":" Storage [function]
 // --------------------------------------------------------------------------
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

-   `clear` clears both the transactions and accounts from the world state.

```k
    syntax EthereumCommand ::= "clear"
 // ----------------------------------
    rule <k> clear => . ... </k>
         <accounts> _ => .Bag </accounts>
         <messages> _ => .Bag </messages>
```

-   `load_` loads an account or transaction into the world state.

```k
    syntax EthereumSpecCommand ::= "load"
 // -------------------------------------
    rule <k> ( load ( account : - id      : (ACCTID:Word)
                                - nonce   : (NONCE:Word)
                                - balance : (BAL:Word)
                                - program : (PGM:Map)
                                - storage : (STORAGE:Map)
                    )
            =>
             .
             )
             ...
         </k>
         <control> .Control => #addAccount ACCTID BAL PGM STORAGE ("nonce" |-> NONCE) </control>

    rule <k> ( load ( transaction : - id       : TXID
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
         <control> .Control => #addMessage TXID ACCTTO ACCTFROM VALUE ("data" |-> DATA "gasPrice" |-> GPRICE "gasLimit" |-> GLIMIT) </control>

    rule <k> ( load "gas" : CURRGAS => . ) ... </k>
         <gas> _ => #parseHexWord(CURRGAS) </gas>
```

-   `check_` checks if an account/transaction appears in the world-state as stated.

```k
    syntax EthereumSpecCommand ::= "check"
 // --------------------------------------
    rule <k> ( check ( account : - id      : ACCT
                                 - nonce   : NONCE
                                 - balance : BAL
                                 - program : (PGM:Map)
                                 - storage : (STORAGE:Map)
                     )
            => .
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
      requires #asMap(PGM) ==K CODE andBool STORAGE ==K ACCTSTORAGE

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

Most of the test-set is encoded in JSON. Here we provide a decoder for that.

TODO: Should JSON enconding stuff be moved to `evm-dasm.md`?
TODO: Parsing the storage needs to actually happen (not calling `#parseWordStack`).

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
                   - program : #asMap(#dasmOpCodes(#parseWordStack(CODE)))
                   - storage : #asMap(#parseMap(STORAGE))
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
    rule <k> ( check "post" : { .JSONList } => . ) ... </k>
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
            ~> run { TESTS }
             )
             ...
         </k>
```

-   `#testFromJSON` is used to convert a JSON encoded test to the sequence of EVM drivers it corresponds to.

```k
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

    rule <k> run "exec" : { "address"  : (ACCTTO:String)
                          , "caller"   : (ACCTFROM:String)
                          , "code"     : (CODE:String)
                          , "data"     : (DATA:String)                  // unused
                          , "gas"      : (GAVAIL:String)
                          , "gasPrice" : (GPRICE:String)
                          , "origin"   : (ORIG:String)
                          , "value"    : (VAL:String)                   // unused
                          }
          => .
          ...
         </k>
         <id>       _ => #parseHexWord(ACCTTO)                       </id>
         <caller>   _ => #parseHexWord(ACCTFROM)                     </caller>
         <origin>   _ => #parseHexWord(ORIG)                         </origin>
         <gas>      _ => #parseHexWord(GAVAIL)                       </gas>
         <gasPrice> _ => #parseHexWord(GPRICE)                       </gasPrice>
         <program>  _ => #asMap(#dasmOpCodes(#parseWordStack(CODE))) </program>
endmodule
```
