// Ethereum
// ========

// Ethereum is using the EVM to drive updates over the world state.


requires "evm.k"
requires "evm-dasm.k"
requires "world-state.k"

module ETHEREUM
    imports EVM
    imports WORLD-STATE

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

    rule <op> COINBASE   => #pushResponse ... </op> <control> .Control => #getGlobal "coinbase"   </control>
    rule <op> TIMESTAMP  => #pushResponse ... </op> <control> .Control => #getGlobal "timestamp"  </control>
    rule <op> NUMBER     => #pushResponse ... </op> <control> .Control => #getGlobal "number"     </control>
    rule <op> DIFFICULTY => #pushResponse ... </op> <control> .Control => #getGlobal "difficulty" </control>
    rule <op> GASLIMIT   => #pushResponse ... </op> <control> .Control => #getGlobal "gasLimit"   </control>

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


// TODO: Calculating gas for `SELFDESTRUCT` needs to take into account the cost of
// creating an account if the recipient address doesn't exist yet. Should it also
// actually create the recipient address if not? Perhaps `#transfer` can take that
// into account automatically for us?


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


// -   `account ...` corresponds to the specification of an account on the network.
// -   `transaction ...` corresponds to the specification of a transaction on
//     the network.


    syntax EthereumSpec ::= "account" ":" "-" "id"      ":" AcctID
                                          "-" "nonce"   ":" Word
                                          "-" "balance" ":" Word
                                          "-" "program" ":" OpCodes
                                          "-" "storage" ":" WordStack

    syntax EthereumSpec ::= "transaction" ":" "-" "id"       ":" MsgID
                                              "-" "to"       ":" AcctID
                                              "-" "from"     ":" AcctID
                                              "-" "value"    ":" Word
                                              "-" "data"     ":" Word
                                              "-" "gasPrice" ":" Word
                                              "-" "gasLimit" ":" Word
 // -----------------------------------------------------------------


// -   `clear` clears both the transactions and accounts from the world state.


    syntax EthereumCommand ::= "clear"
 // ----------------------------------
    rule <k> clear => . ... </k>
         <accounts> _ => .Bag </accounts>
         <messages> _ => .Bag </messages>


// -   `load_` loads an account or transaction into the world state.


    syntax EthereumSpecCommand ::= "load"
 // -------------------------------------
    rule <k> ( load ( account : - id      : ACCTID
                                - nonce   : NONCE
                                - balance : BAL
                                - program : PGM
                                - storage : STORAGE
                    )
            =>
             .
             )
             ...
         </k>
         <control> .Control => #addAccount ACCTID BAL #asMap(PGM) #asMap(STORAGE) ("nonce" |-> NONCE) </control>

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


// -   `check_` checks if an account/transaction appears in the world-state
//     as stated.


    syntax EthereumSpecCommand ::= "check"
 // --------------------------------------
    rule <k> ( check ( account : - id      : ACCT
                                 - nonce   : NONCE
                                 - balance : BAL
                                 - program : PGM
                                 - storage : STORAGE
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
      requires #asMap(PGM) ==K CODE andBool #asMap(STORAGE) ==K ACCTSTORAGE

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


    syntax JSONList ::= List{JSON,","}
    syntax JSON     ::= String
                      | String ":" JSON
                      | "{" JSONList "}"
                      | "[" JSONList "]"
 // ------------------------------------

    syntax EthereumSpec ::= JSON
 // ----------------------------


// -   `#acctFromJSON` returns our nice representation of EVM programs given the
//     JSON encoding.
// -   `#txFromJSON` does the same for transactions.


    syntax EthereumSpec ::= #acctFromJSON ( JSON ) [function]
                          | #txFromJSON   ( JSON ) [function]
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
                   - storage : #parseWordStack(STORAGE)


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
         <global> GM => GM [ "coinbase"   <- #parseHexWord(CB)     ]
                           [ "difficulty" <- #parseHexWord(DIFF)   ]
                           [ "gasLimit"   <- #parseHexWord(GLIMIT) ]
                           [ "number"     <- #parseHexWord(NUM)    ]
                           [ "timestamp"  <- #parseHexWord(TS)     ]
         </global>

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


// -   `run` runs a given set of Ethereum tests (from the test-set)


    syntax EthereumSpecCommand ::= "run"
 // ------------------------------------
    rule <k> run { .JSONList } => . ... </k>
    rule <k> ( run { TESTID : (TEST:JSON)
                   , TESTS
                   }
            => #testFromJSON( TESTID : TEST )
            ~> run { TESTS }
             )
         </k>


// -   `#testFromJSON` is used to convert a JSON encoded test to the sequence of
//     EVM drivers it corresponds to.


    syntax KItem ::= #testFromJSON ( JSON ) [function]
 // --------------------------------------------------
    rule #testFromJSON ( TESTID : { "callcreates" : (CCREATES:JSON)
                                  , "env"         : (ENV:JSON)
                                  , "exec"        : (EXEC:JSON)
                                  , "gas"         : (CURRGAS:String)
                                  , "logs"        : (LOGS:JSON)
                                  , "out"         : (OUTPUT:String)
                                  , "post"        : (POST:JSON)
                                  , "pre"         : (PRE:JSON)
                                  }
                       )
      =>  ( load  "env"  : ENV
         ~> load  "gas"  : CURRGAS
         ~> run   "exec" : EXEC
         ~> check "post" : POST
          )
endmodule

