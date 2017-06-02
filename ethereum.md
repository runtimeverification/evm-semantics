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
    imports ETHEREUM-SIMULATION

    configuration <ethereum>
                    <k> $PGM:EthereumSimulation </k>
                    initEvmCell
                    initWorldStateCell
                  </ethereum>

    syntax AcctID ::= Word
    syntax Code   ::= Map
    syntax MsgID  ::= Word

    syntax InternalOp ::= "#pushResponse"
 // -------------------------------------
    rule <op> #pushResponse => RESPONSE ~> #push ... </op>
         <control> #response RESPONSE => . </control>

    rule <op> SLOAD INDEX => #pushResponse ... </op>
         <id> ACCT </id>
         <control> . => #getAccountStorage ACCT INDEX </control>

    rule <op> SSTORE INDEX VALUE => . ... </op>
         <id> ACCT </id>
         <control> . => #setAccountStorage ACCT INDEX VALUE </control>
```

Ethereum Simulations
====================

An Ethereum simulation is a list of Ethereum commands.

```k
    syntax EthereumSimulation ::= ".EthereumSimulation"
                                | EthereumCommand EthereumSimulation
 // ----------------------------------------------------------------
    rule .EthereumSimulation => .
    rule ETC:EthereumCommand ETS:EthereumSimulation => ETC ~> ETS
```

-   `load_` is used to load an account or transaction into the world state.

```k
    syntax EthereumCommand ::= "load" Account | "load" Transaction
 // --------------------------------------------------------------

    syntax Account ::= "account" ":" "-" "id"      ":" AcctID
                                     "-" "nonce"   ":" Word
                                     "-" "balance" ":" Word
                                     "-" "program" ":" OpCodes
                                     "-" "storage" ":" WordStack
 // ------------------------------------------------------------
    rule <k> ( load ( account : - id      : ACCTID
                                - nonce   : NONCE
                                - balance : BALANCE
                                - code    : CODE
                                - storage : STORAGE
                    )
            =>
             .
             )
             ...
          </k>
          <control> . => #addAccount ACCTID BALANCE #asMap(CODE) #asMap(STORAGE) ("nonce" |-> NONCE) </control>

    syntax Transaction ::= "transaction" ":" "-" "msgid"    ":" MsgID
                                             "-" "to"       ":" AcctID
                                             "-" "from"     ":" AcctID
                                             "-" "value"    ":" Word
                                             "-" "data"     ":" Word
                                             "-" "gasPrice" ":" Word
                                             "-" "gasLimit" ":" Word
 // ----------------------------------------------------------------
    rule <k> ( load ( transaction : - msgid    : MSGID
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
         <control> . => #addMessage MSGID ACCTTO ACCTFROM VALUE ("data" |-> DATA "gasPrice" |-> GPRICE "gasLimit" |-> GLIMIT) </control>
```

-   `check-account_` is used to check if an account appears in the world-state with the given information.

```k
    syntax EthereumCommand ::= "check-account" Account
 // --------------------------------------------------
    rule <k> ( check-account ( account : - id      : ACCT
                                         - nonce   : NONCE
                                         - balance : BALANCE
                                         - program : PROGRAM
                                         - storage : STORAGE
                             )
            => .
             )
             ...
         </k>
         <account>
           <acctID>  ACCT              </acctID>
           <balance> BALANCE           </balance>
           <code>    CODE              </code>
           <storage> ACCTSTORAGE       </storage>
           <acctMap> "nonce" |-> NONCE </acctMap>
         </account>
      requires #asMap(PROGRAM) ==K CODE andBool #asMap(STORAGE) ==K ACCTSTORAGE#asMap(PROGRAM) ==K CODE andBool #asMap(STORAGE) ==K ACCTSTORAGE
endmodule
```

Here is the data of a transaction on the network. It has fields for who it's
directed toward, the data, the value transfered, and the gas-price/gas-limit.
Similarly, a conversion from the JSON format to the pretty K format is provided.

```
    rule <control> ACCTID : { "balance" : (BAL:String)
                            , "code"    : (CODE:String)
                            , "nonce"   : (NONCE:String)
                            , "storage" : STORAGE
                            }
                => account : - id      : #parseHexWord(ACCTID)
                             - nonce   : #parseHexWord(NONCE)
                             - balance : #parseHexWord(BAL)
                             - program : #dasmOpCodes(#parseWordStack(CODE))
                             - storage : #parseWordStack(STORAGE)
                ...
         </control>

    syntax Transaction ::= JSON
                         | "transaction" ":" "-" "to"       ":" AcctID
                                             "-" "from"     ":" AcctID
                                             "-" "data"     ":" WordStack
                                             "-" "value"    ":" Word
                                             "-" "gasPrice" ":" Word
                                             "-" "gasLimit" ":" Word
                         | "transaction" ":" "-" "to"       ":" AcctID
                                             "-" "from"     ":" AcctID
                                             "-" "init"     ":" WordStack
                                             "-" "value"    ":" Word
                                             "-" "gasPrice" ":" Word
                                             "-" "gasLimit" ":" Word
 // ----------------------------------------------------------------
    rule <control> "transaction" : { "data"      : (DATA:String)
                                   , "gasLimit"  : (LIMIT:String)
                                   , "gasPrice"  : (PRICE:String)
                                   , "nonce"     : (NONCE:String)
                                   , "secretKey" : (SECRETKEY:String)
                                   , "to"        : (ACCTTO:String)
                                   , "value"     : (VALUE:String)
                                   }
                => transaction : - to       : #parseHexWord(ACCTTO)
                                 - from     : .AcctID
                                 - data     : #parseWordStack(DATA)
                                 - value    : #parseHexWord(VALUE)
                                 - gasPrice : #parseHexWord(PRICE)
                                 - gasLimit : #parseHexWord(LIMIT)
                ...
         </control>
```
