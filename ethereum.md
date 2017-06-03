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

-   Sort `Account` corresponds to the specification of an account on the network.
-   Sort `Transaction` corresponds to the specification of a transaction on the network.

```k
    syntax Account ::= "account" ":" "-" "id"      ":" AcctID
                                     "-" "nonce"   ":" Word
                                     "-" "balance" ":" Word
                                     "-" "program" ":" OpCodes
                                     "-" "storage" ":" WordStack
 // ------------------------------------------------------------

    syntax Transaction ::= "transaction" ":" "-" "id"       ":" MsgID
                                             "-" "to"       ":" AcctID
                                             "-" "from"     ":" AcctID
                                             "-" "value"    ":" Word
                                             "-" "data"     ":" Word
                                             "-" "gasPrice" ":" Word
                                             "-" "gasLimit" ":" Word
 // ----------------------------------------------------------------
```

-   `load_` is used to load an account or transaction into the world state.

```k
    syntax EthereumCommand ::= "load" Account | "load" Transaction
 // --------------------------------------------------------------
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
```

-   `check_` is used to check if an account/transaction appears in the world-state as stated.

```k
    syntax EthereumCommand ::= "check" Account | "check" Transaction
 // ----------------------------------------------------------------
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
endmodule
```

UNUSED
======

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
