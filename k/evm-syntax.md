Local Execution State
=====================

EVM execution maintains some local state (like a word stack, local memory,
program counter, etc...). We need to specify the syntax of all this local state
for storage.

```k
requires "evm-data.k"
```

EVM Gas Cost
------------

Here we define the gas-cost of each instruction in the instruction set. Many of
the instructions gas cost is fixed and not dependent on any parts of the
configuration; for those that do have some dependence, their associated cost
must be defined after the configuration is defined.

```k
module EVM-GAS
    imports EVM-OPCODE

    syntax Word ::= "#gas" "(" OpCode ")" [function]

    // W_{zero}
    rule #gas( STOP   ) => 0
    rule #gas( RETURN ) => 0

    // W_{base}
    rule #gas( ADDRESS      ) => 2
    rule #gas( ORIGIN       ) => 2
    rule #gas( CALLER       ) => 2
    rule #gas( CALLVALUE    ) => 2
    rule #gas( CALLDATASIZE ) => 2
    rule #gas( CODESIZE     ) => 2
    rule #gas( GASPRICE     ) => 2
    rule #gas( COINBASE     ) => 2
    rule #gas( TIMESTAMP    ) => 2
    rule #gas( NUMBER       ) => 2
    rule #gas( DIFFICULTY   ) => 2
    rule #gas( GASLIMIT     ) => 2
    rule #gas( POP          ) => 2
    rule #gas( PC           ) => 2
    rule #gas( MSIZE        ) => 2
    rule #gas( GAS          ) => 2

    // W_{verylow}
    rule #gas( ADD           ) => 3
    rule #gas( SUB           ) => 3
    rule #gas( NOT           ) => 3
    rule #gas( LT            ) => 3
    rule #gas( GT            ) => 3
    rule #gas( SLT           ) => 3
    rule #gas( SGT           ) => 3
    rule #gas( EQ            ) => 3
    rule #gas( ISZERO        ) => 3
    rule #gas( AND           ) => 3
    rule #gas( EVMOR         ) => 3
    rule #gas( XOR           ) => 3
    rule #gas( BYTE          ) => 3
    rule #gas( CALLDATALOAD  ) => 3
    rule #gas( MLOAD         ) => 3
    rule #gas( MSTORE        ) => 3
    rule #gas( MSTORE8       ) => 3
    rule #gas( PUSH [ W ] W' ) => 3
    rule #gas( DUP  [ W ]    ) => 3
    rule #gas( SWAP [ W ]    ) => 3

    // W_{low}
    rule #gas( MUL        ) => 5
    rule #gas( DIV        ) => 5
    rule #gas( SDIV       ) => 5
    rule #gas( MOD        ) => 5
    rule #gas( SMOD       ) => 5
    rule #gas( SIGNEXTEND ) => 5

    // W_{mid}
    rule #gas( ADDMOD ) => 8
    rule #gas( MULMOD ) => 8
    rule #gas( JUMP   ) => 8

    // W_{high}
    rule #gas( JUMP1 ) => 10

    // W_{extcode}
    rule #gas( EXTCODESIZE ) => 700

    // CALL
    // TODO: This is not correct!!!
    rule #gas( CALL ) => 700
endmodule
```

EVM Simulation
--------------

We need a way to specify the current world state. It will be a list of accounts
and a list of pending transactions. This can come in either the pretty K format,
or in the default EVM test-set format.

First, we build a JSON parser, then we provide some standard "parsers" which
will be used to convert the JSON formatted input into the prettier K format.

```k
module EVM-SYNTAX
    imports EVM-OPCODE

    syntax JSONList ::= List{JSON,","}
    syntax JSON     ::= String
                      | String ":" JSON
                      | "{" JSONList "}"
                      | "[" JSONList "]"
 // ------------------------------------

    syntax Program ::= OpCodes | OpCodeMap
                     | #program ( Program ) [function]
                     | #dasmEVM ( JSON )    [function]
 // --------------------------------------------------
    rule #program( OCM:Map )     => OCM
    rule #program( OCS:OpCodes ) => #asMap(OCS)
    rule #dasmEVM( S:String ) => #program(#dasmOpCodes(replaceAll(S, "0x", "")))

    syntax Storage ::= WordMap | WordStack
                     | #storage ( Storage ) [function]
 // --------------------------------------------------
    rule #storage( WM:Map )       => WM
    rule #storage( WS:WordStack ) => #asMap(WS)

    syntax Map ::= #parseStorage ( JSON ) [function]
 // ------------------------------------------------
    rule #parseStorage( { .JSONList } )                   => .Map
    rule #parseStorage( { KEY : (VALUE:String) , REST } ) => (#parseHexWord(KEY) |-> #parseHexWord(VALUE)) #parseStorage({ REST })
```

Here is the data of an account on the network. It has an id, a balance, a
program, and storage. Additionally, the translation from the JSON account format
to the K format is provided.

```k
    syntax AcctID  ::= Word | ".AcctID"
    syntax Account ::= JSON
                     | "account" ":" "-" "id"      ":" AcctID
                                     "-" "balance" ":" Word
                                     "-" "program" ":" Program
                                     "-" "storage" ":" Storage
 // ----------------------------------------------------------
    rule ACCTID : { "balance" : (BAL:String)
                  , "code"    : (CODE:String)
                  , "nonce"   : (NONCE:String)
                  , "storage" : STORAGE
                  }
      => account : - id      : #parseHexWord(ACCTID)
                   - balance : #parseHexWord(BAL)
                   - program : #dasmEVM(CODE)
                   - storage : #parseStorage(STORAGE)
      [structural]
```

Here is the data of a transaction on the network. It has fields for who it's
directed toward, the data, the value transfered, and the gas-price/gas-limit.
Similarly, a conversion from the JSON format to the pretty K format is provided.

```k
    syntax Transaction ::= JSON
                         | "transaction" ":" "-" "to"       ":" AcctID
                                             "-" "from"     ":" AcctID
                                             "-" "data"     ":" WordStack
                                             "-" "value"    ":" Word
                                             "-" "gasPrice" ":" Word
                                             "-" "gasLimit" ":" Word
 // ----------------------------------------------------------------
    rule "transaction" : { "data"      : (DATA:String)
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
      [structural]
```

Finally, we have the syntax of an `EVMSimulation`, which consists of a list of
accounts followed by a list of transactions.

```k
    syntax Accounts ::= ".Accounts"
                      | Account Accounts
 // ------------------------------------
    rule .Accounts => . [structural]
    rule ACCT:Account ACCTS:Accounts => ACCT ~> ACCTS [structural]

    syntax Transactions ::= ".Transactions"
                          | Transaction Transactions
 // ------------------------------------------------
    rule .Transactions => . [structural]
    rule TX:Transaction TXS:Transactions => TX ~> TXS [structural]

    syntax EVMSimulation ::= Accounts Transactions
 // ----------------------------------------------
    rule ACCTS:Accounts TXS:Transactions => ACCTS ~> TXS [structural]

    syntax Process ::= "{" AcctID "|" Word "|" Word "|" WordStack "|" WordMap "}"
    syntax CallStack ::= ".CallStack"
                       | Process CallStack
endmodule
```
