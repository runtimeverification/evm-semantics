None of the rules defined here should be sensitive to other parts of the
configuration, they should be standalone.

```k
requires "evm-data.k"
```

Local Execution State
=====================

EVM execution maintains some local state (like a word stack, local memory,
program counter, etc...). We need to specify the syntax of all this local state
for storage.


EVM Programs
------------

```k
module EVM-PROGRAM
    imports EVM-OPCODE


    syntax JSONList ::= List{JSON,","}
    syntax JSON     ::= String
                      | String ":" JSON
                      | "{" JSONList "}"
                      | "[" JSONList "]"


    syntax Int ::= #parseValue ( JSON )    [function]
                 | #parseGasPrice ( JSON ) [function]
                 | #parseGasLimit ( JSON ) [function]

    rule #parseValue( S:String )    => #parseHexWord(S)
    rule #parseGasPrice( S:String ) => #parseHexWord(S)
    rule #parseGasLimit( S:String ) => #parseHexWord(S)

    rule #parseStorage( { .JSONList } )                   => .Map
    rule #parseStorage( { KEY : (VALUE:String) , REST } ) => (#parseHexWord(KEY) |-> #parseHexWord(VALUE)) #parseStorage({ REST })

    syntax Map ::= #parseStorage ( JSON )         [function]

    syntax AcctID ::= #parseID ( JSON ) [function]

    rule #parseID( S:String ) => #parseHexWord(S)
    syntax OpCodes ::= List{OpCode,";"}

    syntax Program ::= OpCodes | Map
                     | #program ( Program ) [function]

    rule #program( OPS:OpCodes ) => #pgmMap(0, OPS)
    rule #program( PGM:Map )     => PGM

    syntax Map ::= #pgmMap( Int , OpCodes ) [function]

    rule #pgmMap(N, .OpCodes)          => .Map
    rule #pgmMap(N, (OP:OpCode ; PGM)) => N |-> OP #pgmMap(N +Int 1, PGM)
endmodule
```

EVM Process
-----------

EVM `Account`s contain the `AcctID` (account identifier), the `Balance` (amount
of ether in the account), the `Storage` (long-term memory of the account), and
the `Program` (code of the account). We use a YAML-like notation to specify
them.

The `WordStack` is the size-limited (to 1024) stack of words that each local
execution of an EVM process has acess to. The local memory is an array of memory
it has local access to (modeled here as a map from addresses to values). EVM
Processes are tuples of their associated `PID`, their `ProgramCounter`, their
`WordStack`, and their `WordMap`.

```k
module EVM-PROCESS-SYNTAX
    imports ID
    imports EVM-PROGRAM

    syntax Storage ::= WordMap | WordList
                     | #storage ( Storage ) [function]

    rule #storage( WM:Map )      => WM
    rule #storage( WS:WordList ) => #asMap(WS)

    syntax AcctID  ::= Word | ".AcctID"
    syntax Account ::= JSON
                     | "account" ":" "-" "id"      ":" AcctID
                                     "-" "balance" ":" Word
                                     "-" "program" ":" Program
                                     "-" "storage" ":" Storage

    syntax Program ::= #dasmEVM ( JSON )               [function]

    rule #dasmEVM(S:String) => #program(#dasmProgram(replaceAll(S, "0x", "")))

    rule #dasmProgram("") => .OpCodes
    rule #dasmProgram(S)  => #dasmOpcode(substrString(S, 0, 2), substrString(S, 2, lengthString(S)))
      requires lengthString(S) >=Int 2

    rule ACCTID : { "balance" : BAL
                  , "code"    : CODE
                  , "nonce"   : NONCE
                  , "storage" : STORAGE
                  }
      => account : - id      : #parseID(ACCTID)
                   - balance : #parseHexWord(BAL)
                   - program : #dasmEVM(CODE)
                   - storage : #parseStorage(STORAGE)
      [structural]

    syntax Transaction ::= JSON
                         | "transaction" ":" "-" "to"       ":" AcctID
                                             "-" "from"     ":" AcctID
                                             "-" "data"     ":" WordList
                                             "-" "value"    ":" Word
                                             "-" "gasPrice" ":" Word
                                             "-" "gasLimit" ":" Word

    rule "transaction" : { "data"      : DATA
                         , "gasLimit"  : LIMIT
                         , "gasPrice"  : PRICE
                         , "nonce"     : NONCE
                         , "secretKey" : SECRETKEY
                         , "to"        : ACCTTO
                         , "value"     : VALUE
                         }
      => transaction : - to       : #parseID(ACCTTO)
                       - from     : .AcctID
                       - data     : #parseData(DATA)
                       - value    : #parseValue(VALUE)
                       - gasPrice : #parseGasPrice(PRICE)
                       - gasLimit : #parseGasLimit(LIMIT)
      [structural]
endmodule
```

EVM Gas Cost
------------

Here we define the gas-cost of each instruction in the instruction set. Many of
the instructions gas cost is fixed and not dependent on any parts of the
configuration; for those that do have some dependence, their associated cost
must be defined after the configuration is defined.

```k
module EVM-GAS
    imports EVM-PROCESS-SYNTAX

    syntax Int ::= "#gas" "(" OpCode ")" [function]

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

We need a way to specify the current world state. It will be a list of accounts,
along with which account to call execution on first:

```k
module EVM-SYNTAX
    imports EVM-GAS

    syntax Accounts ::= ".Accounts"
                      | Account Accounts

    rule .Accounts => . [structural]
    rule ACCT:Account ACCTS:Accounts => ACCT ~> ACCTS [structural]

    syntax Transactions ::= ".Transactions"
                          | Transaction Transactions

    rule .Transactions => . [structural]
    rule TX:Transaction TXS:Transactions => TX ~> TXS [structural]

    syntax EVMSimulation ::= Accounts Transactions

    rule ACCTS:Accounts TXS:Transactions => ACCTS ~> TXS [structural]

    syntax Process ::= "{" AcctID "|" Word "|" Word "|" WordStack "|" WordMap "}"
    syntax CallStack ::= ".CallStack"
                       | Process CallStack
endmodule
```
