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

Stack Operations
----------------

We break up stack operations into groups by their arity so that we can pull out
the correct number of arguments for each operation.

NOTE: We have to call the opcode `OR` by `EVMOR` instead, because otherwise K
has trouble parsing it/compiling the definition.

The `Null`, `Un`, `Bin`, `Tern`, and `Quad`, refer to the number of elements that each
operation takes off the stack. These are binned in this way so that we can have
simpler rules (in the semantics) for pulling items off the stacks.

```k
module EVM-OPCODE
    imports EVM-WORD

    syntax NullStackOp ::= "#push"
                         | "PUSH" Word
                         | "#checkStackSize"
                         | "STACK_OVERFLOW"
                         | "DUP" Int
                         | "SWAP" Int
                         | "PC" | "MSIZE" | "GAS"
                         | "STOP" | "ADDRESS" | "ORIGIN" | "CALLER"
                         | "CALLVALUE" | "CALLDATASIZE" | "GASPRICE" | "CODESIZE"
                         | "COINBASE" | "TIMESTAMP" | "NUMBER" | "DIFFICULTY" | "GASLIMIT"
    syntax KItem ::= NullStackOp

    rule PUSH N => N ~> #push ~> #checkStackSize [structural]
    rule (I:Int ~> #checkStackSize) => .              requires I <Int  1024
    rule (I:Int ~> #checkStackSize) => STACK_OVERFLOW requires I >=Int 1024

    syntax UnStackOp ::= "ISZERO" | "NOT" | "POP"
                       | "JUMP" | "MLOAD"
                       | "CALLDATALOAD" | "EXTCODESIZE"
    syntax KItem ::= UnStackOp Word

    rule ISZERO 0 => bool2Word(true)  ~> #push                   [structural]
    rule ISZERO N => bool2Word(false) ~> #push requires N =/=K 0 [structural]
    rule NOT    N => bitwisenot(N)    ~> #push                   [structural]
    rule POP    N => .                                           [structural]

    syntax BinStackOp ::= "ADD" | "MUL" | "SUB" | "DIV" | "EXP"
                        | "MOD" | "SIGNEXTEND" | "SDIV" | "SMOD"
                        | "LT" | "GT" | "SLT" | "SGT" | "EQ"
                        | "AND" | "EVMOR" | "XOR"
                        | "BYTE" | "SHA3"
                        | "JUMP1" | "RETURN" | "MSTORE" | "MSTORE8"
    syntax KItem ::= BinStackOp Word Word

    rule ADD        W0 W1 => W0 +Word W1       ~> #push [structural]
    rule MUL        W0 W1 => W0 *Word W1       ~> #push [structural]
    rule SUB        W0 W1 => W0 -Word W1       ~> #push [structural]
    rule DIV        W0 W1 => W0 /Word W1       ~> #push [structural]
    rule EXP        W0 W1 => W0 ^Word W1       ~> #push [structural]
    rule MOD        W0 W1 => W0 %Word W1       ~> #push [structural]
    rule SIGNEXTEND W0 W1 => signextend(W0,W1) ~> #push [structural]
    rule SDIV       W0 W1 => sdiv(W0,W1)       ~> #push [structural]
    rule SMOD       W0 W1 => smod(W0,W1)       ~> #push [structural]
    rule LT         W0 W1 => W0 <Word W1       ~> #push [structural]
    rule GT         W0 W1 => W0 >Word W1       ~> #push [structural]
    rule SLT        W0 W1 => slt(W0,W1)        ~> #push [structural]
    rule SGT        W0 W1 => sgt(W0,W1)        ~> #push [structural]
    rule EQ         W0 W1 => W0 ==Word W1      ~> #push [structural]
    rule AND        W0 W1 => bitwiseand(W0,W1) ~> #push [structural]
    rule EVMOR      W0 W1 => bitwiseor(W0,W1)  ~> #push [structural]
    rule XOR        W0 W1 => bitwisexor(W0,W1) ~> #push [structural]
    rule BYTE       W0 W1 => getbyte(W0,W1)    ~> #push [structural]
    rule SHA3       W0 W1 => sha3(W0,W1)       ~> #push [structural]

    syntax TernStackOp ::= "ADDMOD" | "MULMOD"
    syntax KItem ::= TernStackOp Word Word Word

    rule ADDMOD W0 W1 W2 => addmod(W0,W1,W2) ~> #push [structural]
    rule MULMOD W0 W1 W2 => mulmod(W0,W1,W2) ~> #push [structural]

    syntax QuadStackOp ::= "CALL"
    syntax KItem ::= QuadStackOp Word Word Word Word

    syntax OpCode ::= NullStackOp | UnStackOp | BinStackOp | TernStackOp | QuadStackOp
endmodule
```

EVM Programs
------------

```k
module EVM-PROGRAM
    imports EVM-OPCODE

    syntax Program ::= List{OpCode, ";"}
 
    syntax KItem ::= OpCode

    syntax Map ::= "#pgmMap" "(" Program ")"         [function]
                 | "#pgmMap" "(" Int "," Program ")" [function]

    rule #pgmMap(PGM) => #pgmMap(0, PGM)
    rule #pgmMap(N, .Program) => .Map
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
    imports EVM-PROGRAM

    syntax AcctID  ::= Word | ".AcctID"
    syntax Account ::= "account" ":"
                       "-" "id" ":" AcctID
                       "-" "balance" ":" Word
                       "-" "program" ":" Program
                       "-" "storage" ":" WordList


    // JSON Format => Pretty Format
    
//            "095e7baea6a6c7c4c2dfeb977efac326af552d87" :
//                "balance" : "0x0de0b6b3a7658689",
//                "code" : "0x60006000600060006017730f572e5295c57f15886f9b263e2f6d2d6c7b5ec66103e8f1600055",
//                "nonce" : "0x00",
//                "storage" : {
//                    "0x00" : "0x01"
//                }

    syntax Transaction ::= "transaction" ":"
                           "-" "to" ":" AcctID
                           "-" "from" ":" AcctID
                           "-" "data" ":" WordList
                           "-" "value" ":" Int
                           "-" "gasPrice" ":" Int
                           "-" "gasLimit" ":" Int

    syntax JSONList ::= List{JSON,","}
    syntax JSON     ::= String
                      | String ":" JSON
                      | "{" JSONList "}"
                      | "[" JSONList "]"

    syntax AcctID   ::= "#parseID" "(" String ")"
    syntax Word     ::= "#parseBalance" "(" String ")"
    syntax Program  ::= "#dasmEVM" "(" String ")"
    syntax WordList ::= "#parseStorage" "(" JSON ")"

    syntax Account ::= JSON

    rule S : { "balance" : BALANCE
             , "code"    : CODE
             , "nonce"   : NONCE
             , "storage" : STORAGE
             }
      => account : - id : #parseID(S)
                   - balance : #parseBalance(BALANCE)
                   - program : #dasmEVM(CODE)
                   - storage : #parseStorage(STORAGE)

    syntax Process ::= "{" AcctID "|" Int "|" Int "|" WordStack "|" WordMap "}"
    syntax CallStack ::= ".CallStack"
                       | Process CallStack
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
    rule #gas( ADD          ) => 3
    rule #gas( SUB          ) => 3
    rule #gas( NOT          ) => 3
    rule #gas( LT           ) => 3
    rule #gas( GT           ) => 3
    rule #gas( SLT          ) => 3
    rule #gas( SGT          ) => 3
    rule #gas( EQ           ) => 3
    rule #gas( ISZERO       ) => 3
    rule #gas( AND          ) => 3
    rule #gas( EVMOR        ) => 3
    rule #gas( XOR          ) => 3
    rule #gas( BYTE         ) => 3
    rule #gas( CALLDATALOAD ) => 3
    rule #gas( MLOAD        ) => 3
    rule #gas( MSTORE       ) => 3
    rule #gas( MSTORE8      ) => 3
    rule #gas( PUSH I       ) => 3
    rule #gas( DUP I        ) => 3
    rule #gas( SWAP I       ) => 3

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
endmodule
```
