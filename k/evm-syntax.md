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
                         | "PUSH" "[" Word "]" Word
                         | "#checkStackSize"
                         | "STACK_OVERFLOW"
                         | "DUP" "[" Word "]"
                         | "SWAP" "[" Word "]"
                         | "PC" | "MSIZE" | "GAS"
                         | "STOP" | "ADDRESS" | "ORIGIN" | "CALLER"
                         | "CALLVALUE" | "CALLDATASIZE" | "GASPRICE" | "CODESIZE"
                         | "COINBASE" | "TIMESTAMP" | "NUMBER" | "DIFFICULTY" | "GASLIMIT"
    syntax KItem ::= NullStackOp

    // rule PUSH N => N ~> #push ~> #checkStackSize [structural]
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
                    | "LOG" "[" Int "]" | "BALANCE" | "BLOCKHASH" | "CALLCODE" | "CALLDATACOPY" | "CODECOPY" | "CREATE" | "EXTCODECOPY" | "JUMPDEST" | "JUMPI" | "SLOAD" | "SSTORE" | "SUICIDE"
endmodule
```

EVM Programs
------------

```k
module EVM-PROGRAM
    imports EVM-OPCODE

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

    syntax JSONList ::= List{JSON,","}
    syntax JSON     ::= String
                      | String ":" JSON
                      | "{" JSONList "}"
                      | "[" JSONList "]"

    syntax Word ::= #parseHexWord ( String ) [function]
    rule #parseHexWord("")   => 0
    rule #parseHexWord("0x") => 0
    rule #parseHexWord(S)    => String2Base(replaceAll(S, "0x", ""), 16)
      requires (S =/=String "") andBool (S =/=String "0x")

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

    syntax OpCodes ::= #dasmProgram ( String )         [function]
                     | #dasmOpcode ( String , String ) [function]
                     | #dasmPUSH ( Int , String )      [function]
                     | #dasmDUP  ( Int , String )      [function]
                     | #dasmSWAP ( Int , String )      [function]
                     | #dasmLOG  ( Int , String )      [function]

    rule #dasmPUSH(N, S) =>   PUSH [ N ] #parseHexWord(substrString(S, 0, N *Int 2))
                            ; #dasmProgram(substrString(S, N *Int 2, lengthString(S)))
      requires lengthString(S) >=Int (N *Int 2)

    rule #dasmOpcode("00", S) => STOP         ; #dasmProgram(S)
    rule #dasmOpcode("01", S) => ADD          ; #dasmProgram(S)
    rule #dasmOpcode("02", S) => MUL          ; #dasmProgram(S)
    rule #dasmOpcode("03", S) => SUB          ; #dasmProgram(S)
    rule #dasmOpcode("04", S) => DIV          ; #dasmProgram(S)
    rule #dasmOpcode("05", S) => SDIV         ; #dasmProgram(S)
    rule #dasmOpcode("06", S) => MOD          ; #dasmProgram(S)
    rule #dasmOpcode("07", S) => SMOD         ; #dasmProgram(S)
    rule #dasmOpcode("08", S) => ADDMOD       ; #dasmProgram(S)
    rule #dasmOpcode("09", S) => MULMOD       ; #dasmProgram(S)
    rule #dasmOpcode("0a", S) => EXP          ; #dasmProgram(S)
    rule #dasmOpcode("0b", S) => SIGNEXTEND   ; #dasmProgram(S)
    rule #dasmOpcode("10", S) => LT           ; #dasmProgram(S)
    rule #dasmOpcode("11", S) => GT           ; #dasmProgram(S)
    rule #dasmOpcode("12", S) => SLT          ; #dasmProgram(S)
    rule #dasmOpcode("13", S) => SGT          ; #dasmProgram(S)
    rule #dasmOpcode("14", S) => EQ           ; #dasmProgram(S)
    rule #dasmOpcode("15", S) => ISZERO       ; #dasmProgram(S)
    rule #dasmOpcode("16", S) => AND          ; #dasmProgram(S)
    rule #dasmOpcode("17", S) => EVMOR        ; #dasmProgram(S)
    rule #dasmOpcode("18", S) => XOR          ; #dasmProgram(S)
    rule #dasmOpcode("19", S) => NOT          ; #dasmProgram(S)
    rule #dasmOpcode("1a", S) => BYTE         ; #dasmProgram(S)
    rule #dasmOpcode("20", S) => SHA3         ; #dasmProgram(S)
    rule #dasmOpcode("30", S) => ADDRESS      ; #dasmProgram(S)
    rule #dasmOpcode("31", S) => BALANCE      ; #dasmProgram(S)
    rule #dasmOpcode("32", S) => ORIGIN       ; #dasmProgram(S)
    rule #dasmOpcode("33", S) => CALLER       ; #dasmProgram(S)
    rule #dasmOpcode("34", S) => CALLVALUE    ; #dasmProgram(S)
    rule #dasmOpcode("35", S) => CALLDATALOAD ; #dasmProgram(S)
    rule #dasmOpcode("36", S) => CALLDATASIZE ; #dasmProgram(S)
    rule #dasmOpcode("37", S) => CALLDATACOPY ; #dasmProgram(S)
    rule #dasmOpcode("38", S) => CODESIZE     ; #dasmProgram(S)
    rule #dasmOpcode("39", S) => CODECOPY     ; #dasmProgram(S)
    rule #dasmOpcode("3a", S) => GASPRICE     ; #dasmProgram(S)
    rule #dasmOpcode("3b", S) => EXTCODESIZE  ; #dasmProgram(S)
    rule #dasmOpcode("3c", S) => EXTCODECOPY  ; #dasmProgram(S)
    rule #dasmOpcode("40", S) => BLOCKHASH    ; #dasmProgram(S)
    rule #dasmOpcode("41", S) => COINBASE     ; #dasmProgram(S)
    rule #dasmOpcode("42", S) => TIMESTAMP    ; #dasmProgram(S)
    rule #dasmOpcode("43", S) => NUMBER       ; #dasmProgram(S)
    rule #dasmOpcode("44", S) => DIFFICULTY   ; #dasmProgram(S)
    rule #dasmOpcode("45", S) => GASLIMIT     ; #dasmProgram(S)
    rule #dasmOpcode("50", S) => POP          ; #dasmProgram(S)
    rule #dasmOpcode("51", S) => MLOAD        ; #dasmProgram(S)
    rule #dasmOpcode("52", S) => MSTORE       ; #dasmProgram(S)
    rule #dasmOpcode("53", S) => MSTORE8      ; #dasmProgram(S)
    rule #dasmOpcode("54", S) => SLOAD        ; #dasmProgram(S)
    rule #dasmOpcode("55", S) => SSTORE       ; #dasmProgram(S)
    rule #dasmOpcode("56", S) => JUMP         ; #dasmProgram(S)
    rule #dasmOpcode("57", S) => JUMPI        ; #dasmProgram(S)
    rule #dasmOpcode("58", S) => PC           ; #dasmProgram(S)
    rule #dasmOpcode("59", S) => MSIZE        ; #dasmProgram(S)
    rule #dasmOpcode("5a", S) => GAS          ; #dasmProgram(S)
    rule #dasmOpcode("5b", S) => JUMPDEST     ; #dasmProgram(S)
    rule #dasmOpcode("60", S) => #dasmPUSH(1, S)
    rule #dasmOpcode("61", S) => #dasmPUSH(2, S)
    rule #dasmOpcode("62", S) => #dasmPUSH(3, S)
    rule #dasmOpcode("63", S) => #dasmPUSH(4, S)
    rule #dasmOpcode("64", S) => #dasmPUSH(5, S)
    rule #dasmOpcode("65", S) => #dasmPUSH(6, S)
    rule #dasmOpcode("66", S) => #dasmPUSH(7, S)
    rule #dasmOpcode("67", S) => #dasmPUSH(8, S)
    rule #dasmOpcode("68", S) => #dasmPUSH(9, S)
    rule #dasmOpcode("69", S) => #dasmPUSH(10, S)
    rule #dasmOpcode("6a", S) => #dasmPUSH(11, S)
    rule #dasmOpcode("6b", S) => #dasmPUSH(12, S)
    rule #dasmOpcode("6c", S) => #dasmPUSH(13, S)
    rule #dasmOpcode("6d", S) => #dasmPUSH(14, S)
    rule #dasmOpcode("6e", S) => #dasmPUSH(15, S)
    rule #dasmOpcode("6f", S) => #dasmPUSH(16, S)
    rule #dasmOpcode("70", S) => #dasmPUSH(17, S)
    rule #dasmOpcode("71", S) => #dasmPUSH(18, S)
    rule #dasmOpcode("72", S) => #dasmPUSH(19, S)
    rule #dasmOpcode("73", S) => #dasmPUSH(20, S)
    rule #dasmOpcode("74", S) => #dasmPUSH(21, S)
    rule #dasmOpcode("75", S) => #dasmPUSH(22, S)
    rule #dasmOpcode("76", S) => #dasmPUSH(23, S)
    rule #dasmOpcode("77", S) => #dasmPUSH(24, S)
    rule #dasmOpcode("78", S) => #dasmPUSH(25, S)
    rule #dasmOpcode("79", S) => #dasmPUSH(26, S)
    rule #dasmOpcode("7a", S) => #dasmPUSH(27, S)
    rule #dasmOpcode("7b", S) => #dasmPUSH(28, S)
    rule #dasmOpcode("7c", S) => #dasmPUSH(29, S)
    rule #dasmOpcode("7d", S) => #dasmPUSH(30, S)
    rule #dasmOpcode("7e", S) => #dasmPUSH(31, S)
    rule #dasmOpcode("7f", S) => #dasmPUSH(32, S)
    rule #dasmOpcode("80", S) => #dasmDUP(1, S)
    rule #dasmOpcode("81", S) => #dasmDUP(2, S)
    rule #dasmOpcode("82", S) => #dasmDUP(3, S)
    rule #dasmOpcode("83", S) => #dasmDUP(4, S)
    rule #dasmOpcode("84", S) => #dasmDUP(5, S)
    rule #dasmOpcode("85", S) => #dasmDUP(6, S)
    rule #dasmOpcode("86", S) => #dasmDUP(7, S)
    rule #dasmOpcode("87", S) => #dasmDUP(8, S)
    rule #dasmOpcode("88", S) => #dasmDUP(9, S)
    rule #dasmOpcode("89", S) => #dasmDUP(10, S)
    rule #dasmOpcode("8a", S) => #dasmDUP(11, S)
    rule #dasmOpcode("8b", S) => #dasmDUP(12, S)
    rule #dasmOpcode("8c", S) => #dasmDUP(13, S)
    rule #dasmOpcode("8d", S) => #dasmDUP(14, S)
    rule #dasmOpcode("8e", S) => #dasmDUP(15, S)
    rule #dasmOpcode("8f", S) => #dasmDUP(16, S)
    rule #dasmOpcode("90", S) => #dasmSWAP(1, S)
    rule #dasmOpcode("91", S) => #dasmSWAP(2, S)
    rule #dasmOpcode("92", S) => #dasmSWAP(3, S)
    rule #dasmOpcode("93", S) => #dasmSWAP(4, S)
    rule #dasmOpcode("94", S) => #dasmSWAP(5, S)
    rule #dasmOpcode("95", S) => #dasmSWAP(6, S)
    rule #dasmOpcode("96", S) => #dasmSWAP(7, S)
    rule #dasmOpcode("97", S) => #dasmSWAP(8, S)
    rule #dasmOpcode("98", S) => #dasmSWAP(9, S)
    rule #dasmOpcode("99", S) => #dasmSWAP(10, S)
    rule #dasmOpcode("9a", S) => #dasmSWAP(11, S)
    rule #dasmOpcode("9b", S) => #dasmSWAP(12, S)
    rule #dasmOpcode("9c", S) => #dasmSWAP(13, S)
    rule #dasmOpcode("9d", S) => #dasmSWAP(14, S)
    rule #dasmOpcode("9e", S) => #dasmSWAP(15, S)
    rule #dasmOpcode("9f", S) => #dasmSWAP(16, S)
    rule #dasmOpcode("a0", S) => #dasmLOG(0, S)
    rule #dasmOpcode("a1", S) => #dasmLOG(1, S)
    rule #dasmOpcode("a2", S) => #dasmLOG(2, S)
    rule #dasmOpcode("a3", S) => #dasmLOG(3, S)
    rule #dasmOpcode("a4", S) => #dasmLOG(4, S)
    rule #dasmOpcode("f0", S) => CREATE   ; #dasmProgram(S)
    rule #dasmOpcode("f1", S) => CALL     ; #dasmProgram(S)
    rule #dasmOpcode("f2", S) => CALLCODE ; #dasmProgram(S)
    rule #dasmOpcode("f3", S) => RETURN   ; #dasmProgram(S)
    rule #dasmOpcode("ff", S) => SUICIDE  ; #dasmProgram(S)

    rule #dasmProgram("") => .OpCodes
    rule #dasmProgram(S)  => #dasmOpcode(substrString(S, 0, 2), substrString(S, 2, lengthString(S)))
      requires lengthString(S) >=Int 2

    syntax Map ::= #parseStorage ( JSON )         [function]
    syntax WordList ::= #parseData ( JSON )       [function]
                      | #parseWordList ( String ) [function]

    rule #parseData( S:String ) => #parseWordList(S)
    rule #parseWordList( S )    => #parseHexWord(substrString(S, 0, 2)) , #parseWordList(substrString(S, 2, lengthString(S)))
      requires lengthString(S) >=Int 2
    rule #parseWordList( S )    => #parseHexWord(S)
      requires lengthString(S) <Int 2

    rule #parseStorage( { .JSONList } )                   => .Map
    rule #parseStorage( { KEY : (VALUE:String) , REST } ) => (#parseHexWord(KEY) |-> #parseHexWord(VALUE)) #parseStorage({ REST })

    syntax Int ::= #parseValue ( JSON )    [function]
                 | #parseGasPrice ( JSON ) [function]
                 | #parseGasLimit ( JSON ) [function]

    rule #parseValue( S:String )    => #parseHexWord(S)
    rule #parseGasPrice( S:String ) => #parseHexWord(S)
    rule #parseGasLimit( S:String ) => #parseHexWord(S)

    syntax AcctID ::= #parseID ( JSON ) [function]

    rule #parseID( S:String ) => #parseHexWord(S)

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
                                             "-" "value"    ":" Int
                                             "-" "gasPrice" ":" Int
                                             "-" "gasLimit" ":" Int

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

    syntax Process ::= "{" AcctID "|" Int "|" Int "|" WordStack "|" WordMap "}"
    syntax CallStack ::= ".CallStack"
                       | Process CallStack
endmodule
```
