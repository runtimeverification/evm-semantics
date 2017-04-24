EVM Words
=========

EVM uses bounded 256 bit integer words. Here we provide the arithmetic of these
words, as well as some data-structures over them.

Word Operations
---------------

To perform arithmetic on words, make sure that you use the corresponding
`<op>Word` operators (eg. `+Word`), which will make sure that the correct
rounding modes are used when performing the operations.

```k
module EVM-WORD

    syntax KResult ::= Int 

    syntax Word ::= Int
                  | "#symbolicWord"               [function]
                  | chop ( Int )                  [function]
                  | bool2Word ( Bool )            [function]
                  | Word "+Word" Word             [function]
                  | Word "*Word" Word             [function]
                  | Word "-Word" Word             [function]
                  | Word "/Word" Word             [function]
                  | Word "^Word" Word             [function]
                  | Word "%Word" Word             [function]
                  | signextend ( Word , Word )    [function] // needs implemented
                  | Word "<Word" Word             [function]
                  | Word ">Word" Word             [function]
                  | Word "==Word" Word            [function]
                  | bitwisenot ( Word )           [function] // needs implemented
                  | sdiv ( Word , Word )          [function] // needs implemented
                  | smod ( Word , Word )          [function] // needs implemented
                  | slt ( Word , Word )           [function] // needs implemented
                  | sgt ( Word , Word )           [function] // needs implemented
                  | bitwiseand ( Word , Word )    [function] // needs implemented
                  | bitwiseor ( Word , Word )     [function] // needs implemented
                  | bitwisexor ( Word , Word )    [function] // needs implemented
                  | getbyte ( Word , Word )       [function] // needs implemented
                  | sha3 ( Word , Word )          [function] // needs implemented
                  | addmod ( Word , Word , Word ) [function]
                  | mulmod ( Word , Word , Word ) [function]

    rule #symbolicWord => ?X:Int

    rule chop( I:Int ) => I                           requires I <Int (2 ^Int 256) andBool I >=Int 0
    rule chop( I:Int ) => chop( I +Int (2 ^Int 256) ) requires I <Int 0
    rule chop( I:Int ) => chop( I -Int (2 ^Int 256) ) requires I >=Int (2 ^Int 256)

    rule bool2Word(true)  => 1
    rule bool2Word(false) => 0

    rule W0:Int +Word W1:Int  => chop( W0 +Int W1 )
    rule W0:Int -Word W1:Int  => chop( W0 -Int W1 )
    rule W0:Int *Word W1:Int  => chop( W0 *Int W1 )
    rule W0:Int /Word W1:Int  => chop( W0 /Int W1 )
    rule W0:Int ^Word W1:Int  => chop( W0 ^Int W1 )
    rule W0:Int <Word W1:Int  => bool2Word( W0 <Int W1 )
    rule W0:Int >Word W1:Int  => bool2Word( W0 >Int W1 )
    rule W0:Int ==Word W1:Int => bool2Word( W0 ==Int W1)
    rule W0:Int %Word W1:Int  => chop( W0 %Int W1 )

    rule addmod(W0:Int, W1:Int, 0)      => 0
    rule addmod(W0:Int, W1:Int, W2:Int) => chop((W0 +Int W1) %Int W2) [owise]

    rule mulmod(W0:Int, W1:Int, 0)      => 0
    rule mulmod(W0:Int, W1:Int, W2:Int) => chop((W0 *Int W1) %Int W2) [owise]
```

Word Stack
----------

EVM is a stack machine, and so needs a stack of words to operate on. The stack
and some standard operations over it are provided here. Note that this stack
also serves as a cons-list, so we provide some standard cons-list manipulation
tools over it.

```k
    syntax WordStack ::= ".WordStack"
                       | Word ":" WordStack

    syntax Word ::= WordStack "[" Word "]" [function]
 // -------------------------------------------------
    rule (W0 : WS)[0] => W0
    rule (W0 : WS)[N] => WS[N -Word 1] requires N >Word 0

    syntax Word ::= #stackSize ( WordStack ) [function]
 // ---------------------------------------------------
    rule #stackSize ( .WordStack ) => 0
    rule #stackSize ( W : WS )     => 1 +Word #stackSize(WS)

    syntax WordStack ::= #take ( Word , WordStack )
 // -----------------------------------------------
    rule #take(0, WS)            => .WordStack
    rule #take(N, (W:Word : WS)) => W : #take(N -Word 1, WS) requires N >Word 0
```

Word Map
--------

Most of EVM data is held in finite maps. Here standard maps from `Word` to
`Word` are provided. A common idiom is to assign a contiguous chunk of a map to
a list (stack) of words, or to read a contiguous chunk of a map as a list, so
the functionality for that is provided as well.

```k
    syntax WordMap ::= Map
                     | ".WordMap"

    rule .WordMap => .Map [macro]

    syntax WordMap ::= WordMap "[" Word ":=" WordStack "]" [function]
 // -----------------------------------------------------------------
    rule WM[N := .WordStack]   => WM
    rule WM[N := W0:Word : WS] => (WM[N <- W0])[N +Word 1 := WS]
    
    syntax WordMap ::= #asMap ( WordStack ) [function]
 // --------------------------------------------------
    rule #asMap(WS) => .WordMap [ 0 := WS ]

    syntax WordStack ::= #range ( WordMap , Word , Word ) [function]
 // ----------------------------------------------------------------
    rule #range(WM,         N, M) => .WordStack                           requires M ==Word 0
    rule #range(N |-> W WM, N, M) => W : #range(WM, N +Word 1, M -Word 1) requires M >Word 0
endmodule
```

EVM OpCodes
===========

The EVM opcodes are provided here, as well as a dissasebler for programs in the
EVM test format.

We break up stack operations into groups by their arity so that we can pull out
the correct number of arguments for each operation.

NOTE: We have to call the opcode `OR` by `EVMOR` instead, because otherwise K
has trouble parsing it/compiling the definition.

```k
module EVM-OPCODE
    imports EVM-WORD

    syntax InternalOps ::= "#push"
                         | "#checkStackSize"
 // ----------------------------------------
    // rule PUSH N => N ~> #push ~> #checkStackSize [structural]
    rule (I:Int ~> #checkStackSize) => .              requires I <Int  1024
    rule (I:Int ~> #checkStackSize) => STACK_OVERFLOW requires I >=Int 1024

    syntax NullStackOp ::= "PUSH" "[" Word "]" Word
                         | "STACK_OVERFLOW"
                         | "DUP" "[" Word "]"
                         | "SWAP" "[" Word "]"
                         | "PC" | "MSIZE" | "GAS"
                         | "STOP" | "ADDRESS" | "ORIGIN" | "CALLER"
                         | "CALLVALUE" | "CALLDATASIZE" | "GASPRICE" | "CODESIZE"
                         | "COINBASE" | "TIMESTAMP" | "NUMBER" | "DIFFICULTY" | "GASLIMIT"
 // --------------------------------------------------------------------------------------

    syntax UnStackOp ::= "ISZERO" | "NOT" | "POP"
                       | "JUMP" | "MLOAD"
                       | "CALLDATALOAD" | "EXTCODESIZE"
 // ---------------------------------------------------
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
 // ---------------------------------------------------------------
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
 // ------------------------------------------
    rule ADDMOD W0 W1 W2 => addmod(W0,W1,W2) ~> #push [structural]
    rule MULMOD W0 W1 W2 => mulmod(W0,W1,W2) ~> #push [structural]

    syntax QuadStackOp ::= "CALL"
 // -----------------------------
 
    syntax OpCode ::= NullStackOp | UnStackOp | BinStackOp | TernStackOp | QuadStackOp | InternalOps
                    | "LOG" "[" Int "]" | "BALANCE" | "BLOCKHASH" | "CALLCODE" | "CALLDATACOPY" | "CODECOPY"
                    | "CREATE" | "EXTCODECOPY" | "JUMPDEST" | "JUMPI" | "SLOAD" | "SSTORE" | "SUICIDE"
 // --------------------------------------------------------------------------------------------------

    syntax KItem ::= OpCode
                   | UnStackOp Word
                   | BinStackOp Word Word
                   | TernStackOp Word Word Word
                   | QuadStackOp Word Word Word Word
```

The default EVM test-set format is JSON, where the data is hex-encoded. A
dissassembler is provided here for the basic data so that both the JSON and our
pretty format can be read in.

```k
    syntax Word ::= #parseHexWord ( String ) [function]
    rule #parseHexWord("")   => 0
    rule #parseHexWord("0x") => 0
    rule #parseHexWord(S)    => String2Base(replaceAll(S, "0x", ""), 16)
      requires (S =/=String "") andBool (S =/=String "0x")
      

    syntax OpCodes ::= #dasmProgram ( String )         [function]
                     | #dasmOpcode ( String , String ) [function]
                     | #dasmPUSH ( Int , String )      [function]
                     | #dasmDUP  ( Int , String )      [function]
                     | #dasmSWAP ( Int , String )      [function]
                     | #dasmLOG  ( Int , String )      [function]

    rule #dasmPUSH(N, S) =>   PUSH [ N ] #parseHexWord(substrString(S, 0, N *Int 2))
                            ; #dasmProgram(substrString(S, N *Int 2, lengthString(S)))
      requires lengthString(S) >=Int (N *Int 2)


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
endmodule
```
