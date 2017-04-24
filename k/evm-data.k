// EVM Words
// =========

// EVM uses bounded 256 bit integer words. Here we provide the arithmetic of these
// words, as well as some data-structures over them.

// Word Operations
// ---------------

// To perform arithmetic on words, make sure that you use the corresponding
// `<op>Word` operators (eg. `+Word`), which will make sure that the correct
// rounding modes are used when performing the operations.


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


// Word Stack
// ----------

// EVM is a stack machine, and so needs a stack of words to operate on. The stack
// and some standard operations over it are provided here. Note that this stack
// also serves as a cons-list, so we provide some standard cons-list manipulation
// tools over it.


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


// Word Map
// --------

// Most of EVM data is held in finite maps. Here standard maps from `Word` to
// `Word` are provided. A common idiom is to assign a contiguous chunk of a map to
// a list (stack) of words, or to read a contiguous chunk of a map as a list, so
// the functionality for that is provided as well.


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


// EVM OpCodes
// ===========

// The EVM opcodes are provided here, as well as a dissasebler for programs in the
// EVM test format.

// We break up stack operations into groups by their arity so that we can pull out
// the correct number of arguments for each operation.

// NOTE: We have to call the opcode `OR` by `EVMOR` instead, because otherwise K
// has trouble parsing it/compiling the definition.


module EVM-OPCODE
    imports EVM-WORD
    imports STRING

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
                    | "LOG" "[" Word "]" | "BALANCE" | "BLOCKHASH" | "CALLCODE" | "CALLDATACOPY" | "CODECOPY"
                    | "CREATE" | "EXTCODECOPY" | "JUMPDEST" | "JUMPI" | "SLOAD" | "SSTORE" | "SUICIDE"
 // --------------------------------------------------------------------------------------------------

    syntax OpCodes ::= ".OpCodes"
                     | OpCode ";" OpCodes
 // -------------------------------------

    syntax OpCodeMap ::= ".OpCodeMap"
                       | Map

    rule .OpCodeMap => .Map [macro]

    syntax Map ::= #asMap ( OpCodes ) [function]
                 | #asMap ( Int , OpCodes ) [function]
 // --------------------------------------------------
    rule #asMap( OPS:OpCodes )         => #asMap(0, OPS)
    rule #asMap( N , .OpCodes )        => .Map
    rule #asMap( N , OP:OpCode ; OCS ) => N |-> OP #asMap(N +Int 1, OCS)

    syntax KItem ::= OpCode
                   | UnStackOp Word
                   | BinStackOp Word Word
                   | TernStackOp Word Word Word
                   | QuadStackOp Word Word Word Word


// The default EVM test-set format is JSON, where the data is hex-encoded. A
// dissassembler is provided here for the basic data so that both the JSON and our
// pretty format can be read in.


    syntax Word ::= #parseHexWord ( String ) [function]
 // ---------------------------------------------------
    rule #parseHexWord("")   => 0
    rule #parseHexWord("0x") => 0
    rule #parseHexWord(S)    => String2Base(replaceAll(S, "0x", ""), 16)
      requires (S =/=String "") andBool (S =/=String "0x")

    syntax OpCodes ::= #dasmOpCodes ( String ) [function]
 // -----------------------------------------------------
    rule #dasmOpCodes( "" ) => .OpCodes
    rule #dasmOpCodes( S )  => #dasmOpCode(substrString(S, 0, 2), substrString(S, 2, lengthString(S)))
      requires lengthString(S) >=Int 2

    syntax OpCodes ::= #dasmPUSH ( Word , String ) [function]
 // ---------------------------------------------------------
    rule #dasmPUSH(N, S) =>   PUSH [ N ] #parseHexWord(substrString(S, 0, N *Int 2))
                            ; #dasmOpCodes(substrString(S, N *Int 2, lengthString(S)))
      requires lengthString(S) >=Int (N *Int 2)

    syntax OpCodes ::= #dasmDUP ( Word , String ) [function]
 // --------------------------------------------------------
    syntax OpCodes ::= #dasmSWAP ( Word , String ) [function]
 // ---------------------------------------------------------
    syntax OpCodes ::= #dasmLOG ( Word , String ) [function]
 // --------------------------------------------------------

    syntax WordStack ::= #parseWordStack ( String ) [function]
 // ----------------------------------------------------------
    rule #parseWordStack( "" ) => .WordStack
    rule #parseWordStack( S )  => #parseHexWord(substrString(S, 0, 2)) : #parseWordStack(substrString(S, 2, lengthString(S)))
      requires lengthString(S) >=Int 2

    syntax OpCodes ::= #dasmOpCode ( String , String ) [function]
 // -------------------------------------------------------------
    rule #dasmOpCode("00", S) => STOP         ; #dasmOpCodes(S)
    rule #dasmOpCode("01", S) => ADD          ; #dasmOpCodes(S)
    rule #dasmOpCode("02", S) => MUL          ; #dasmOpCodes(S)
    rule #dasmOpCode("03", S) => SUB          ; #dasmOpCodes(S)
    rule #dasmOpCode("04", S) => DIV          ; #dasmOpCodes(S)
    rule #dasmOpCode("05", S) => SDIV         ; #dasmOpCodes(S)
    rule #dasmOpCode("06", S) => MOD          ; #dasmOpCodes(S)
    rule #dasmOpCode("07", S) => SMOD         ; #dasmOpCodes(S)
    rule #dasmOpCode("08", S) => ADDMOD       ; #dasmOpCodes(S)
    rule #dasmOpCode("09", S) => MULMOD       ; #dasmOpCodes(S)
    rule #dasmOpCode("0a", S) => EXP          ; #dasmOpCodes(S)
    rule #dasmOpCode("0b", S) => SIGNEXTEND   ; #dasmOpCodes(S)
    rule #dasmOpCode("10", S) => LT           ; #dasmOpCodes(S)
    rule #dasmOpCode("11", S) => GT           ; #dasmOpCodes(S)
    rule #dasmOpCode("12", S) => SLT          ; #dasmOpCodes(S)
    rule #dasmOpCode("13", S) => SGT          ; #dasmOpCodes(S)
    rule #dasmOpCode("14", S) => EQ           ; #dasmOpCodes(S)
    rule #dasmOpCode("15", S) => ISZERO       ; #dasmOpCodes(S)
    rule #dasmOpCode("16", S) => AND          ; #dasmOpCodes(S)
    rule #dasmOpCode("17", S) => EVMOR        ; #dasmOpCodes(S)
    rule #dasmOpCode("18", S) => XOR          ; #dasmOpCodes(S)
    rule #dasmOpCode("19", S) => NOT          ; #dasmOpCodes(S)
    rule #dasmOpCode("1a", S) => BYTE         ; #dasmOpCodes(S)
    rule #dasmOpCode("20", S) => SHA3         ; #dasmOpCodes(S)
    rule #dasmOpCode("30", S) => ADDRESS      ; #dasmOpCodes(S)
    rule #dasmOpCode("31", S) => BALANCE      ; #dasmOpCodes(S)
    rule #dasmOpCode("32", S) => ORIGIN       ; #dasmOpCodes(S)
    rule #dasmOpCode("33", S) => CALLER       ; #dasmOpCodes(S)
    rule #dasmOpCode("34", S) => CALLVALUE    ; #dasmOpCodes(S)
    rule #dasmOpCode("35", S) => CALLDATALOAD ; #dasmOpCodes(S)
    rule #dasmOpCode("36", S) => CALLDATASIZE ; #dasmOpCodes(S)
    rule #dasmOpCode("37", S) => CALLDATACOPY ; #dasmOpCodes(S)
    rule #dasmOpCode("38", S) => CODESIZE     ; #dasmOpCodes(S)
    rule #dasmOpCode("39", S) => CODECOPY     ; #dasmOpCodes(S)
    rule #dasmOpCode("3a", S) => GASPRICE     ; #dasmOpCodes(S)
    rule #dasmOpCode("3b", S) => EXTCODESIZE  ; #dasmOpCodes(S)
    rule #dasmOpCode("3c", S) => EXTCODECOPY  ; #dasmOpCodes(S)
    rule #dasmOpCode("40", S) => BLOCKHASH    ; #dasmOpCodes(S)
    rule #dasmOpCode("41", S) => COINBASE     ; #dasmOpCodes(S)
    rule #dasmOpCode("42", S) => TIMESTAMP    ; #dasmOpCodes(S)
    rule #dasmOpCode("43", S) => NUMBER       ; #dasmOpCodes(S)
    rule #dasmOpCode("44", S) => DIFFICULTY   ; #dasmOpCodes(S)
    rule #dasmOpCode("45", S) => GASLIMIT     ; #dasmOpCodes(S)
    rule #dasmOpCode("50", S) => POP          ; #dasmOpCodes(S)
    rule #dasmOpCode("51", S) => MLOAD        ; #dasmOpCodes(S)
    rule #dasmOpCode("52", S) => MSTORE       ; #dasmOpCodes(S)
    rule #dasmOpCode("53", S) => MSTORE8      ; #dasmOpCodes(S)
    rule #dasmOpCode("54", S) => SLOAD        ; #dasmOpCodes(S)
    rule #dasmOpCode("55", S) => SSTORE       ; #dasmOpCodes(S)
    rule #dasmOpCode("56", S) => JUMP         ; #dasmOpCodes(S)
    rule #dasmOpCode("57", S) => JUMPI        ; #dasmOpCodes(S)
    rule #dasmOpCode("58", S) => PC           ; #dasmOpCodes(S)
    rule #dasmOpCode("59", S) => MSIZE        ; #dasmOpCodes(S)
    rule #dasmOpCode("5a", S) => GAS          ; #dasmOpCodes(S)
    rule #dasmOpCode("5b", S) => JUMPDEST     ; #dasmOpCodes(S)
    rule #dasmOpCode("60", S) => #dasmPUSH(1, S)
    rule #dasmOpCode("61", S) => #dasmPUSH(2, S)
    rule #dasmOpCode("62", S) => #dasmPUSH(3, S)
    rule #dasmOpCode("63", S) => #dasmPUSH(4, S)
    rule #dasmOpCode("64", S) => #dasmPUSH(5, S)
    rule #dasmOpCode("65", S) => #dasmPUSH(6, S)
    rule #dasmOpCode("66", S) => #dasmPUSH(7, S)
    rule #dasmOpCode("67", S) => #dasmPUSH(8, S)
    rule #dasmOpCode("68", S) => #dasmPUSH(9, S)
    rule #dasmOpCode("69", S) => #dasmPUSH(10, S)
    rule #dasmOpCode("6a", S) => #dasmPUSH(11, S)
    rule #dasmOpCode("6b", S) => #dasmPUSH(12, S)
    rule #dasmOpCode("6c", S) => #dasmPUSH(13, S)
    rule #dasmOpCode("6d", S) => #dasmPUSH(14, S)
    rule #dasmOpCode("6e", S) => #dasmPUSH(15, S)
    rule #dasmOpCode("6f", S) => #dasmPUSH(16, S)
    rule #dasmOpCode("70", S) => #dasmPUSH(17, S)
    rule #dasmOpCode("71", S) => #dasmPUSH(18, S)
    rule #dasmOpCode("72", S) => #dasmPUSH(19, S)
    rule #dasmOpCode("73", S) => #dasmPUSH(20, S)
    rule #dasmOpCode("74", S) => #dasmPUSH(21, S)
    rule #dasmOpCode("75", S) => #dasmPUSH(22, S)
    rule #dasmOpCode("76", S) => #dasmPUSH(23, S)
    rule #dasmOpCode("77", S) => #dasmPUSH(24, S)
    rule #dasmOpCode("78", S) => #dasmPUSH(25, S)
    rule #dasmOpCode("79", S) => #dasmPUSH(26, S)
    rule #dasmOpCode("7a", S) => #dasmPUSH(27, S)
    rule #dasmOpCode("7b", S) => #dasmPUSH(28, S)
    rule #dasmOpCode("7c", S) => #dasmPUSH(29, S)
    rule #dasmOpCode("7d", S) => #dasmPUSH(30, S)
    rule #dasmOpCode("7e", S) => #dasmPUSH(31, S)
    rule #dasmOpCode("7f", S) => #dasmPUSH(32, S)
    rule #dasmOpCode("80", S) => #dasmDUP(1, S)
    rule #dasmOpCode("81", S) => #dasmDUP(2, S)
    rule #dasmOpCode("82", S) => #dasmDUP(3, S)
    rule #dasmOpCode("83", S) => #dasmDUP(4, S)
    rule #dasmOpCode("84", S) => #dasmDUP(5, S)
    rule #dasmOpCode("85", S) => #dasmDUP(6, S)
    rule #dasmOpCode("86", S) => #dasmDUP(7, S)
    rule #dasmOpCode("87", S) => #dasmDUP(8, S)
    rule #dasmOpCode("88", S) => #dasmDUP(9, S)
    rule #dasmOpCode("89", S) => #dasmDUP(10, S)
    rule #dasmOpCode("8a", S) => #dasmDUP(11, S)
    rule #dasmOpCode("8b", S) => #dasmDUP(12, S)
    rule #dasmOpCode("8c", S) => #dasmDUP(13, S)
    rule #dasmOpCode("8d", S) => #dasmDUP(14, S)
    rule #dasmOpCode("8e", S) => #dasmDUP(15, S)
    rule #dasmOpCode("8f", S) => #dasmDUP(16, S)
    rule #dasmOpCode("90", S) => #dasmSWAP(1, S)
    rule #dasmOpCode("91", S) => #dasmSWAP(2, S)
    rule #dasmOpCode("92", S) => #dasmSWAP(3, S)
    rule #dasmOpCode("93", S) => #dasmSWAP(4, S)
    rule #dasmOpCode("94", S) => #dasmSWAP(5, S)
    rule #dasmOpCode("95", S) => #dasmSWAP(6, S)
    rule #dasmOpCode("96", S) => #dasmSWAP(7, S)
    rule #dasmOpCode("97", S) => #dasmSWAP(8, S)
    rule #dasmOpCode("98", S) => #dasmSWAP(9, S)
    rule #dasmOpCode("99", S) => #dasmSWAP(10, S)
    rule #dasmOpCode("9a", S) => #dasmSWAP(11, S)
    rule #dasmOpCode("9b", S) => #dasmSWAP(12, S)
    rule #dasmOpCode("9c", S) => #dasmSWAP(13, S)
    rule #dasmOpCode("9d", S) => #dasmSWAP(14, S)
    rule #dasmOpCode("9e", S) => #dasmSWAP(15, S)
    rule #dasmOpCode("9f", S) => #dasmSWAP(16, S)
    rule #dasmOpCode("a0", S) => #dasmLOG(0, S)
    rule #dasmOpCode("a1", S) => #dasmLOG(1, S)
    rule #dasmOpCode("a2", S) => #dasmLOG(2, S)
    rule #dasmOpCode("a3", S) => #dasmLOG(3, S)
    rule #dasmOpCode("a4", S) => #dasmLOG(4, S)
    rule #dasmOpCode("f0", S) => CREATE   ; #dasmOpCodes(S)
    rule #dasmOpCode("f1", S) => CALL     ; #dasmOpCodes(S)
    rule #dasmOpCode("f2", S) => CALLCODE ; #dasmOpCodes(S)
    rule #dasmOpCode("f3", S) => RETURN   ; #dasmOpCodes(S)
    rule #dasmOpCode("ff", S) => SUICIDE  ; #dasmOpCodes(S)
endmodule

