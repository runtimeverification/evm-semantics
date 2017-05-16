EVM Programs
============

The EVM opcodes are provided here, as well as a dissasebler for programs in the
EVM test format. We break up stack operations into groups by their arity so that
we can pull out the correct number of arguments for each operation.

EVM OpCodes
-----------

NOTE: We have to call the opcode `OR` by `EVMOR` instead, because otherwise K
has trouble parsing it/compiling the definition.

```k
requires "words.k"

module EVM-OPCODE
    imports EVM-WORD
    imports STRING

    syntax InternalOps ::= "#push" | "#setStack" WordStack | "#checkStackSize"
 // --------------------------------------------------------------------------
    rule (I:Int ~> #checkStackSize) => .              requires I <Int  1024
    rule (I:Int ~> #checkStackSize) => STACK_OVERFLOW requires I >=Int 1024

    syntax NullStackOp ::= "STACK_OVERFLOW"
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

    syntax CallOp ::= "CALL"
    syntax PushOp ::= PUSH ( Word )
    syntax LogOp  ::= LOG ( Word )
    syntax SpecialOp ::= "CALL"
                       | PUSH ( Word )
                       | LOG ( Word )
 // ---------------------------------

    syntax StackOp ::= DUP ( Word ) | SWAP ( Word )
 // -----------------------------------------------
    rule DUP(N)  WS:WordStack => #pushStack ((WS [ N -Word 1 ]) : WS)
    rule SWAP(N) (W0 : WS)    => #pushStack ((WS [ N -Word 1 ]) : (WS [ N -Word 1 := W0 ]))
```

Here, all the operators that have not been binned/implemented are thrown (as
well as the subsorts).

```k
    syntax OpCode ::= NullStackOp | UnStackOp | BinStackOp | TernStackOp | SpecialOp | StackOp | InternalOps
                    | "BALANCE" | "BLOCKHASH" | "CALLCODE" | "CALLDATACOPY" | "CODECOPY" | "CREATE" | "EXTCODECOPY"
                    | "JUMPDEST" | "JUMPI" | "SLOAD" | "SSTORE" | "DELEGATECALL" | "INVALID" | "SELFDESTRUCT"
 // ---------------------------------------------------------------------------------------------------------
    syntax KItem ::= OpCode
                   | UnStackOp Word
                   | BinStackOp Word Word
                   | TernStackOp Word Word Word
                   | CallOp Word Word Word Word Word Word Word
                   | StackOp WordStack
```

EVM Programs
------------

Lists of opcodes form programs. Deciding if an opcode is in a list will be
useful for modelling gas, and converting a program into a map of program-counter
to opcode is useful for execution.

```k
    syntax OpCodes ::= ".OpCodes"
                     | OpCode ";" OpCodes
 // -------------------------------------

    syntax Bool ::= OpCode "in" OpCodes
 // -----------------------------------
    rule OP in .OpCodes    => false
    rule OP in (OP ; OPS)  => true
    rule OP in (OP' ; OPS) => OP in OPS requires OP =/=K OP'

    syntax Map ::= #asMap ( OpCodes )       [function]
                 | #asMap ( Int , OpCodes ) [function]
 // --------------------------------------------------
    rule #asMap( OPS:OpCodes )         => #asMap(0, OPS)
    rule #asMap( N , .OpCodes )        => .Map
    rule #asMap( N , OP:OpCode ; OCS ) => (N |-> OP) #asMap(N +Int 1, OCS)
endmodule
```

EVM Disassembler
================

The default EVM test-set format is JSON, where the data is hex-encoded. A
dissassembler is provided here for the basic data so that both the JSON and our
pretty format can be read in.

```k
module EVM-DASM
    imports EVM-OPCODE

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
    rule #dasmOpCode("80", S) => DUP(1)  ; #dasmOpCodes(S)
    rule #dasmOpCode("81", S) => DUP(2)  ; #dasmOpCodes(S)
    rule #dasmOpCode("82", S) => DUP(3)  ; #dasmOpCodes(S)
    rule #dasmOpCode("83", S) => DUP(4)  ; #dasmOpCodes(S)
    rule #dasmOpCode("84", S) => DUP(5)  ; #dasmOpCodes(S)
    rule #dasmOpCode("85", S) => DUP(6)  ; #dasmOpCodes(S)
    rule #dasmOpCode("86", S) => DUP(7)  ; #dasmOpCodes(S)
    rule #dasmOpCode("87", S) => DUP(8)  ; #dasmOpCodes(S)
    rule #dasmOpCode("88", S) => DUP(9)  ; #dasmOpCodes(S)
    rule #dasmOpCode("89", S) => DUP(10) ; #dasmOpCodes(S)
    rule #dasmOpCode("8a", S) => DUP(11) ; #dasmOpCodes(S)
    rule #dasmOpCode("8b", S) => DUP(12) ; #dasmOpCodes(S)
    rule #dasmOpCode("8c", S) => DUP(13) ; #dasmOpCodes(S)
    rule #dasmOpCode("8d", S) => DUP(14) ; #dasmOpCodes(S)
    rule #dasmOpCode("8e", S) => DUP(15) ; #dasmOpCodes(S)
    rule #dasmOpCode("8f", S) => DUP(16) ; #dasmOpCodes(S)
    rule #dasmOpCode("90", S) => SWAP(1)  ; #dasmOpCodes(S)
    rule #dasmOpCode("91", S) => SWAP(2)  ; #dasmOpCodes(S)
    rule #dasmOpCode("92", S) => SWAP(3)  ; #dasmOpCodes(S)
    rule #dasmOpCode("93", S) => SWAP(4)  ; #dasmOpCodes(S)
    rule #dasmOpCode("94", S) => SWAP(5)  ; #dasmOpCodes(S)
    rule #dasmOpCode("95", S) => SWAP(6)  ; #dasmOpCodes(S)
    rule #dasmOpCode("96", S) => SWAP(7)  ; #dasmOpCodes(S)
    rule #dasmOpCode("97", S) => SWAP(8)  ; #dasmOpCodes(S)
    rule #dasmOpCode("98", S) => SWAP(9)  ; #dasmOpCodes(S)
    rule #dasmOpCode("99", S) => SWAP(10) ; #dasmOpCodes(S)
    rule #dasmOpCode("9a", S) => SWAP(11) ; #dasmOpCodes(S)
    rule #dasmOpCode("9b", S) => SWAP(12) ; #dasmOpCodes(S)
    rule #dasmOpCode("9c", S) => SWAP(13) ; #dasmOpCodes(S)
    rule #dasmOpCode("9d", S) => SWAP(14) ; #dasmOpCodes(S)
    rule #dasmOpCode("9e", S) => SWAP(15) ; #dasmOpCodes(S)
    rule #dasmOpCode("9f", S) => SWAP(16) ; #dasmOpCodes(S)
    rule #dasmOpCode("a0", S) => #dasmLOG(0, S)
    rule #dasmOpCode("a1", S) => #dasmLOG(1, S)
    rule #dasmOpCode("a2", S) => #dasmLOG(2, S)
    rule #dasmOpCode("a3", S) => #dasmLOG(3, S)
    rule #dasmOpCode("a4", S) => #dasmLOG(4, S)
    rule #dasmOpCode("f0", S) => CREATE       ; #dasmOpCodes(S)
    rule #dasmOpCode("f1", S) => CALL         ; #dasmOpCodes(S)
    rule #dasmOpCode("f2", S) => CALLCODE     ; #dasmOpCodes(S)
    rule #dasmOpCode("f3", S) => RETURN       ; #dasmOpCodes(S)
    rule #dasmOpCode("f4", S) => DELEGATECALL ; #dasmOpCodes(S)
    rule #dasmOpCode("fe", S) => INVALID      ; #dasmOpCodes(S)
    rule #dasmOpCode("ff", S) => SELFDESTRUCT ; #dasmOpCodes(S)
endmodule
```
