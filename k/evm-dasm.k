// EVM Disassembler
// ================

// The default EVM test-set format is JSON, where the data is hex-encoded. A
// dissassembler is provided here for the basic data so that both the JSON and our
// pretty format can be read in.


requires "evm.k"

module EVM-DASM
    imports EVM
    imports STRING

    syntax JSONList ::= List{JSON,","}
    syntax JSON     ::= String
                      | String ":" JSON
                      | "{" JSONList "}"
                      | "[" JSONList "]"
 // ------------------------------------

    syntax Word ::= #parseHexWord ( String ) [function]
 // ---------------------------------------------------
    rule #parseHexWord("")   => 0
    rule #parseHexWord("0x") => 0
    rule #parseHexWord(S)    => String2Base(replaceAll(S, "0x", ""), 16)
      requires (S =/=String "") andBool (S =/=String "0x")

    syntax WordStack ::= #parseHexWords  ( String ) [function]
                       | #parseWordStack ( String ) [function]
 // ----------------------------------------------------------
    rule #parseWordStack(S) => #parseHexWords(replaceAll(S, "0x", ""))
    rule #parseHexWords("") => .WordStack
    rule #parseHexWords(S)  => #parseHexWord(substrString(S, 0, 2)) : #parseHexWords(substrString(S, 2, lengthString(S)))
      requires lengthString(S) >=Int 2

    syntax OpCode ::= #dasmOpCode ( Word ) [function]
 // -------------------------------------------------
    rule #dasmOpCode(   0 ) => STOP
    rule #dasmOpCode(   1 ) => ADD
    rule #dasmOpCode(   2 ) => MUL
    rule #dasmOpCode(   3 ) => SUB
    rule #dasmOpCode(   4 ) => DIV
    rule #dasmOpCode(   5 ) => SDIV
    rule #dasmOpCode(   6 ) => MOD
    rule #dasmOpCode(   7 ) => SMOD
    rule #dasmOpCode(   8 ) => ADDMOD
    rule #dasmOpCode(   9 ) => MULMOD
    rule #dasmOpCode(  10 ) => EXP
    rule #dasmOpCode(  11 ) => SIGNEXTEND
    rule #dasmOpCode(  16 ) => LT
    rule #dasmOpCode(  17 ) => GT
    rule #dasmOpCode(  18 ) => SLT
    rule #dasmOpCode(  19 ) => SGT
    rule #dasmOpCode(  20 ) => EQ
    rule #dasmOpCode(  21 ) => ISZERO
    rule #dasmOpCode(  22 ) => AND
    rule #dasmOpCode(  23 ) => EVMOR
    rule #dasmOpCode(  24 ) => XOR
    rule #dasmOpCode(  25 ) => NOT
    rule #dasmOpCode(  26 ) => BYTE
    rule #dasmOpCode(  32 ) => SHA3
    rule #dasmOpCode(  48 ) => ADDRESS
    rule #dasmOpCode(  49 ) => BALANCE
    rule #dasmOpCode(  50 ) => ORIGIN
    rule #dasmOpCode(  51 ) => CALLER
    rule #dasmOpCode(  52 ) => CALLVALUE
    rule #dasmOpCode(  53 ) => CALLDATALOAD
    rule #dasmOpCode(  54 ) => CALLDATASIZE
    rule #dasmOpCode(  55 ) => CALLDATACOPY
    rule #dasmOpCode(  56 ) => CODESIZE
    rule #dasmOpCode(  57 ) => CODECOPY
    rule #dasmOpCode(  58 ) => GASPRICE
    rule #dasmOpCode(  59 ) => EXTCODESIZE
    rule #dasmOpCode(  60 ) => EXTCODECOPY
    rule #dasmOpCode(  64 ) => BLOCKHASH
    rule #dasmOpCode(  65 ) => COINBASE
    rule #dasmOpCode(  66 ) => TIMESTAMP
    rule #dasmOpCode(  67 ) => NUMBER
    rule #dasmOpCode(  68 ) => DIFFICULTY
    rule #dasmOpCode(  69 ) => GASLIMIT
    rule #dasmOpCode(  80 ) => POP
    rule #dasmOpCode(  81 ) => MLOAD
    rule #dasmOpCode(  82 ) => MSTORE
    rule #dasmOpCode(  83 ) => MSTORE8
    rule #dasmOpCode(  84 ) => SLOAD
    rule #dasmOpCode(  85 ) => SSTORE
    rule #dasmOpCode(  86 ) => JUMP
    rule #dasmOpCode(  87 ) => JUMPI
    rule #dasmOpCode(  88 ) => PC
    rule #dasmOpCode(  89 ) => MSIZE
    rule #dasmOpCode(  90 ) => GAS
    rule #dasmOpCode(  91 ) => JUMPDEST
    rule #dasmOpCode( 240 ) => CREATE
    rule #dasmOpCode( 241 ) => CALL
    rule #dasmOpCode( 242 ) => CALLCODE
    rule #dasmOpCode( 243 ) => RETURN
    rule #dasmOpCode( 244 ) => DELEGATECALL
    rule #dasmOpCode( 254 ) => INVALID
    rule #dasmOpCode( 255 ) => SELFDESTRUCT

    syntax OpCodes ::= #dasmPUSH ( Word , WordStack ) [function]
                     | #dasmLOG  ( Word , WordStack ) [function]
    syntax Word ::= #pushArg ( WordStack ) [function]
 // -------------------------------------------------
    rule #dasmPUSH( W , WS ) => PUSH(#pushArg(#take(W, WS))) ; #dasmOpCodes(#drop(W, WS))

    syntax OpCodes ::= #dasmOpCodes ( WordStack ) [function]
 // --------------------------------------------------------
    rule #dasmOpCodes( .WordStack ) => .OpCodes
    rule #dasmOpCodes( W : WS )     => #dasmOpCode(W)    ; #dasmOpCodes(WS) requires (W >=Word 0   ==K bool2Word(true)) andBool (W <=Word 95  ==K bool2Word(true))
    rule #dasmOpCodes( W : WS )     => #dasmOpCode(W)    ; #dasmOpCodes(WS) requires (W >=Word 240 ==K bool2Word(true)) andBool (W <=Word 255 ==K bool2Word(true))
    rule #dasmOpCodes( W : WS )     => DUP( W -Word 127) ; #dasmOpCodes(WS) requires (W >=Word 128 ==K bool2Word(true)) andBool (W <=Word 143 ==K bool2Word(true))
    rule #dasmOpCodes( W : WS )     => SWAP(W -Word 143) ; #dasmOpCodes(WS) requires (W >=Word 144 ==K bool2Word(true)) andBool (W <=Word 159 ==K bool2Word(true))
    rule #dasmOpCodes( W : WS )     => #dasmLOG( W -Word 160 , WS )         requires (W >=Word 160 ==K bool2Word(true)) andBool (W <=Word 164 ==K bool2Word(true))
    rule #dasmOpCodes( W : WS )     => #dasmPUSH( W -Word 95 , WS )         requires (W >=Word 96  ==K bool2Word(true)) andBool (W <=Word 127 ==K bool2Word(true))
endmodule

