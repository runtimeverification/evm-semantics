// EVM World State
// ===============

// We need a way to specify the current world state. It will be a list of accounts
// and a list of pending transactions. This can come in either the pretty K format,
// or in the default EVM test-set format.

// First, we build a JSON parser, then we provide some standard "parsers" which
// will be used to convert the JSON formatted input into the prettier K format.


requires "data.k"

module EVM-WORLD-STATE
    imports EVM-DASM

    configuration <worldState>
                    <accounts>
                        <account multiplicity="*">
                            <acctID> .AcctID </acctID>
                            <nonce> 0:Word </nonce>
                            <balance> 0:Word </balance>
                            <program> .Map </program>
                            <storage> .Map </storage>
                        </account>
                    </accounts>
                  </worldState>

    syntax AcctID  ::= Word | ".AcctID"
 // -----------------------------------

    syntax Program ::= OpCodes | Map
                     | #program ( Program ) [function]
                     | #dasmEVM ( JSON )    [function]
 // --------------------------------------------------
    rule #program( OCM:Map )     => OCM
    rule #program( OCS:OpCodes ) => #asMap(OCS)
    rule #dasmEVM( S:String )    => #program(#dasmOpCodes(replaceAll(S, "0x", "")))

    syntax Storage ::= WordMap | WordStack
                     | #storage ( Storage ) [function]
 // --------------------------------------------------
    rule #storage( WM:Map )       => WM
    rule #storage( WS:WordStack ) => #asMap(WS)

    syntax Map ::= #parseStorage ( JSON ) [function]
 // ------------------------------------------------
    rule #parseStorage( { .JSONList } )                   => .Map
    rule #parseStorage( { KEY : (VALUE:String) , REST } ) => (#parseHexWord(KEY) |-> #parseHexWord(VALUE)) #parseStorage({ REST })


// Here is the data of an account on the network. It has an id, a balance, a
// program, and storage. Additionally, the translation from the JSON account format
// to the K format is provided.


    syntax Account ::= JSON
                     | "account" ":" "-" "id"      ":" AcctID
                                     "-" "nonce"   ":" Word
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
                   - nonce   : #parseHexWord(NONCE)
                   - balance : #parseHexWord(BAL)
                   - program : #dasmEVM(CODE)
                   - storage : #parseStorage(STORAGE)


// Here is the data of a transaction on the network. It has fields for who it's
// directed toward, the data, the value transfered, and the gas-price/gas-limit.
// Similarly, a conversion from the JSON format to the pretty K format is provided.


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


// Finally, we have the syntax of an `EVMSimulation`, which consists of a list of
// accounts followed by a list of transactions.


    syntax Accounts ::= ".Accounts"
                      | Account Accounts
 // ------------------------------------
    rule .Accounts => .
    rule ACCT:Account ACCTS:Accounts => ACCT ~> ACCTS

    syntax Transactions ::= ".Transactions"
                          | Transaction Transactions
 // ------------------------------------------------
    rule .Transactions => .
    rule TX:Transaction TXS:Transactions => TX ~> TXS

    syntax EVMSimulation ::= Accounts Transactions
 // ----------------------------------------------
    rule ACCTS:Accounts TXS:Transactions => ACCTS ~> TXS

    syntax Process ::= "{" AcctID "|" Word "|" Word "|" WordStack "|" WordMap "}"
    syntax CallStack ::= ".CallStack"
                       | Process CallStack
endmodule


// EVM Disassembler
// ================

// The default EVM test-set format is JSON, where the data is hex-encoded. A
// dissassembler is provided here for the basic data so that both the JSON and our
// pretty format can be read in.


module EVM-DASM
    imports EVM-OPCODE
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

    syntax OpCodes ::= #dasmOpCodes ( String ) [function]
 // -----------------------------------------------------
    rule #dasmOpCodes( "" ) => .OpCodes
    rule #dasmOpCodes( S )  => #dasmOpCode(substrString(S, 0, 2), substrString(S, 2, lengthString(S)))
      requires lengthString(S) >=Int 2

    syntax OpCodes ::= #dasmPUSH ( Word , String ) [function]
 // ---------------------------------------------------------
    rule #dasmPUSH(N, S) => PUSH(#parseHexWord(substrString(S, 0, N *Int 2))) ; #dasmOpCodes(substrString(S, N *Int 2, lengthString(S)))
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

