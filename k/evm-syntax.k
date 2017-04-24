// Local Execution State
// =====================

// EVM execution maintains some local state (like a word stack, local memory,
// program counter, etc...). We need to specify the syntax of all this local state
// for storage.


requires "evm-data.k"


// EVM Gas Cost
// ------------

// Here we define the gas-cost of each instruction in the instruction set. Many of
// the instructions gas cost is fixed and not dependent on any parts of the
// configuration; for those that do have some dependence, their associated cost
// must be defined after the configuration is defined.


module EVM-GAS
    imports EVM-OPCODE

    syntax Word ::= #gas ( OpCode )    [function]

    syntax Word ::= "Gzero" | "Gbase" | "Gverylow" | "Glow" | "Gmid" | "Ghigh" | "Gextcode"
                  | "Gbalance" | "Gsload" | "Gjumpdest" | "Gsset" | "Gsreset" | "Rsclear"
                  | "Rself-destruct" | "Gself-destruct" | "Gcreate" | "Gcodedeposit" | "Gcall"
                  | "Gcallvalue" | "Gcallstipend" | "Gnewaccount" | "Gexp" | "Gexpbyte"
                  | "Gmemory" | "Gtxcreate" | "Gtxdatazero" | "Gtxdatanonzero" | "Gtransaction"
                  | "Glog" | "Glogdata" | "Glogtopic" | "Gsha3" | "Gsha3word" | "Gcopy" | "Gblockhash"
                  | "#gasSSTORE" | "#gasCALL" | "#gasSELFDESTRUCT"
 // --------------------------------------------------------------
    rule Gzero          => 0     [macro]
    rule Gbase          => 2     [macro]
    rule Gverylow       => 3     [macro]
    rule Glow           => 5     [macro]
    rule Gmid           => 8     [macro]
    rule Ghigh          => 10    [macro]
    rule Gextcode       => 700   [macro]
    rule Gbalance       => 400   [macro]
    rule Gsload         => 200   [macro]
    rule Gjumpdest      => 1     [macro]
    rule Gsset          => 20000 [macro]
    rule Gsreset        => 5000  [macro]
    rule Rsclear        => 15000 [macro]
    rule Rself-destruct => 24000 [macro]
    rule Gself-destruct => 5000  [macro]
    rule Gcreate        => 32000 [macro]
    rule Gcodedeposit   => 200   [macro]
    rule Gcall          => 700   [macro]
    rule Gcallvalue     => 9000  [macro]
    rule Gcallstipend   => 2300  [macro]
    rule Gnewaccount    => 25000 [macro]
    rule Gexp           => 10    [macro]
    rule Gexpbyte       => 10    [macro]
    rule Gmemory        => 3     [macro]
    rule Gtxcreate      => 32000 [macro]
    rule Gtxdatazero    => 4     [macro]
    rule Gtxdatanonzero => 68    [macro]
    rule Gtransaction   => 21000 [macro]
    rule Glog           => 375   [macro]
    rule Glogdata       => 8     [macro]
    rule Glogtopic      => 375   [macro]
    rule Gsha3          => 30    [macro]
    rule Gsha3word      => 6     [macro]
    rule Gcopy          => 3     [macro]
    rule Gblockhash     => 20    [macro]

    syntax OpCodes ::= "Wzero" | "Wbase" | "Wverylow" | "Wlow" | "Wmid" | "Whigh" | "Wextcode" | "Wcopy" | "Wcall"
 // --------------------------------------------------------------------------------------------------------------
    rule Wzero => STOP ; RETURN ; .OpCodes
    rule Wbase =>   ADDRESS ; ORIGIN ; CALLER ; CALLVALUE ; CALLDATASIZE
                  ; CODESIZE ; GASPRICE ; COINBASE ; TIMESTAMP ; NUMBER
                  ; DIFFICULTY ; GASLIMIT ; POP ; PC ; MSIZE ; GAS ; .OpCodes
    rule Wverylow =>  ADD ; SUB ; NOT ; LT ; GT ; SLT ; SGT ; EQ ; ISZERO ; AND
                    ; EVMOR ; XOR ; BYTE ; CALLDATALOAD ; MLOAD ; MSTORE ; MSTORE8
                    ; PUSH [ 0 ] 0 ; DUP [ 0 ] ; SWAP [ 0 ] ; .OpCodes
    rule Wlow => MUL ; DIV ; SDIV ; MOD ; SMOD ; SIGNEXTEND ; .OpCodes
    rule Wmid => ADDMOD ; MULMOD ; JUMP ; JUMPI; .OpCodes
    rule Wextcode => EXTCODESIZE ; .OpCodes
    rule Wcopy => CALLDATACOPY ; CODECOPY ; .OpCodes
    rule Wcall => CALL ; CALLCODE ; DELEGATECALL ; .OpCodes

    rule #gas(SSTORE)       => #gasSSTORE                                           // INCORRECT
    rule #gas(EXP)          => Gexp                                                 // INCORRECT
    rule #gas(OP)           => Gverylow +Word Gcopy          requires OP in Wcopy   // INCORRECT
    rule #gas(EXTCODECOPY)  => Gextcode +Word Gcopy                                 // INCORRECT
    rule #gas(LOG [ N ])    => Glog +Word (N *Word Glogdata)                        // INCORRECT
    rule #gas(OP)           => #gasCALL                      requires OP in Wcall   // INCORRECT
    rule #gas(SELFDESTRUCT) => #gasSELFDESTRUCT                                     // INCORRECT
    rule #gas(CREATE)       => Gcreate
    rule #gas(SHA3)         => Gsha3                                                // INCORRECT
    rule #gas(JUMPDEST)     => Gjumpdest
    rule #gas(SLOAD)        => Gsload
    rule #gas(OP)           => Gzero                         requires OP in Wzero
    rule #gas(OP)           => Gbase                         requires OP in Wbase
    rule #gas(OP)           => Gverylow                      requires OP in Wverylow
    rule #gas(OP)           => Glow                          requires OP in Wlow
    rule #gas(OP)           => Gmid                          requires OP in Wmid
    rule #gas(OP)           => Ghigh                         requires OP in Whigh
    rule #gas(OP)           => Gextcode                      requires OP in Wextcode
    rule #gas(BALANCE)      => Gbalance
    rule #gas(BLOCKHASH)    => Gblockhash
endmodule


// EVM Simulation
// --------------

// We need a way to specify the current world state. It will be a list of accounts
// and a list of pending transactions. This can come in either the pretty K format,
// or in the default EVM test-set format.

// First, we build a JSON parser, then we provide some standard "parsers" which
// will be used to convert the JSON formatted input into the prettier K format.


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


    syntax AcctID  ::= Word | ".AcctID"
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
      [structural]


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
      [structural]


// Finally, we have the syntax of an `EVMSimulation`, which consists of a list of
// accounts followed by a list of transactions.


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

