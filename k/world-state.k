// EVM World State
// ===============

// We need a way to specify the current world state. It will be a list of accounts
// and a list of pending transactions. This can come in either the pretty K format,
// or in the default EVM test-set format.

// First, we build a JSON parser, then we provide some standard "parsers" which
// will be used to convert the JSON formatted input into the prettier K format.


requires "opcodes.k"

module EVM-WORLD-STATE
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

