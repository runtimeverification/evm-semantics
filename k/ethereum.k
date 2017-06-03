// Ethereum
// ========

// Ethereum is using the EVM to drive updates over the world state.


requires "evm.k"
requires "evm-dasm.k"
requires "world-state.k"

module ETHEREUM
    imports EVM
    imports WORLD-STATE

    configuration <ethereum>
                    <k> $PGM:EthereumSimulation </k>
                    initEvmCell
                    initWorldStateCell
                  </ethereum>

    syntax AcctID ::= Word
    syntax Code   ::= Map
    syntax MsgID  ::= Word
    syntax Value  ::= Word

    syntax InternalOp ::= "#pushResponse"
 // -------------------------------------
    rule <op> #pushResponse => RESPONSE ~> #push ... </op>
         <control> #response RESPONSE => .Control </control>

    rule <op> COINBASE   => #pushResponse ... </op> <control> .Control => #getGlobal "coinbase"   </control>
    rule <op> TIMESTAMP  => #pushResponse ... </op> <control> .Control => #getGlobal "timestamp"  </control>
    rule <op> NUMBER     => #pushResponse ... </op> <control> .Control => #getGlobal "number"     </control>
    rule <op> DIFFICULTY => #pushResponse ... </op> <control> .Control => #getGlobal "difficulty" </control>
    rule <op> GASLIMIT   => #pushResponse ... </op> <control> .Control => #getGlobal "gaslimit"   </control>

    rule <op> BALANCE ACCT => BAL ~> #push ... </op>
         <account>
           <acctID> ACCT </acctID>
           <balance> BAL </balance>
           ...
         </account>

    rule <op> SLOAD INDEX => #pushResponse ... </op>
         <id> ACCT </id>
         <control> .Control => #getAccountStorage ACCT INDEX </control>

    rule <op> SSTORE INDEX VALUE => . ... </op>
         <id> ACCT </id>
         <control> .Control => #setAccountStorage ACCT INDEX VALUE </control>


// TODO: Calculating gas for `SELFDESTRUCT` needs to take into account the cost of
// creating an account if the recipient address doesn't exist yet. Should it also
// actually create the recipient address if not? Perhaps `#transfer` can take that
// into account automatically for us?


    rule <op> SELFDESTRUCT ACCTTO => . ... </op>
         <id> ACCT </id>
         <selfDestruct> SD </selfDestruct>
         <control> .Control => #transfer ACCT ACCTTO ALL </control>
      requires ACCT in SD

    rule <op> SELFDESTRUCT ACCTTO => . ... </op>
         <id> ACCT </id>
         <selfDestruct> SD => ACCT : SD               </selfDestruct>
         <refund>       RF => RF +Word Rself-destruct </refund>
         <control> .Control => #transfer ACCT ACCTTO ALL </control>
      requires notBool (ACCT in SD)


// Ethereum Simulations
// ====================

// An Ethereum simulation is a list of Ethereum commands.


    syntax EthereumSimulation ::= ".EthereumSimulation"
                                | EthereumCommand EthereumSimulation
 // ----------------------------------------------------------------
    rule .EthereumSimulation => .
    rule ETC:EthereumCommand ETS:EthereumSimulation => ETC ~> ETS


// -   Sort `Account` corresponds to the specification of an account on
//     the network.
// -   Sort `Transaction` corresponds to the specification of a transaction on
//     the network.


    syntax Account ::= "account" ":" "-" "id"      ":" AcctID
                                     "-" "nonce"   ":" Word
                                     "-" "balance" ":" Word
                                     "-" "program" ":" OpCodes
                                     "-" "storage" ":" WordStack
 // ------------------------------------------------------------

    syntax Transaction ::= "transaction" ":" "-" "id"       ":" MsgID
                                             "-" "to"       ":" AcctID
                                             "-" "from"     ":" AcctID
                                             "-" "value"    ":" Word
                                             "-" "data"     ":" Word
                                             "-" "gasPrice" ":" Word
                                             "-" "gasLimit" ":" Word
 // ----------------------------------------------------------------


// -   `clear` clears both the transactions and accounts from the world state.


    syntax EthereumCommand ::= "clear"
 // ----------------------------------
    rule <k> clear => . ... </k>
         <accounts> _ => .Bag </accounts>
         <messages> _ => .Bag </messages>


// -   `load_` loads an account or transaction into the world state.


    syntax EthereumCommand ::= "load" Account | "load" Transaction
 // --------------------------------------------------------------
    rule <k> ( load ( account : - id      : ACCTID
                               - nonce   : NONCE
                               - balance : BAL
                               - program : PGM
                               - storage : STORAGE
                   )
            =>
             .
             )
             ...
         </k>
         <control> .Control => #addAccount ACCTID BAL #asMap(PGM) #asMap(STORAGE) ("nonce" |-> NONCE) </control>

    rule <k> ( load ( transaction : - id       : TXID
                                    - to       : ACCTTO
                                    - from     : ACCTFROM
                                    - value    : VALUE
                                    - data     : DATA
                                    - gasPrice : GPRICE
                                    - gasLimit : GLIMIT
                    )
            =>
             .
             )
             ...
         </k>
         <control> .Control => #addMessage TXID ACCTTO ACCTFROM VALUE ("data" |-> DATA "gasPrice" |-> GPRICE "gasLimit" |-> GLIMIT) </control>


// -   `check_` checks if an account/transaction appears in the world-state
//     as stated.


    syntax EthereumCommand ::= "check" Account | "check" Transaction
 // ----------------------------------------------------------------
    rule <k> ( check ( account : - id      : ACCT
                                 - nonce   : NONCE
                                 - balance : BAL
                                 - program : PGM
                                 - storage : STORAGE
                     )
            => .
             )
             ...
         </k>
         <account>
           <acctID>  ACCT              </acctID>
           <balance> BAL               </balance>
           <code>    CODE              </code>
           <storage> ACCTSTORAGE       </storage>
           <acctMap> "nonce" |-> NONCE </acctMap>
         </account>
      requires #asMap(PGM) ==K CODE andBool #asMap(STORAGE) ==K ACCTSTORAGE

    rule <k> ( check ( transaction : - id       : TXID
                                     - to       : ACCTTO
                                     - from     : ACCTFROM
                                     - value    : VALUE
                                     - data     : DATA
                                     - gasPrice : GPRICE
                                     - gasLimit : GLIMIT
                     )
            =>
             .
             )
             ...
         </k>
         <message>
           <msgID>  TXID     </msgID>
           <to>     ACCTTO   </to>
           <from>   ACCTFROM </from>
           <amount> VALUE    </amount>
           <data>   "data"     |-> DATA
                    "gasPrice" |-> GPRICE
                    "gasLimit" |-> GLIMIT
           </data>
         </message>
endmodule

