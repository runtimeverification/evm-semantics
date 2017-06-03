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

    syntax InternalOp ::= "#pushResponse"
 // -------------------------------------
    rule <op> #pushResponse => RESPONSE ~> #push ... </op>
         <control> #response RESPONSE => . </control>

    rule <op> SLOAD INDEX => #pushResponse ... </op>
         <id> ACCT </id>
         <control> . => #getAccountStorage ACCT INDEX </control>

    rule <op> SSTORE INDEX VALUE => . ... </op>
         <id> ACCT </id>
         <control> . => #setAccountStorage ACCT INDEX VALUE </control>


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


// -   `load_` is used to load an account or transaction into the world state.


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


// -   `check_` is used to check if an account/transaction appears in the
//     world-state as stated.


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

