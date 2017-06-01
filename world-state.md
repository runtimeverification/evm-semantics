World State
===========

We need a way to specify the current world state. It will be a list of accounts
and a list of pending transactions. This world state should not depend on
specifics of the EVM at all, instead it should be a distributed ledger of
accounts with the associated balances, code, and storage.

Configuration
-------------

-   `worldState` is the top-level cell. Import this sub-configuration into
    whatever language will operate over this world-state.

-   `global` is for storing "global" (non-account-specific) world-state for EVM.

-   `accounts` stores the list of accounts as a map from the account ID to each
    of the fields in the account (`nonce`, `balance`, `code`, and `storage`).

-   `messages` stores the list of pending message calls on the network. The
    field `data` stores information about the transaction separate from the
    amount to transfer.

Note that this model of world-state is pretty much just the Actor/Agent model of
computation with distributed entities (each of the accounts) communicating
through asynchronous message passing (the transactions). Anything that depends
on the `global` cell is a synchronization constraint, which means that the whole
network must reach a consensus before a read/write to that cell.

```k
module WORLD-STATE
    configuration <worldState>

                    <control> .Control </control>
                    <global> .Map </global>

                    <accounts>
                      <account multiplicity="*">
                        <acctID>  .AcctID  </acctID>
                        <balance> 0        </balance>
                        <code>    .Code    </code>
                        <storage> .Map     </storage>
                        <acctMap> .Map     </acctMap>
                      </account>
                    </accounts>

                    <messages>
                      <message multiplicity="*">
                        <msgID>  .MsgID   </msgID>
                        <to>     .AcctID  </to>
                        <from>   .AcctID  </from>
                        <amount> 0        </amount>
                        <data>   .Map     </data>
                      </message>
                    </messages>

                  </worldState>
```

Here the "null" values of each of the abstract sorts used in the configuration
are provided here.

```k
    syntax Control ::= ".Control"
    syntax AcctID  ::= ".AcctID"
    syntax Code    ::= ".Code"
    syntax MsgID   ::= ".MsgID"
```

TODO: I would prefer to state instead "`Balance` behaves like an abelian group
with order" instead of pinning it to `Int`. This isn't such a big deal, but
would make this presentation more abstract. The machinery for developing a group
with order is too cumbersome/verbose without proper AC matching.

Primitives
----------

The world state exports certain primitives (for driving updates to the state).
Primitives should be added to the `Control` sort and when placed in the
`control` cell will have their affect on the state.

Certain actions on the world state elicit responses, thes responses will be
placed in the `#response_` wrapper on the world state cell.

```k
    syntax Control ::= "#response" K
```

### Global Actions

-   `#setGlobal__` will update the global map with the given key/value pair.
-   `#getGlobal_` will retrieve the value associated to the supplied key from
    the global state map.

```k
    syntax Control ::= "#setGlobal" K K
                     | "#getGlobal" K
 // ---------------------------------
    rule <control> #setGlobal INDEX VALUE => .Control </control>
         <global> GLOBAL => GLOBAL [ INDEX <- VALUE ] </global>

    rule <control> #getGlobal INDEX => #response VALUE </control>
         <global> ... INDEX |-> VALUE ... </global>
```

### State Setup

-   `#addAccount_____` adds an account to the network with the given data.
-   `#addMessage_____` adds a message to the pool of pending messages.

TODO: `#addAccount_____` does *not* check that the account doesn't already
exist, which it really should.

```k
    syntax Control ::= "#addAccount" AcctID Int Code Map Map
                     | "#addMessage" MsgID AcctID AcctID Int Map
 // ------------------------------------------------------------
    rule <control> #addAccount ACCTID BAL CODE STORAGE ACCTMAP => .Control </control>
         <accounts>
            ( .Bag
           => <account>
                <acctID>  ACCTID  </acctID>
                <balance> BAL     </balance>
                <code>    CODE    </code>
                <storage> STORAGE </storage>
                <acctMap> ACCTMAP </acctMap>
              </account>
            )
            ...
         </accounts>
      requires BAL >=Int 0

    rule <control> #addMessage MSGID ACCTTO ACCTFROM AMT DATA => .Control </control>
         <messages>
            ( .Bag
           => <message>
                <msgID>  MSGID    </msgID>
                <to>     ACCTTO   </to>
                <from>   ACCTFROM </from>
                <amount> AMT      </amount>
                <data>   DATA     </data>
              </message>
            )
            ...
         </messages>
```

### Account Actions

-   `#transfer___` can be used to transfer some ammount from one account
    to another. It will check that the accounts exist and that the sending
    account has enough to perform the send. If the sending account is set to
    `.AcctID`, it treats the transfer like it is being minted (to be used for
    things like rewarding miners).

```k
    syntax Control ::= "#transfer" AcctID AcctID Int
 // ------------------------------------------------
    rule <control> #transfer ACCTFROM ACCTTO AMT => .Control </control>
         <account>
           <acctID> ACCTFROM </acctID>
           <balance> BALFROM => BALFROM -Int AMT </balance>
           ...
         </account>
         <account>
           <acctID> ACCTTO </acctID>
           <balance> BALTO => BALTO +Int AMT </balance>
           ...
         </account>
      requires BALFROM >Int AMT

    rule <control> #transfer .AcctID ACCTTO AMT => .Control </control>
         <account>
           <acctID> ACCTTO </acctID>
           <balance> BALTO => BALTO +Int AMT </balance>
           ...
         </account>
```

-   `#setAccountStorage___` updates the map which holds the storage of
    the account.
-   `#getAccountStorage__` retrieves a value from the storage of a
    specified account.

```k
    syntax Control ::= "#setAccountStorage" AcctID K K
                     | "#getAccountStorage" AcctID K
 // ------------------------------------------------
    rule <control> #setAccountStorage ACCT INDEX VALUE => .Control </control>
         <account>
           <acctID> ACCT </acctID>
           <storage> STORAGE => STORAGE [ INDEX <- VALUE ] </storage>
           ...
         </account>

    rule <control> #getAccountStorage ACCT INDEX => #response VALUE </control>
         <account>
           <acctID> ACCT </acctID>
           <storage> ... INDEX |-> VALUE ... </storage>
           ...
         </account>
endmodule
```
