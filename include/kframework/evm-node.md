EVM Integration with Production Client
======================================

Contained in this file is glue code needed in order to enable the ability to use KEVM as a VM for an actual Ethereum node.

```{.k .node}
requires "evm.md"
requires "optimizations.md"

module EVM-NODE
    imports EVM
    imports EVM-OPTIMIZATIONS
    imports K-REFLECTION
    imports COLLECTIONS
    imports BYTES

  configuration
    <kevm/>
    <loaded> false </loaded>
```

### State loading operations.

In order to enable scalable execution of transactions on an entire blockchain, it is necessary to avoid serializing/deserializing the entire state of all accounts when constructing the initial configuration for KEVM.
To do this, we assume that accounts not present in the `<accounts>` cell might not exist and need to be loaded on each access.
We also defer loading of storage entries and the actual code byte string until it is needed.
Because the same account may be loaded more than once, implementations of this interface are expected to cache the actual query to the Ethereum client.

-   `#unloaded` represents the code of an account that has not had its code loaded yet. Unloaded code may not be empty.
-   Empty code is detected without lazy evaluation by means of checking the code hash, and therefore will always be represented in the `<code>` cell as `.WordStack`.

```{.k .node}
    syntax InternalOp ::= "#load" "[" OpCode "]"
 // --------------------------------------------
    rule <k> (. => #load [ OP ]) ~> #next [ OP ] ... </k>
         <loaded> false => true </loaded>
      [priority(35)]

    rule <k> #execute ... </k>
         <loaded> true => false </loaded>
      [priority(35)]
```

-   `CREATE2` is a special case
Note that we cannot execute #loadAccount during the #load phase earlier because gas will not yet
have been paid, and it may be to expensive to compute the hash of the init code.

```{.k .node}
    rule <k> #gas [ CREATE2, _ ] ... </k>
         <loaded> true => false </loaded>
      [priority(35)]

    rule <k> (. => #loadAccount #newAddr(ACCT, SALT, #range(LM, MEMSTART, MEMWIDTH)))
          ~> CREATE2 _VALUE MEMSTART MEMWIDTH SALT
         ...
         </k>
         <id> ACCT </id>
         <localMem> LM </localMem>
         <loaded> false => true </loaded>
      [priority(35)]
```

```{.k .node}
    rule <k> #load [ OP:OpCode ] => #loadAccount W0 ~> #lookupCode W0 ... </k>
         <wordStack> W0 : _ </wordStack>
      requires isAddr1Op(OP)

    rule <k> #load [ OP:OpCode ] => #loadAccount W1 ~> #lookupCode W1 ... </k>
         <wordStack> _ : W1 : _ </wordStack>
      requires isAddr2Op(OP)

    rule <k> #load [ CREATE ] => #loadAccount #newAddr(ACCT, NONCE) ... </k>
         <id> ACCT </id>
         <account>
           <acctID> ACCT </acctID>
           <nonce> NONCE </nonce>
           ...
         </account>

    rule <k> #load [ OP:OpCode ] => #lookupStorage ACCT W0 ... </k>
         <id> ACCT </id>
         <wordStack> W0 : _ </wordStack>
      requires OP ==K SSTORE orBool OP ==K SLOAD

    rule <k> #load [ _OP:OpCode ] => . ... </k> [owise]
```

```{.k .node}
    syntax AccountCode ::= #unloaded(Int)
```

-   `#getBalance` returns the balance of an account that exists based on its integer address.
-   `#getNonce` returns the nonce of an account that exists based on its integer address.
-   `#isCodeEmpty` returns true if the code hash of the account is equal to the hash of the empty string, and false otherwise.
-   `#accountExists` returns true if the account is present in the state trie for the current block, and false otherwise.

```{.k .node}
    syntax Int  ::= #getBalance  ( Int ) [function, hook(BLOCKCHAIN.getBalance)]
                  | #getNonce    ( Int ) [function, hook(BLOCKCHAIN.getNonce)]
                  | #getCodeHash ( Int ) [function]
 // -----------------------------------------------------------------------------
    rule #getCodeHash(ACCT) => keccak(#parseByteStackRaw(#getCode(ACCT)))

    syntax Bool ::= #isCodeEmpty   ( Int ) [function, hook(BLOCKCHAIN.isCodeEmpty)]
                  | #accountExists ( Int ) [function, hook(BLOCKCHAIN.accountExists)]
 // ---------------------------------------------------------------------------------
```

The following operations help with loading account information from an external running client.
This minimizes the amount of information which must be stored in the configuration.

-   `#loadAccount` queries for account data from the running client.
-   `#lookupCode` loads the code of an account into the `<code>` cell.
-   `#lookupStorage` loads the value of the specified storage key into the `<storage>` cell.

```k
    syntax InternalOp ::= "#loadAccount"   Int
                        | "#lookupCode"    Int
                        | "#lookupStorage" Int Int
 // ----------------------------------------------
```

-   `#loadAccount` loads an account's balance and nonce if it exists, and leaves the code and storage unloaded, except if the code is empty, in which case the code is fully loaded.
    If the account does not exist, it does nothing.

```{.k .node}
    rule <k> #loadAccount ACCT => . ... </k> <account> <acctID> ACCT </acctID> ... </account>

    rule <k> #loadAccount ACCT => . ... </k>
      requires notBool #accountExists(ACCT)
      [priority(55)]

    rule <k> #loadAccount ACCT => . ... </k>
         <accounts>
           ( .Bag
          => <account>
               <acctID> ACCT </acctID>
               <balance> #getBalance(ACCT) </balance>
               <code> #if #isCodeEmpty(ACCT) #then .Bytes #else #unloaded(#getCodeHash(ACCT)) #fi </code>
               <storage> .Map </storage>
               <origStorage> .Map </origStorage>
               <nonce> #getNonce(ACCT) </nonce>
             </account>
           )
           ...
         </accounts> [owise]
```

-   `#getStorageData` loads the value for a single storage key of a specified account by its address and storage offset.
    If the storage key has already been loaded or the account does not exist, it does nothing.

```{.k .node}
    syntax Int ::= #getStorageData ( Int , Int ) [function, hook(BLOCKCHAIN.getStorageData)]
 // ----------------------------------------------------------------------------------------
    rule <k> #lookupStorage ACCT INDEX => . ... </k>
         <account>
           <acctID>  ACCT                                                         </acctID>
           <storage> STORAGE => STORAGE [ INDEX <- #getStorageData(ACCT, INDEX) ] </storage>
           <origStorage> ORIGSTORAGE => ORIGSTORAGE [ INDEX <- #getStorageData(ACCT, INDEX) ] </origStorage>
           ...
         </account>
      requires notBool INDEX in_keys(STORAGE)

    rule <k> #lookupStorage ACCT INDEX => . ... </k>
         <account>
           <acctID> ACCT </acctID>
           <storage> STORAGE:Map </storage>
           ...
         </account>
      requires INDEX in_keys(STORAGE)

    rule <k> #lookupStorage ACCT _ => . ... </k>
      requires notBool #accountExists(ACCT)
```

-   `#getCode` loads the code for a specified account by its address. If the code has already been loaded, it does nothing.
    If the account does not exist, it also does nothing.

```{.k .node}
    syntax String ::= #getCode ( Int ) [function, hook(BLOCKCHAIN.getCode)]
 // -----------------------------------------------------------------------
    rule <k> #lookupCode ACCT => . ... </k>
         <account>
           <acctID> ACCT </acctID>
           <code> #unloaded(_) => #parseByteStackRaw(#getCode(ACCT)) </code>
           ...
         </account>

    rule <k> #lookupCode ACCT => . ... </k>
         <account>
           <acctID> ACCT </acctID>
           <code> _:Bytes </code>
           ...
         </account>

    rule <k> #lookupCode ACCT => . ... </k>
      requires notBool #accountExists(ACCT)
```

-   `#getBlockhash(N)` returns the blockhash of the Nth most recent block, up to a maximum of 256 blocks.
    It is used in the implementation of the BLOCKHASH instruction as seen below.

```{.k .node}
    syntax Int ::= #getBlockhash ( Int ) [function, hook(BLOCKCHAIN.getBlockhash)]
 // ------------------------------------------------------------------------------
    rule <k> BLOCKHASH N => #getBlockhash(N) ~> #push ... </k> <mode> NORMAL </mode> requires N >=Int 0 andBool N  <Int 256
    rule <k> BLOCKHASH N => 0                ~> #push ... </k> <mode> NORMAL </mode> requires N  <Int 0  orBool N >=Int 256
```

```{.k .node}
    rule keccak({#unloaded(HASH)}:>Bytes) => HASH [concrete]
```

### Transaction Execution

-   `runVM` takes all the input state of a transaction and the current block header and executes the transaction according to the specified state, relying on the above loading operations for access to accounts and block hashes.
    The signature of this function must match the signature expected by VM.ml in the blockchain-k-plugin.

```{.k .node}
    syntax EthereumSimulation ::= runVM ( iscreate: Bool , to: Int          , from: Int       , code: String  , args: String  , value: Int     , gasprice: Int
                                        , gas: Int       , beneficiary: Int , difficulty: Int , number: Int   , gaslimit: Int , timestamp: Int , unused: String ) [symbol]
 // ----------------------------------------------------------------------------------------------------------------------------------------------------------------------
    rule <k> (.K => #loadAccount ACCTFROM) ~> runVM(... from: ACCTFROM) ... </k>
         <accounts> .Bag </accounts>

    rule <k> runVM(true, _, ACCTFROM, _, ARGS, VALUE, GPRICE, GAVAIL, CB, DIFF, NUMB, GLIMIT, TS, _)
          => #loadAccount #newAddr(ACCTFROM, NONCE -Int 1)
          ~> #create ACCTFROM #newAddr(ACCTFROM, NONCE -Int 1) VALUE #parseByteStackRaw(ARGS)
          ~> #codeDeposit #newAddr(ACCTFROM, NONCE -Int 1)
          ~> #endCreate
         ...
         </k>
         <gasPrice> _ => GPRICE </gasPrice>
         <callGas> _ => GAVAIL </callGas>
         <origin> _ => ACCTFROM </origin>
         <callDepth> _ => -1 </callDepth>
         <coinbase> _ => CB </coinbase>
         <difficulty> _ => DIFF </difficulty>
         <number> _ => NUMB </number>
         <gasLimit> _ => GLIMIT </gasLimit>
         <timestamp> _ => TS </timestamp>
         <account>
           <acctID> ACCTFROM </acctID>
           <nonce> NONCE </nonce>
           ...
         </account>
         <touchedAccounts> _ => SetItem(CB) </touchedAccounts>
         <accessedAccounts> ACCESSED => ACCESSED |Set SetItem(ACCTFROM) |Set SetItem(#newAddr(ACCTFROM, NONCE -Int 1)) </accessedAccounts>

    rule <k> runVM(false, ACCTTO, ACCTFROM, _, ARGS, VALUE, GPRICE, GAVAIL, CB, DIFF, NUMB, GLIMIT, TS, _)
          => #loadAccount ACCTTO
          ~> #lookupCode ACCTTO
          ~> #call ACCTFROM ACCTTO ACCTTO VALUE VALUE #parseByteStackRaw(ARGS) false
          ~> #endVM
         ...
         </k>
         <gasPrice> _ => GPRICE </gasPrice>
         <callGas> _ => GAVAIL </callGas>
         <origin> _ => ACCTFROM </origin>
         <callDepth> _ => -1 </callDepth>
         <coinbase> _ => CB </coinbase>
         <difficulty> _ => DIFF </difficulty>
         <number> _ => NUMB </number>
         <gasLimit> _ => GLIMIT </gasLimit>
         <timestamp> _ => TS </timestamp>
         <touchedAccounts> _ => SetItem(CB) </touchedAccounts>
         <accessedAccounts> ACCESSED => ACCESSED |Set SetItem(ACCTFROM) |Set SetItem(ACCTTO) </accessedAccounts>
         <account> <acctID> ACCTFROM </acctID> ... </account>
```

-   `makeAccessList` will initialize the `<accessedAccounts>` and `<accessedStorage>` cells for an access list transaction type and leave runVM at the top of the `<k>` cell.

```{.k .node}
    syntax KItem ::= storageLocation ( Int, Int ) [symbol]
    syntax EthereumSimulation ::= makeAccessList ( accessedAddresses: Set, storageList: Set , runvm: EthereumSimulation ) [symbol]
 // ------------------------------------------------------------------------------------------------------------------------------
    rule <k> makeAccessList( ACCESSED, .Set, RUNVM ) => RUNVM ... </k>
         <accessedAccounts> _ => ACCESSED </accessedAccounts>

    rule <k> makeAccessList( _, SetItem(storageLocation(ACCT, LOCATION)) STORAGELIST => STORAGELIST, _ ) ... </k>
         <accessedStorage> ... ACCT |-> (LOCATIONS => LOCATIONS |Set SetItem(LOCATION)) ... </accessedStorage>

    rule <k> makeAccessList( _, SetItem(storageLocation(ACCT, LOCATION)) STORAGELIST => STORAGELIST, _ ) ... </k>
         <accessedStorage> STORAGEMAP => STORAGEMAP[ACCT <- SetItem(LOCATION)] </accessedStorage>
      requires notBool ACCT in_keys(STORAGEMAP)
```

-   `#endCreate` and `#endVM` clean up after the transaction finishes and store the return status code of the top level call frame on the top of the `<k>` cell.

```{.k .node}
    syntax KItem ::= "#endVM" | "#endCreate"
 // ----------------------------------------
    rule <statusCode> _:ExceptionalStatusCode </statusCode>
         <k> #halt ~> #endVM => #popCallStack ~> #popWorldState ~> 0 </k>
         <output> _ => .Bytes </output>

    rule <statusCode> EVMC_REVERT </statusCode>
         <k> #halt ~> #endVM => #popCallStack ~> #popWorldState ~> #refund GAVAIL ~> 0 </k>
         <gas> GAVAIL </gas>

    rule <statusCode> EVMC_SUCCESS </statusCode>
         <k> #halt ~> #endVM => #popCallStack ~> #dropWorldState ~> #refund GAVAIL ~> 1 </k>
         <gas> GAVAIL </gas>

    rule <k> #endCreate => W ... </k> <wordStack> W : _WS </wordStack>
```

### Primitive operations expected to exist by the blockchain-k-plugin

-   `vmResult` represents the extracted information about the world state after the transaction finishes.
    Its signature must match the signature expected by VM.ml in the blockchain-k-plugin.
-   `extractConfig` takes a final configuration after rewriting and extracts a `vmResult` from it in order to abstract away configuration structure from the postprocessing done by the blockchain-k-plugin.

```{.k .node}
    syntax KItem ::= vmResult ( return: String , gas: Int , refund: Int , status: Int , selfdestruct: Set , logs: List , AccountsCell , touched: Set , statusCode: String )
    syntax KItem ::= extractConfig() [function, symbol]
 // ---------------------------------------------------
    rule [[ extractConfig() => vmResult(#unparseByteStack(OUT), GAVAIL, REFUND, STATUS, SD, LOGS, <accounts> ACCTS </accounts>, TOUCHED, StatusCode2String(STATUSCODE)) ]]
         <output> OUT </output>
         <gas> GAVAIL </gas>
         <refund> REFUND </refund>
         <k> STATUS:Int </k>
         <selfDestruct> SD </selfDestruct>
         <log> LOGS </log>
         <accounts> ACCTS </accounts>
         <touchedAccounts> TOUCHED </touchedAccounts>
         <statusCode> STATUSCODE </statusCode>

    syntax KItem ::= accessListResult( accountsSet: Set, storageSet: Set ) [symbol]
    syntax KItem ::= extractAccessList() [function, symbol]
 // -------------------------------------------------------------------------------
    rule [[ extractAccessList() => accessListResult( ACCESSED, warmStorage2Set( keys_list(STORAGE), STORAGE, .Set) ) ]]
         <accessedAccounts> ACCESSED </accessedAccounts>
         <accessedStorage>  STORAGE  </accessedStorage>

    syntax Set ::= warmStorage2Set   ( List, Map, Set ) [function]
                 | warmStorage2SetAux( Int, List, Set ) [function]
 // --------------------------------------------------------------
    rule warmStorage2Set( .List, _, STORAGELIST ) => STORAGELIST
    rule warmStorage2Set( (ListItem(ACCT) => .List) _, STORAGE, RESULT => RESULT |Set warmStorage2SetAux(ACCT, Set2List({STORAGE[ACCT]}:>Set), .Set) )

    rule warmStorage2SetAux( _, .List, RESULT ) => RESULT
    rule warmStorage2SetAux( ACCT, (ListItem(LOCATION) => .List) _LOCATIONS, RESULT => RESULT |Set SetItem(storageLocation(ACCT, LOCATION)) )
```

-   `contractBytes` takes the contents of the `<code>` cell and returns its binary representation as a String.

```{.k .node}
    syntax String ::= contractBytes(AccountCode) [function, symbol]
 // ---------------------------------------------------------------
    rule contractBytes(WS) => #unparseByteStack(WS)
```

The following are expected to exist in the client, but are already defined in [data.md].

-   `accountEmpty` takes the contents of the `<code>` cell, the contents of the `<nonce>` cell, and the contents of the `<balance>` cell and returns true if the account is empty according to the semantics of EIP161 (i.e., empty code zero balance zero nonce).
-   `unparseByteStack` takes a WordStack and returns the corresponding byte String.
-   `initKevmCell` is the top cell initializer used to construct an initial configuration.
    The configuration is expected to have `$MODE`, `$PGM`, and `$SCHEDULE` parameters.
-   `logEntry` is an entry in the log data created by a transaction.
    It is expected to consist of an Int address, a List of Int topics, and a WordStack of data.
-   `NORMAL` is the value of `$MODE` used by actual transaction execution.

```{.k .node}
endmodule
```
