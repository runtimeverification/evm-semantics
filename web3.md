Web3 RPC JSON Handler
====================

```k
requires "evm.k"

module WEB3
    imports EVM
    imports EVM-DATA
    imports K-IO

    configuration
      <kevm-client>
        <kevm/>
        <blockchain>
          <chainID> $CHAINID:Int </chainID>
          <blockList> .List </blockList>
        </blockchain>
        <accountKeys> .Map </accountKeys>
        <nextFilterSlot> 0 </nextFilterSlot>
        <filters>
          <filter  multiplicity="*" type="Map">
            <filterID>  0   </filterID>
            <fromBlock> 0   </fromBlock>
            <toBlock>   0   </toBlock>
            <address>   0   </address>
            <topics>  .List </topics>
          </filter>
        </filters>
        <snapshots> .List </snapshots>
        <web3socket> $SOCK:Int </web3socket>
        <web3shutdownable> $SHUTDOWNABLE:Bool </web3shutdownable>
        <web3clientsocket> 0:IOInt </web3clientsocket>
        <web3request>
          <jsonrpc> "":JSON </jsonrpc>
          <callid> 0:JSON </callid>
          <method> "":JSON </method>
          <params> [ .JSONList ] </params>
          <batch> undef </batch>
        </web3request>
        <web3response> .List </web3response>
      </kevm-client>
```

The Blockchain State
--------------------

A `BlockchainItem` contains the information of a block and its network state.
The `blockList` cell stores a list of previous blocks and network states.
-   `#pushBlockchainState` saves a copy of the block state and network state as a `BlockchainItem` in the `blockList` cell.
-   `#getBlockchainState(Int)` restores a blockchain state for a given block number.
-   `#setBlockchainState(BlockchainItem)` helper rule for `#getBlockchainState(Int)`.
-   `#getBlockByNumber(Int)` retrieves a specific `BlockchainItem` from the `blockList` cell.

```k
    syntax BlockchainItem ::= ".BlockchainItem"
                            | "{" NetworkCell "|" BlockCell "}"
 // -----------------------------------------------------------

    syntax KItem ::= "#pushBlockchainState"
 // ---------------------------------------
    rule <k> #pushBlockchainState => . ... </k>
         <blockList> (.List => ListItem({ <network> NETWORK </network> | <block> BLOCK </block> })) ... </blockList>
         <network> NETWORK </network>
         <block>   BLOCK   </block>

    syntax KItem ::= #getBlockchainState ( Int )
 // --------------------------------------------
    rule <k> #getBlockchainState(BLOCKNUM) => #setBlockchainState(#getBlockByNumber(BLOCKNUM, BLOCKLIST)) ... </k>
         <blockList> BLOCKLIST </blockList>

    syntax KItem ::= #setBlockchainState ( BlockchainItem )
 // -------------------------------------------------------
    rule <k> #setBlockchainState({ <network> NETWORK </network> | <block> BLOCK </block> }) => . ... </k>
         <network> _ => NETWORK </network>
         <block>   _ => BLOCK   </block>

    rule <k> #setBlockchainState(.BlockchainItem) => #sendResponse("error": {"code": -37600, "message": "Unable to find block by number"}) ... </k>

    syntax BlockchainItem ::= #getBlockByNumber ( Int , List ) [function]
 // ---------------------------------------------------------------------
    rule #getBlockByNumber(BLOCKNUM,  ListItem({ _ | <block> <number> BLOCKNUM </number> ... </block> } #as BLOCKCHAINITEM) REST ) => BLOCKCHAINITEM
    rule #getBlockByNumber(BLOCKNUM', ListItem({ _ | <block> <number> BLOCKNUM </number> ... </block> }                   ) REST ) => #getBlockByNumber(BLOCKNUM', REST)
      requires BLOCKNUM =/=Int BLOCKNUM'
    rule #getBlockByNumber(_, .List) => .BlockchainItem

    syntax AccountItem ::= AccountCell | ".NoAccount"
 // -------------------------------------------------

    syntax AccountItem ::= #getAccountFromBlockchainItem( BlockchainItem , Int ) [function]
 // ---------------------------------------------------------------------------------------
    rule #getAccountFromBlockchainItem ( { <network> <accounts> (<account> <acctID> ACCT </acctID> ACCOUNTDATA </account>) ... </accounts>  ... </network> | _ } , ACCT ) => <account> <acctID> ACCT </acctID> ACCOUNTDATA </account>
    rule #getAccountFromBlockchainItem(_, _) => .NoAccount [owise]

    syntax BlockIdentifier ::= Int | String
 // ---------------------------------------

    syntax BlockIdentifier ::= #parseBlockIdentifier ( String ) [function]
 // --------------------------------------------------------------------
    rule #parseBlockIdentifier(TAG) => TAG
      requires TAG ==String "earliest"
        orBool TAG ==String "latest"
        orBool TAG ==String "pending"

    rule #parseBlockIdentifier(BLOCKNUM) => #parseHexWord(BLOCKNUM) [owise]

    syntax KItem ::= #getAccountAtBlock ( BlockIdentifier , Int )
 // -------------------------------------------------------------
    rule <k> #getAccountAtBlock(BLOCKNUM:Int , ACCTID) => #getAccountFromBlockchainItem(#getBlockByNumber(BLOCKNUM, BLOCKLIST), ACCTID) ... </k>
         <blockList> BLOCKLIST </blockList>

    rule <k> #getAccountAtBlock(TAG , ACCTID) => #getAccountFromBlockchainItem(#getBlockByNumber(0, BLOCKLIST), ACCTID) ... </k>
         <blockList> BLOCKLIST </blockList>
      requires TAG ==String "earliest"

    rule <k> #getAccountAtBlock(TAG , ACCTID) => #getAccountFromBlockchainItem(#getBlockByNumber((size(BLOCKLIST) -Int 1), BLOCKLIST), ACCTID) ... </k>
         <blockList> BLOCKLIST </blockList>
      requires TAG ==String "latest"

    rule <k> #getAccountAtBlock(TAG , ACCTID) => #getAccountFromBlockchainItem({<network> NETWORK </network> | <block> BLOCK </block>}, ACCTID) ... </k>
         <network> NETWORK </network>
         <block>   BLOCK   </block>
      requires TAG ==String "pending"

```

WEB3 JSON RPC
-------------

```k
    syntax JSON ::= "null" | "undef"
 // --------------------------------

    syntax JSON ::= #getJSON ( JSONKey , JSON ) [function]
 // ------------------------------------------------------
    rule #getJSON( KEY, { KEY : J, _ } )     => J
    rule #getJSON( _, { .JSONList } )        => undef
    rule #getJSON( KEY, { KEY2 : _, REST } ) => #getJSON( KEY, { REST } )
      requires KEY =/=K KEY2

    syntax Int ::= #getInt ( JSONKey , JSON ) [function]
 // ----------------------------------------------------
    rule #getInt( KEY, J ) => {#getJSON( KEY, J )}:>Int

    syntax String ::= #getString ( JSONKey , JSON ) [function]
 // ----------------------------------------------------------
    rule #getString( KEY, J ) => {#getJSON( KEY, J )}:>String

    syntax IOJSON ::= JSON | IOError
 // --------------------------------

    syntax EthereumSimulation ::= accept() [symbol]
 // -----------------------------------------------
    rule <k> accept() => getRequest() ... </k>
         <web3socket> SOCK </web3socket>
         <web3clientsocket> _ => #accept(SOCK) </web3clientsocket>

    syntax KItem ::= getRequest()
 // -----------------------------
    rule <k> getRequest() => #loadRPCCall(#getRequest(SOCK)) ... </k>
         <web3clientsocket> SOCK </web3clientsocket>
         <batch> _ => undef </batch>

    syntax IOJSON ::= #getRequest(Int) [function, hook(JSON.read)]
 // --------------------------------------------------------------

    syntax K ::= #putResponse(JSON, Int) [function, hook(JSON.write)]
 // -----------------------------------------------------------------

    syntax KItem ::= #loadRPCCall(IOJSON)
 // -------------------------------------
    rule <k> #loadRPCCall({ _ } #as J) => #checkRPCCall ~> #runRPCCall ... </k>
         <jsonrpc> _ => #getJSON("jsonrpc", J) </jsonrpc>
         <callid>  _ => #getJSON("id"     , J) </callid>
         <method>  _ => #getJSON("method" , J) </method>
         <params>  _ => #getJSON("params" , J) </params>

    rule <k> #loadRPCCall(#EOF) => #shutdownWrite(SOCK) ~> #close(SOCK) ~> accept() ... </k>
         <web3clientsocket> SOCK </web3clientsocket>

    rule <k> #loadRPCCall([ _, _ ] #as J) => #loadFromBatch ... </k>
         <batch> _ => J </batch>
         <web3response> _ => .List </web3response>

    rule <k> #loadRPCCall(_:String #Or null #Or _:Int #Or [ .JSONList ]) => #sendResponse("error": {"code": -32600, "message": "Invalid Request"}) ... </k>
         <callid> _ => null </callid>

    rule <k> #loadRPCCall(undef) => #sendResponse("error": {"code": -32700, "message": "Parse error"}) ... </k>
         <callid> _ => null </callid>

    syntax KItem ::= "#loadFromBatch"
 // ---------------------------------
    rule <k> #loadFromBatch ~> _ => #loadRPCCall(J) </k>
         <batch> [ J , JS => JS ] </batch>

    rule <k> #loadFromBatch ~> _ => #putResponse(List2JSON(RESPONSE), SOCK) ~> getRequest() </k>
         <batch> [ .JSONList ] </batch>
         <web3clientsocket> SOCK </web3clientsocket>
         <web3response> RESPONSE </web3response>
      requires size(RESPONSE) >Int 0

    rule <k> #loadFromBatch ~> _ => getRequest() </k>
         <batch> [ .JSONList ] </batch>
         <web3response> .List </web3response>

    syntax JSON ::= List2JSON(List)           [function]
                  | List2JSON(List, JSONList) [function, klabel(List2JSONAux)]
 // --------------------------------------------------------------------------
    rule List2JSON(L) => List2JSON(L, .JSONList)

    rule List2JSON(L ListItem(J), JS) => List2JSON(L, (J, JS))
    rule List2JSON(.List        , JS) => [ JS ]

    syntax KItem ::= #sendResponse( JSON )
 // --------------------------------------
    rule <k> #sendResponse(J) ~> _ => #putResponse({ "jsonrpc": "2.0", "id": CALLID, J }, SOCK) ~> getRequest() </k>
         <callid> CALLID </callid>
         <web3clientsocket> SOCK </web3clientsocket>
         <batch> undef </batch>
      requires CALLID =/=K undef

    rule <k> #sendResponse(_) ~> _ => getRequest() </k>
         <callid> undef </callid>
         <batch> undef </batch>

    rule <k> #sendResponse(J) ~> _ => #loadFromBatch </k>
         <callid> CALLID </callid>
         <batch> [ _ ] </batch>
         <web3response> ... .List => ListItem({ "jsonrpc": "2.0", "id": CALLID, J }) </web3response>

    rule <k> #sendResponse(_) ~> _ => #loadFromBatch </k>
         <callid> undef </callid>
         <batch> [ _ ] </batch>

    syntax KItem ::= "#checkRPCCall"
 // --------------------------------
    rule <k> #checkRPCCall => . ...</k>
         <jsonrpc> "2.0" </jsonrpc>
         <method> _:String </method>
         <params> undef #Or [ _ ] #Or { _ } </params>
         <callid> _:String #Or null #Or _:Int #Or undef </callid>

    rule <k> #checkRPCCall => #sendResponse( "error": {"code": -32600, "message": "Invalid Request"} ) ... </k>
         <callid> undef #Or [ _ ] #Or { _ } => null </callid> [owise]

    rule <k> #checkRPCCall => #sendResponse( "error": {"code": -32600, "message": "Invalid Request"} ) ... </k>
         <callid> _:Int </callid> [owise]

    rule <k> #checkRPCCall => #sendResponse( "error": {"code": -32600, "message": "Invalid Request"} ) ... </k>
         <callid> _:String </callid> [owise]

    syntax KItem ::= "#runRPCCall"
 // ------------------------------
    rule <k> #runRPCCall => #firefly_shutdown ... </k>
         <method> "firefly_shutdown" </method>
    rule <k> #runRPCCall => #net_version ... </k>
         <method> "net_version" </method>
    rule <k> #runRPCCall => #web3_clientVersion ... </k>
         <method> "web3_clientVersion" </method>
    rule <k> #runRPCCall => #eth_gasPrice ... </k>
         <method> "eth_gasPrice" </method>
    rule <k> #runRPCCall => #eth_blockNumber ... </k>
         <method> "eth_blockNumber" </method>
    rule <k> #runRPCCall => #eth_accounts ... </k>
         <method> "eth_accounts" </method>
    rule <k> #runRPCCall => #eth_getBalance ... </k>
         <method> "eth_getBalance" </method>
    rule <k> #runRPCCall => #eth_getStorageAt ... </k>
         <method> "eth_getStorageAt" </method>
    rule <k> #runRPCCall => #eth_getCode ... </k>
         <method> "eth_getCode" </method>
    rule <k> #runRPCCall => #eth_getTransactionCount ... </k>
         <method> "eth_getTransactionCount" </method>
    rule <k> #runRPCCall => #eth_sign ... </k>
         <method> "eth_sign" </method>
    rule <k> #runRPCCall => #evm_snapshot ... </k>
         <method> "evm_snapshot" </method>
    rule <k> #runRPCCall => #evm_revert ... </k>
         <method> "evm_revert" </method>
    rule <k> #runRPCCall => #evm_increaseTime ... </k>
         <method> "evm_increaseTime" </method>
    rule <k> #runRPCCall => #eth_newBlockFilter ... </k>
         <method> "eth_newBlockFilter" </method>
    rule <k> #runRPCCall => #eth_uninstallFilter ... </k>
         <method> "eth_uninstallFilter" </method>
    rule <k> #runRPCCall => #eth_sendTransaction ... </k>
         <method> "eth_sendTransaction" </method>
    rule <k> #runRPCCall => #personal_importRawKey ... </k>
         <method> "personal_importRawKey" </method>

    rule <k> #runRPCCall => #sendResponse( "error": {"code": -32601, "message": "Method not found"} ) ... </k> [owise]

    syntax KItem ::= "#firefly_shutdown"
 // ------------------------------------
    rule <k> #firefly_shutdown ~> _ => #putResponse({ "jsonrpc": "2.0" , "id": CALLID , "result": "Firefly client shutting down!" }, SOCK) </k>
         <web3shutdownable> true </web3shutdownable>
         <callid> CALLID </callid>
         <web3clientsocket> SOCK </web3clientsocket>
         <exit-code> _ => 0 </exit-code>

    rule <k> #firefly_shutdown => #sendResponse( "error": {"code": -32800, "message": "Firefly client not started with `--shutdownable`!"} ) ... </k>
         <web3shutdownable> false </web3shutdownable>

    syntax KItem ::= "#net_version"
 // -------------------------------
    rule <k> #net_version => #sendResponse( "result" : Int2String( CHAINID ) ) ... </k>
         <chainID> CHAINID </chainID>

    syntax KItem ::= "#web3_clientVersion"
 // --------------------------------------
    rule <k> #web3_clientVersion => #sendResponse( "result" : "Firefly RPC/v0.0.1/kevm" ) ... </k>

    syntax KItem ::= "#eth_gasPrice"
 // --------------------------------
    rule <k> #eth_gasPrice => #sendResponse( "result" : #unparseQuantity( PRICE ) ) ... </k>
         <gasPrice> PRICE </gasPrice>

    syntax KItem ::= "#eth_blockNumber"
 // -----------------------------------
    rule <k> #eth_blockNumber => #sendResponse( "result" : #unparseQuantity( BLOCKNUM ) ) ... </k>
         <number> BLOCKNUM </number>

    syntax KItem ::= "#eth_accounts"
 // --------------------------------
    rule <k> #eth_accounts => #sendResponse( "result" : [ #acctsToJArray( ACCTS ) ] ) ... </k>
         <activeAccounts> ACCTS </activeAccounts>

    syntax JSONList ::= #acctsToJArray ( Set ) [function]
 // -----------------------------------------------------
    rule #acctsToJArray( .Set                      ) => .JSONList
    rule #acctsToJArray( SetItem( ACCT ) ACCTS:Set ) => #unparseData( ACCT, 20 ), #acctsToJArray( ACCTS )

    syntax KItem ::= "#eth_getBalance"
 // ----------------------------------
    rule <k> #eth_getBalance ... </k>
         <params> [ (DATA => #parseHexWord(DATA)), _, .JSONList ] </params>

    rule <k> #eth_getBalance => #getAccountAtBlock(#parseBlockIdentifier(TAG), DATA) ~> #eth_getBalance ... </k>
         <params> [ DATA, TAG, .JSONList ] </params>

    rule <k> <account> ... <balance> ACCTBALANCE </balance> ... </account> ~> #eth_getBalance => #sendResponse( "result" : #unparseQuantity( ACCTBALANCE )) ... </k>

    rule <k> .NoAccount ~> #eth_getBalance => #sendResponse( "result" : #unparseQuantity( 0 )) ... </k>

    syntax KItem ::= "#eth_getStorageAt"
 // ------------------------------------
    rule <k> #eth_getStorageAt ... </k>
         <params> [ (DATA => #parseHexWord(DATA)), QUANTITY:Int, _, .JSONList ] </params>

    rule <k> #eth_getStorageAt => #getAccountAtBlock(#parseBlockIdentifier(TAG), DATA) ~> #eth_getStorageAt ... </k>
         <params> [ DATA, QUANTITY, TAG, .JSONList ] </params>

    rule <k> <account> ... <storage> STORAGE </storage> ... </account> ~> #eth_getStorageAt => #sendResponse( "result" : #unparseQuantity( #lookup (STORAGE, QUANTITY))) ... </k>
         <params> [ DATA, QUANTITY, TAG, .JSONList ] </params>

    rule <k> .NoAccount ~> #eth_getStorageAt => #sendResponse( "result" : #unparseQuantity( 0 )) ... </k>

    syntax KItem ::= "#eth_getCode"
 // -------------------------------
    rule <k> #eth_getCode ... </k>
         <params> [ (DATA => #parseHexWord(DATA)), _, .JSONList ] </params>

    rule <k> #eth_getCode => #getAccountAtBlock(#parseBlockIdentifier(TAG), DATA) ~> #eth_getCode ... </k>
         <params> [ DATA, TAG, .JSONList ] </params>

     rule <k> <account> ... <code> CODE </code> ... </account> ~> #eth_getCode =>  #sendResponse( "result" : #unparseDataByteArray( CODE )) ... </k>

     rule <k> .NoAccount ~> #eth_getCode => #sendResponse( "result" : #unparseDataByteArray( .ByteArray )) ... </k>

    syntax KItem ::= "#eth_getTransactionCount"
 // -------------------------------------------
    rule <k> #eth_getTransactionCount ... </k>
         <params> [ (DATA => #parseHexWord(DATA)), _, .JSONList ] </params>

    rule <k> #eth_getTransactionCount => #getAccountAtBlock(#parseBlockIdentifier(TAG), DATA) ~> #eth_getTransactionCount ... </k>
         <params> [ DATA, TAG, .JSONList ] </params>

    rule <k> <account> ... <nonce> NONCE </nonce> ... </account> ~> #eth_getTransactionCount => #sendResponse( "result" : #unparseQuantity( NONCE )) ... </k>

    rule <k> .NoAccount ~> #eth_getTransactionCount => #sendResponse ("result" : #unparseQuantity( 0 )) ... </k>

    syntax KItem ::= "#eth_sign"
 // ----------------------------
    rule <k> #eth_sign => #signMessage(KEY, #hashMessage(#unparseByteStack(#parseByteStack(MESSAGE)))) ... </k>
         <params> [ ACCTADDR, MESSAGE, .JSONList ] </params>
         <accountKeys>... #parseHexWord(ACCTADDR) |-> KEY ...</accountKeys>

    rule <k> #eth_sign => #sendResponse( "error": {"code": 3, "message": "Execution error", "data": [{ "code": 100, "message": "Account key doesn't exist, account locked!" }]} ) ... </k>
         <params> [ ACCTADDR, _ ] </params>
         <accountKeys> KEYMAP </accountKeys>
      requires notBool #parseHexWord(ACCTADDR) in_keys(KEYMAP)

    syntax KItem ::= #signMessage ( String , String )
 // -------------------------------------------------
    rule <k> #signMessage(KEY, MHASH) => #sendResponse( "result" : "0x" +String ECDSASign( MHASH, KEY ) ) ... </k>

    syntax String ::= #hashMessage ( String ) [function]
 // ----------------------------------------------------
    rule #hashMessage( S ) => #unparseByteStack(#parseHexBytes(Keccak256("\x19Ethereum Signed Message:\n" +String Int2String(lengthString(S)) +String S)))

    syntax KItem ::= "#evm_snapshot"
 // --------------------------------
    rule <k> #evm_snapshot => #pushNetworkState ~> #sendResponse( "result" : #unparseQuantity( size ( SNAPSHOTS ) ) ) ... </k>
         <snapshots> SNAPSHOTS </snapshots>

    syntax KItem ::= "#pushNetworkState"
 // ------------------------------------
    rule <k> #pushNetworkState => . ... </k>
         <snapshots> ... ( .List => ListItem(NETWORKSTATE)) </snapshots>
         <network> NETWORKSTATE </network>

    syntax KItem ::= "#evm_revert"
 // ------------------------------
    rule <k> #evm_revert => #sendResponse( "result" : true ) ... </k>
         <params> [ .JSONList ] </params>
         <snapshots> ... ( ListItem(NETWORKSTATE) => .List ) </snapshots>
         <network> ( _ => NETWORKSTATE ) </network>

    rule <k> #evm_revert ... </k>
         <params> [ (DATA => #parseHexWord(DATA)), .JSONList ] </params>

    rule <k> #evm_revert ... </k>
         <params> ( [ DATA:Int, .JSONList ] => [ .JSONList ] ) </params>
         <snapshots> ( SNAPSHOTS => range(SNAPSHOTS, 0, DATA ) ) </snapshots>

    syntax KItem ::= "#evm_increaseTime"
 // ------------------------------------
    rule <k> #evm_increaseTime => #sendResponse( "result" : Int2String(TS +Int DATA ) ) ... </k>
         <params> [ DATA:Int, .JSONList ] </params>
         <timestamp> ( TS:Int => ( TS +Int DATA ) ) </timestamp>

    syntax KItem ::= "#eth_newBlockFilter"
 // --------------------------------------
    rule <k> #eth_newBlockFilter => #sendResponse ( "result": #unparseQuantity( FILTID )) ... </k>
         <filters>
           ( .Bag
          => <filter>
               <filterID> FILTID </filterID>
               <fromBlock> BLOCKNUM </fromBlock>
               ...
             </filter>
           )
           ...
         </filters>
         <number> BLOCKNUM </number>
         <nextFilterSlot> ( FILTID:Int => FILTID +Int 1 ) </nextFilterSlot>

    syntax KItem ::= "#eth_uninstallFilter"
 // ---------------------------------------
    rule <k> #eth_uninstallFilter ... </k>
         <params> [ (DATA => #parseHexWord(DATA)), .JSONList ] </params>

    rule <k> #eth_uninstallFilter => #sendResponse ( "result": true ) ... </k>
         <params> [ FILTID, .JSONList ] </params>
         <filters>
           ( <filter>
               <filterID> FILTID </filterID>
               ...
             </filter>
          => .Bag
           )
           ...
         </filters>

    rule <k> #eth_uninstallFilter => #sendResponse ( "result": false ) ... </k> [owise]
```

# eth_sendTransaction

**TODO**: Handle contract creation

```k
    syntax KItem ::= "#eth_sendTransaction"
                   | "#eth_sendTransaction_finalize"
 // ------------------------------------------------
    rule <k> #eth_sendTransaction => loadTX J ~> #eth_sendTransaction_finalize ... </k>
         <params> [ ({ _ } #as J), .JSONList ] </params>
      requires isString( #getJSON("from",J) )

    rule <k> #eth_sendTransaction_finalize => #sendResponse( "result": "0x" +String #hashSignedTx( TXID ) ) ... </k>
         <txPending> ListItem( TXID ) ... </txPending>

    rule <k> #eth_sendTransaction => #sendResponse( "error": {"code": -32000, "message": "from not found; is required"} ) ... </k>
         <params> [ ({ _ } #as J), .JSONList ] </params>
      requires notBool isString( #getJSON("from",J) )

    rule <k> #eth_sendTransaction => #sendResponse( "error": {"code": -32000, "message": "Incorrect number of arguments. Method 'eth_sendTransaction' requires exactly 1 argument."} ) ... </k> [owise]
```

- `#hashSignedTx` Takes a transaction ID. Returns the hash of the rlp-encoded transaction with R S and V.
- `#hashUnsignedTx` Returns the hash of the rlp-encoded transaction without R S or V.

```k
    syntax String ::= #hashSignedTx   ( Int ) [function]
                    | #hashUnsignedTx ( Int ) [function]
 // ----------------------------------------------------
    rule [[ #hashSignedTx( TXID )
         => Keccak256( #rlpEncodeLength(         #rlpEncodeWord( TXNONCE )
                                         +String #rlpEncodeWord( GPRICE )
                                         +String #rlpEncodeWord( GLIMIT )
                                         +String #rlpEncodeWord( ACCTTO )
                                         +String #rlpEncodeWord( VALUE )
                                         +String #rlpEncodeString( #unparseByteStack( DATA ) )
                                         +String #rlpEncodeWord( V +Int 27 )
                                         +String #rlpEncodeString( #unparseByteStack( R ) )
                                         +String #rlpEncodeString( #unparseByteStack( S ) )
                                       , 192
                                       )
                     )
         ]]
         <message>
           <msgID> TXID </msgID>
           <txNonce>    TXNONCE </txNonce>
           <txGasPrice> GPRICE  </txGasPrice>
           <txGasLimit> GLIMIT  </txGasLimit>
           <to>         ACCTTO  </to>
           <value>      VALUE   </value>
           <data>       DATA    </data>
           <sigR>       R       </sigR>
           <sigS>       S       </sigS>
           <sigV>       V       </sigV>
         </message>

    rule [[ #hashUnsignedTx( TXID )
         => Keccak256( #rlpEncodeLength(         #rlpEncodeWord( TXNONCE )
                                         +String #rlpEncodeWord( GPRICE )
                                         +String #rlpEncodeWord( GLIMIT )
                                         +String #rlpEncodeWord( ACCTTO )
                                         +String #rlpEncodeWord( VALUE )
                                         +String #rlpEncodeString( #unparseByteStack( DATA ) )
                                       , 192
                                       )
                     )
         ]]
         <message>
           <msgID>      TXID    </msgID>
           <txNonce>    TXNONCE </txNonce>
           <txGasPrice> GPRICE  </txGasPrice>
           <txGasLimit> GLIMIT  </txGasLimit>
           <to>         ACCTTO  </to>
           <value>      VALUE   </value>
           <data>       DATA    </data>
           ...
         </message>
```

- `loadTX` Loads the JSON parameter for a transaction and signs it with the "from" account's key.

**TODO**: Make sure nonce is being determined properly
**TODO**: You're supposed to be able to overwrite a pending tx by using its same "from" and "nonce" values

```k
    syntax KItem ::= "loadTX" JSON
 // ------------------------------
    rule <k> loadTX J => signTX !TXID ACCTADDR ... </k>
         <txPending> .List => ListItem( !TXID ) ... </txPending>
         <account>
           <acctID> ACCTADDR </acctID>
           <nonce> ACCTNONCE => ACCTNONCE +Int 1 </nonce>
           ...
         </account>
         <messages>
           (.Bag => <message>
             <msgID> !TXID:Int </msgID>
             <txNonce>    #if isString( #getJSON("nonce",    J) ) #then #parseHexWord(#getString("nonce",J))    #else ACCTNONCE  #fi </txNonce>
             <to>         #if isString( #getJSON("to",       J) ) #then #parseHexWord(#getString("to",J))       #else 0          #fi </to>
             <txGasLimit> #if isString( #getJSON("gas",      J) ) #then #parseHexWord(#getString("gas",J))      #else 90000      #fi </txGasLimit>
             <txGasPrice> #if isString( #getJSON("gasPrice", J) ) #then #parseHexWord(#getString("gasPrice",J)) #else GASP       #fi </txGasPrice>
             <value>      #if isString( #getJSON("value",    J) ) #then #parseHexWord(#getString("value",J))    #else 0          #fi </value>
             <data>       #if isString( #getJSON("data",     J) ) #then #parseByteStack(#getString("data",J))   #else .ByteArray #fi </data>
             ...
           </message>)
         ...
         </messages>
         <gasPrice> GASP </gasPrice>
      requires #parseHexWord(#getString("from",J)) ==Int ACCTADDR

    syntax KItem ::= "signTX" Int Int
                   | "signTX" Int String [klabel(signTXAux)]
 // --------------------------------------------------------
    rule <k> signTX TXID ACCTFROM:Int => signTX TXID ECDSASign( Hex2Raw( #hashUnsignedTx( TXID ) ), #unparseByteStack( #padToWidth( 32, #asByteStack( KEY ) ) ) ) ... </k>
         <accountKeys> ... ACCTFROM |-> KEY ... </accountKeys>
         <message>
           <msgID>      TXID    </msgID>
           <txNonce>    TXNONCE </txNonce>
           <txGasPrice> GPRICE  </txGasPrice>
           <txGasLimit> GLIMIT  </txGasLimit>
           <to>         ACCTTO  </to>
           <value>      VALUE   </value>
           <data>       DATA    </data>
           ...
         </message>

    rule <k> signTX TXID SIG:String => . ... </k>
         <message>
           <msgID> TXID </msgID>
           <sigR> _ => #parseHexBytes( substrString( SIG, 0, 64 ) )   </sigR>
           <sigS> _ => #parseHexBytes( substrString( SIG, 64, 128 ) ) </sigS>
           <sigV> _ => #parseHexWord( substrString( SIG, 128, 130 ) ) </sigV>
           ...
         </message>
```

- `#personal_importRawKey` Takes an unencrypted private key, encrypts it with a passphrase, stores it and returns the address of the key.

**TODO**: Currently nothing is done with the passphrase

```k
    syntax KItem ::= "#personal_importRawKey"
 // -----------------------------------------
    rule <k> #personal_importRawKey => #acctFromPrivateKey PRIKEY ~> #sendResponse( "result": #unparseData( #addrFromPrivateKey( PRIKEY ), 20 ) ) ... </k>
         <params> [ PRIKEY:String, PASSPHRASE:String, .JSONList ] </params>
      requires lengthString( PRIKEY ) ==Int 66

    rule <k> #personal_importRawKey => #sendResponse( "error": {"code": -32000, "message":"Private key length is invalid. Must be 32 bytes."} ) ... </k>
         <params> [ PRIKEY:String, _:String, .JSONList ] </params>
      requires lengthString( PRIKEY ) =/=Int 66

    rule <k> #personal_importRawKey => #sendResponse( "error": {"code": -32000, "message":"Method 'personal_importRawKey' requires exactly 2 parameters"} ) ... </k> [owise]

    syntax KItem ::= "#acctFromPrivateKey" String
 // ---------------------------------------------
    rule <k> #acctFromPrivateKey KEY => #newAccount #addrFromPrivateKey(KEY) ... </k>
         <accountKeys> M => M[#addrFromPrivateKey(KEY) <- #parseHexWord(KEY)] </accountKeys>

endmodule
```
