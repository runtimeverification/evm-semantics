Web3 RPC JSON Handler
====================

```k
requires "evm.k"
requires "state-loader.k"

module WEB3
    imports EVM
    imports EVM-DATA
    imports K-IO
    imports STATE-LOADER

    configuration
      <kevm-client>
        <kevm/>
        <blockchain>
          <chainID> $CHAINID:Int </chainID>
          <blockList> .List </blockList>
        </blockchain>
        <accountKeys> .Map </accountKeys>
        <nextFilterSlot> 0 </nextFilterSlot>
        <txReceipts>
          <txReceipt multiplicity ="*" type="Map">
            <txHash>          "":String  </txHash>
            <txCumulativeGas> 0          </txCumulativeGas>
            <logSet>          .List      </logSet>
            <bloomFilter>     .ByteArray </bloomFilter>
            <txStatus>        0          </txStatus>
          </txReceipt>
        </txReceipts>
        <filters>
          <filter multiplicity="*" type="Map">
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

    syntax AccountItem ::= AccountCell | ".AccountItem"
 // ---------------------------------------------------

    syntax AccountItem ::= #getAccountFromBlockchainItem( BlockchainItem , Int ) [function]
 // ---------------------------------------------------------------------------------------
    rule #getAccountFromBlockchainItem ( { <network> <accounts> (<account> <acctID> ACCT </acctID> ACCOUNTDATA </account>) ... </accounts>  ... </network> | _ } , ACCT ) => <account> <acctID> ACCT </acctID> ACCOUNTDATA </account>
    rule #getAccountFromBlockchainItem(_, _) => .AccountItem [owise]

    syntax BlockIdentifier ::= Int | String
 // ---------------------------------------

    syntax BlockIdentifier ::= #parseBlockIdentifier ( String ) [function]
 // ----------------------------------------------------------------------
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

    rule <k> #getAccountAtBlock(TAG , ACCTID) => #getAccountFromBlockchainItem(#getBlockByNumber(size(BLOCKLIST) -Int 1, BLOCKLIST), ACCTID) ... </k>
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
    syntax JSON ::= "null" | "undef" | ByteArray | Account
 // ------------------------------------------------------

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

    syntax Bool ::= isJSONUndef ( JSON ) [function]
 // -----------------------------------------------
    rule isJSONUndef(J) => J ==K undef

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
    rule <k> #runRPCCall => #firefly_addAccount ... </k>
         <method> "firefly_addAccount" </method>
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
    rule <k> #runRPCCall => #eth_sendRawTransaction ... </k>
         <method> "eth_sendRawTransaction" </method>
    rule <k> #runRPCCall => #personal_importRawKey ... </k>
         <method> "personal_importRawKey" </method>
    rule <k> #runRPCCall => #eth_call ... </k>
         <method> "eth_call" </method>

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

    rule <k> .AccountItem ~> #eth_getBalance => #sendResponse( "result" : #unparseQuantity( 0 )) ... </k>

    rule <k> #eth_getBalance => #sendResponse( "error": {"code": -32000, "message": "Incorrect number of arguments. Method 'eth_getBalance' requires exactly 2 arguments."} ) ... </k> [owise]

    syntax KItem ::= "#eth_getStorageAt"
 // ------------------------------------
    rule <k> #eth_getStorageAt ... </k>
         <params> [ (DATA => #parseHexWord(DATA)), (QUANTITY => #parseHexWord(QUANTITY)), _, .JSONList ] </params>

    rule <k> #eth_getStorageAt => #getAccountAtBlock(#parseBlockIdentifier(TAG), DATA) ~> #eth_getStorageAt ... </k>
         <params> [ DATA, QUANTITY, TAG, .JSONList ] </params>

    rule <k> <account> ... <storage> STORAGE </storage> ... </account> ~> #eth_getStorageAt => #sendResponse( "result" : #unparseQuantity( #lookup (STORAGE, QUANTITY))) ... </k>
         <params> [ DATA, QUANTITY, TAG, .JSONList ] </params>

    rule <k> .AccountItem ~> #eth_getStorageAt => #sendResponse( "result" : #unparseQuantity( 0 )) ... </k>

    rule <k> #eth_getStorageAt => #sendResponse( "error": {"code": -32000, "message": "Incorrect number of arguments. Method 'eth_getStorageAt' requires exactly 3 arguments."} ) ... </k> [owise]

    syntax KItem ::= "#eth_getCode"
 // -------------------------------
    rule <k> #eth_getCode ... </k>
         <params> [ (DATA => #parseHexWord(DATA)), _, .JSONList ] </params>

    rule <k> #eth_getCode => #getAccountAtBlock(#parseBlockIdentifier(TAG), DATA) ~> #eth_getCode ... </k>
         <params> [ DATA, TAG, .JSONList ] </params>

     rule <k> <account> ... <code> CODE </code> ... </account> ~> #eth_getCode =>  #sendResponse( "result" : #unparseDataByteArray( CODE )) ... </k>

     rule <k> .AccountItem ~> #eth_getCode => #sendResponse( "result" : #unparseDataByteArray( .ByteArray )) ... </k>

    rule <k> #eth_getCode => #sendResponse( "error": {"code": -32000, "message": "Incorrect number of arguments. Method 'eth_getCode' requires exactly 2 arguments."} ) ... </k> [owise]

    syntax KItem ::= "#eth_getTransactionCount"
 // -------------------------------------------
    rule <k> #eth_getTransactionCount ... </k>
         <params> [ (DATA => #parseHexWord(DATA)), _, .JSONList ] </params>

    rule <k> #eth_getTransactionCount => #getAccountAtBlock(#parseBlockIdentifier(TAG), DATA) ~> #eth_getTransactionCount ... </k>
         <params> [ DATA, TAG, .JSONList ] </params>

    rule <k> <account> ... <nonce> NONCE </nonce> ... </account> ~> #eth_getTransactionCount => #sendResponse( "result" : #unparseQuantity( NONCE )) ... </k>

    rule <k> .AccountItem ~> #eth_getTransactionCount => #sendResponse ("result" : #unparseQuantity( 0 )) ... </k>

    rule <k> #eth_getTransactionCount => #sendResponse( "error": {"code": -32000, "message": "Incorrect number of arguments. Method 'eth_getTransactionCount' requires exactly 2 arguments."} ) ... </k> [owise]

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

    syntax SnapshotItem ::= "{" BlockListCell "|" NetworkCell "|" BlockCell "}"
 // ---------------------------------------------------------------------------

    syntax KItem ::= "#evm_snapshot"
 // --------------------------------
    rule <k> #evm_snapshot => #pushNetworkState ~> #sendResponse( "result" : #unparseQuantity( size ( SNAPSHOTS ))) ... </k>
         <snapshots> SNAPSHOTS </snapshots>

    syntax KItem ::= "#pushNetworkState"
 // ------------------------------------
    rule <k> #pushNetworkState => . ... </k>
         <snapshots> ... (.List => ListItem({ <blockList> BLOCKLIST </blockList> | <network> NETWORK </network> | <block> BLOCK </block> })) </snapshots>
         <network>   NETWORK   </network>
         <block>     BLOCK     </block>
         <blockList> BLOCKLIST </blockList>

    syntax KItem ::= "#popNetworkState"
 // -----------------------------------
    rule <k> #popNetworkState => . ... </k>
         <snapshots> ... ( ListItem({ <blockList> BLOCKLIST </blockList> | <network> NETWORK </network> | <block> BLOCK </block> }) => .List ) </snapshots>
         <network>   ( _ => NETWORK )   </network>
         <block>     ( _ => BLOCK )     </block>
         <blockList> ( _ => BLOCKLIST ) </blockList>

    syntax KItem ::= "#evm_revert"
 // ------------------------------
    rule <k> #evm_revert => #popNetworkState ~> #sendResponse( "result" : true ) ... </k>
         <params>    [ DATA:Int, .JSONList ] </params>
         <snapshots> SNAPSHOTS </snapshots>
      requires DATA ==Int ( size(SNAPSHOTS) -Int 1 )

    rule <k> #evm_revert ... </k>
         <params> [ (DATA => #parseHexWord(DATA)), .JSONList ] </params>

    rule <k> #evm_revert ... </k>
         <params> ( [ DATA:Int, .JSONList ] ) </params>
         <snapshots> ( SNAPSHOTS => range(SNAPSHOTS, 0, DATA ) ) </snapshots>
      requires size(SNAPSHOTS) >Int (DATA +Int 1)

    rule <k> #evm_revert => #sendResponse( "error": {"code": -32000, "message": "Incorrect number of arguments. Method 'evm_revert' requires exactly 1 arguments. Request specified 0 arguments: [null]."} )  ... </k>
         <params> [ .JSONList ] </params>

     rule <k> #evm_revert => #sendResponse ( "result" : false ) ... </k> [owise]

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

eth_sendTransaction
-------------------

**TODO**: Only call `#executeTx TXID` when mining is turned on, or when the mining interval comes around.

```k
    syntax KItem ::= "#eth_sendTransaction"
                   | "#eth_sendTransaction_load" JSON
                   | "#eth_sendTransaction_final" Int
 // -------------------------------------------------
    rule <k> #eth_sendTransaction => #eth_sendTransaction_load J ... </k>
         <params> [ ({ _ } #as J), .JSONList ] </params>
      requires isString( #getJSON("from",J) )

    rule <k> #eth_sendTransaction => #sendResponse( "error": {"code": -32000, "message": "from not found; is required"} ) ... </k>
         <params> [ ({ _ } #as J), .JSONList ] </params>
      requires notBool isString( #getJSON("from",J) )

    rule <k> #eth_sendTransaction => #sendResponse( "error": {"code": -32000, "message": "Incorrect number of arguments. Method 'eth_sendTransaction' requires exactly 1 argument."} ) ... </k> [owise]

    rule <k> #eth_sendTransaction_load J => mkTX !ID:Int ~> #loadNonce #parseHexWord( #getString("from",J) ) !ID ~> load "transaction" : { !ID : J } ~> signTX !ID #parseHexWord( #getString("from",J) ) ~> #prepareTx !ID ~> #eth_sendTransaction_final !ID ... </k>

    rule <k> #eth_sendTransaction_final TXID => #sendResponse( "result": "0x" +String #hashSignedTx( TXID ) ) ... </k>

    rule <k> load "transaction" : { TXID : { "gas"      : (TG:String => #parseHexWord(TG))                    } } ... </k>
    rule <k> load "transaction" : { TXID : { "gasPrice" : (TP:String => #parseHexWord(TP))                    } } ... </k>
    rule <k> load "transaction" : { TXID : { "nonce"    : (TN:String => #parseHexWord(TN))                    } } ... </k>
    rule <k> load "transaction" : { TXID : { "v"        : (TW:String => #parseHexWord(TW))                    } } ... </k>
    rule <k> load "transaction" : { TXID : { "value"    : (TV:String => #parseHexWord(TV))                    } } ... </k>
    rule <k> load "transaction" : { TXID : { "to"       : (TT:String => #parseHexWord(TT))                    } } ... </k>
    rule <k> load "transaction" : { TXID : { "data"     : (TI:String => #parseByteStack(TI))                  } } ... </k>
    rule <k> load "transaction" : { TXID : { "r"        : (TR:String => #padToWidth(32, #parseByteStack(TR))) } } ... </k>
    rule <k> load "transaction" : { TXID : { "s"        : (TS:String => #padToWidth(32, #parseByteStack(TS))) } } ... </k>
    rule <k> load "transaction" : { TXID : { "from"     : _ } } => . ... </k>

    syntax KItem ::= "#loadNonce" Int Int
 // -------------------------------------
    rule <k> #loadNonce ACCT TXID => . ... </k>
         <message>
           <msgID> TXID </msgID>
           <txNonce> _ => NONCE </txNonce>
           ...
         </message>
         <account>
           <acctID> ACCT </acctID>
           <nonce> NONCE </nonce>
           ...
         </account>
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
                                         +String #rlpEncodeAccount( ACCTTO )
                                         +String #rlpEncodeWord( VALUE )
                                         +String #rlpEncodeString( #unparseByteStack( DATA ) )
                                         +String #rlpEncodeWord( V )
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
                                         +String #rlpEncodeAccount( ACCTTO )
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

-   signTX TXID ACCTFROM: Signs the transaction with TXID using ACCTFROM's private key

```k
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
           <sigR> _ => #parseHexBytes( substrString( SIG, 0, 64 ) )           </sigR>
           <sigS> _ => #parseHexBytes( substrString( SIG, 64, 128 ) )         </sigS>
           <sigV> _ => #parseHexWord( substrString( SIG, 128, 130 ) ) +Int 27 </sigV>
           ...
         </message>
```

eth_sendRawTransaction
----------------------

**TODO**: Verify the signature provided for the transaction

```k

    syntax KItem ::= "#eth_sendRawTransaction"
                   | "#eth_sendRawTransactionLoad"
                   | "#eth_sendRawTransactionVerify" Int
                   | "#eth_sendRawTransactionSend" Int
 // ----------------------------------------------------
    rule <k> #eth_sendRawTransaction => #eth_sendRawTransactionLoad ... </k>
         <params> [ RAWTX:String, .JSONList ] => #rlpDecode( Hex2Raw( RAWTX ) ) </params>

    rule <k> #eth_sendRawTransaction => #sendResponse("error": { "code": -32000, "message":"\"value\" argument must not be a number" } ) ... </k>
         <params> [ _:Int, .JSONList ] </params>

    rule <k> #eth_sendRawTransaction => #sendResponse("error": { "code": -32000, "message":"Invalid Signature" } ) ... </k> [owise]

    rule <k> #eth_sendRawTransactionLoad
          => mkTX !ID:Int
          ~> load "transaction" : { !ID : { "data"  : Raw2Hex(TI) , "gas"      : Raw2Hex(TG) , "gasPrice" : Raw2Hex(TP)
                                          , "nonce" : Raw2Hex(TN) , "r"        : Raw2Hex(TR) , "s"        : Raw2Hex(TS)
                                          , "to"    : Raw2Hex(TT) , "v"        : Raw2Hex(TW) , "value"    : Raw2Hex(TV)
                                          , .JSONList
                                          }
                                  }
          ~> #eth_sendRawTransactionVerify !ID
         ...
         </k>
         <params> [ TN, TP, TG, TT, TV, TI, TW, TR, TS, .JSONList ] </params>

    rule <k> #eth_sendRawTransactionLoad => #sendResponse( "error": { "code": -32000, "message":"Invalid Signature" } ) ... </k> [owise]

    rule <k> #eth_sendRawTransactionVerify TXID => #eth_sendRawTransactionSend TXID ... </k>
         <message>
           <msgID> TXID </msgID>
           <sigV> V </sigV>
           <sigR> R </sigR>
           <sigS> S </sigS>
           ...
         </message>
      requires ECDSARecover( Hex2Raw( #hashUnsignedTx( TXID ) ), V, #unparseByteStack(R), #unparseByteStack(S) ) =/=String ""

    rule <k> #eth_sendRawTransactionVerify _ => #sendResponse( "error": { "code": -32000, "message":"Invalid Signature" } ) ... </k> [owise]

    rule <k> #eth_sendRawTransactionSend TXID => #sendResponse( "result": "0x" +String #hashSignedTx( TXID ) ) ... </k>
```

Transaction Receipts
--------------------

-   The transaction receipt is a tuple of four items comprising:

    -   the cumulative gas used in the block containing the transaction receipt as of immediately after the transaction has happened,
    -   the set of logs created through execution of the transaction,
    -   the Bloom filter composed from information in those logs, and
    -   the status code of the transaction.

```k
    syntax KItem ::= "#makeTxReceipt" Int
 // -------------------------------------
    rule <k> #makeTxReceipt TXID => . ... </k>
         <txReceipts>
           ( .Bag
          => <txReceipt>
               <txHash> "0x" +String #hashSignedTx (TXID) </txHash>
               <txCumulativeGas> CGAS </txCumulativeGas>
               <logSet> LOGS </logSet>
               <bloomFilter> #bloomFilter(LOGS) </bloomFilter>
               <txStatus> bool2Word(STATUSCODE ==K EVMC_SUCCESS) </txStatus>
             </txReceipt>
           )
           ...
         </txReceipts>
         <statusCode> STATUSCODE </statusCode>
         <gasUsed> CGAS </gasUsed>
         <log> LOGS </log>
```

loadCallSettings
----------------

- Takes a JSON with parameters for sendTransaction/call/estimateGas/etc and sets up the execution environment

```k
    syntax KItem ::= "#loadCallSettings" JSON
 // -----------------------------------------
    rule <k> #loadCallSettings { .JSONList } => . ... </k>

    rule <k> #loadCallSettings { "from" : ( ACCTFROM:String => #parseHexWord( ACCTFROM ) ), REST } ... </k>
    rule <k> #loadCallSettings { ("from" : ACCTFROM:Int, REST => REST) } ... </k>
         <caller> _ => ACCTFROM </caller>
         <origin> _ => ACCTFROM </origin>

    rule <k> #loadCallSettings { "to" : ( ACCTTO:String => #parseHexWord( ACCTTO ) ), REST } ... </k>
    rule <k> #loadCallSettings { "to" : .Account   , REST => REST } ... </k>
    rule <k> #loadCallSettings { "to" : ACCTTO:Int , REST => REST } ... </k>
         <id> _ => ACCTTO </id>
         <program> _ => CODE </program>
         <jumpDests> _ => #computeValidJumpDests(CODE) </jumpDests>
         <account>
           <acctID> ACCTTO </acctID>
           <code> CODE </code>
           ...
         </account>

    rule <k> ( . => #newAccount ACCTTO ) ~> #loadCallSettings { "to" : ACCTTO:Int, REST } ... </k> [owise]

    rule <k> #loadCallSettings { "gas" : ( GLIMIT:String => #parseHexWord( GLIMIT ) ), REST } ... </k>
    rule <k> #loadCallSettings { ( "gas" : GLIMIT:Int, REST => REST ) } ... </k>
         <gas> _ => GLIMIT </gas>

    rule <k> #loadCallSettings { "gasPrice" : ( GPRICE:String => #parseHexWord( GPRICE ) ), REST } ... </k>
    rule <k> #loadCallSettings { ( "gasPrice" : GPRICE:Int, REST => REST ) } ... </k>
         <gasPrice> _ => GPRICE </gasPrice>

    rule <k> #loadCallSettings { "value" : ( VALUE:String => #parseHexWord( VALUE ) ), REST } ... </k>
    rule <k> #loadCallSettings { ( "value" : VALUE:Int, REST => REST ) } ... </k>
         <callValue> _ => VALUE </callValue>

    rule <k> #loadCallSettings { "data" : ( DATA:String => #parseByteStack( DATA ) ), REST } ... </k>
    rule <k> #loadCallSettings { ( "data" : DATA:ByteArray, REST => REST ) } ... </k>
         <callData> _ => DATA </callData>

    rule <k> #loadCallSettings { ( "nonce" : _, REST => REST ) } ... </k>

    rule <k> #loadCallSettings TXID:Int
          => #loadCallSettings {
               "from":     #unparseDataByteArray(#ecrecAddr(#sender(TN, TP, TG, TT, TV, #unparseByteStack(DATA), TW , TR, TS))),
               "to":       TT,
               "gas":      TG,
               "gasPrice": TP,
               "value":    TV,
               "data":     DATA
             }
         ...
         </k>
         <txPending> ListItem(TXID) ... </txPending>
         <message>
           <msgID>      TXID </msgID>
           <txNonce>    TN   </txNonce>
           <txGasPrice> TP   </txGasPrice>
           <txGasLimit> TG   </txGasLimit>
           <to>         TT   </to>
           <value>      TV   </value>
           <sigV>       TW   </sigV>
           <sigR>       TR   </sigR>
           <sigS>       TS   </sigS>
           <data>       DATA </data>
         </message>

    syntax ByteArray ::= #ecrecAddr ( Account ) [function]
 // ------------------------------------------------------
    rule #ecrecAddr(.Account) => .ByteArray
    rule #ecrecAddr(N:Int)    => #padToWidth(20, #asByteStack(N))
```

- `#executeTx` takes a transaction, loads it into the current state and executes it.
**TODO**: treat the account creation case
**TODO**: record the logs after `finalizeTX`
**TODO**: execute all pending transactions

```k
    syntax KItem ::= "#prepareTx" Int
 // ---------------------------------
    rule <k> #prepareTx TXID:Int
          => #clearLogs
          ~> #loadCallSettings TXID
          ~> #executeTx TXID
          ~> #makeTxReceipt TXID
         ...
         </k>


    syntax KItem ::= "#executeTx" Int
 // ---------------------------------
    rule <k> #executeTx TXID:Int
          => #create ACCTFROM #newAddr(ACCTFROM, NONCE) VALUE CODE
          ~> #catchHaltTx
          ~> #finalizeTx(false)
         ...
         </k>
         <origin> ACCTFROM </origin>
         <schedule> SCHED </schedule>
         <callGas> _ => GLIMIT -Int G0(SCHED, CODE, true) </callGas>
         <callDepth> _ => -1 </callDepth>
         <txPending> ListItem(TXID:Int) ... </txPending>
         <coinbase> MINER </coinbase>
         <message>
           <msgID>      TXID     </msgID>
           <txGasPrice> GPRICE   </txGasPrice>
           <txGasLimit> GLIMIT   </txGasLimit>
           <to>         .Account </to>
           <value>      VALUE    </value>
           <data>       CODE     </data>
           ...
         </message>
         <account>
           <acctID> ACCTFROM </acctID>
           <balance> BAL => BAL -Int (GLIMIT *Int GPRICE) </balance>
           <nonce> NONCE </nonce>
           ...
         </account>
         <touchedAccounts> _ => SetItem(MINER) </touchedAccounts>

    rule <k> #executeTx TXID:Int
          => #call ACCTFROM ACCTTO ACCTTO VALUE VALUE DATA false
          ~> #catchHaltTx
          ~> #finalizeTx(false)
         ...
         </k>
         <origin> ACCTFROM </origin>
         <txPending> ListItem(TXID) ... </txPending>
         <schedule> SCHED </schedule>
         <callGas> _ => GLIMIT -Int G0(SCHED, DATA, false) </callGas>
         <callDepth> _ => -1 </callDepth>
         <coinbase> MINER </coinbase>
         <message>
           <msgID>      TXID   </msgID>
           <txGasPrice> GPRICE </txGasPrice>
           <txGasLimit> GLIMIT </txGasLimit>
           <to>         ACCTTO </to>
           <value>      VALUE  </value>
           <data>       DATA   </data>
           ...
         </message>
         <account>
           <acctID> ACCTFROM </acctID>
           <balance> BAL => BAL -Int (GLIMIT *Int GPRICE) </balance>
           <nonce> NONCE => NONCE +Int 1 </nonce>
           ...
         </account>
         <touchedAccounts> _ => SetItem(MINER) </touchedAccounts>
      requires ACCTTO =/=K .Account

    syntax KItem ::= "#catchHaltTx"
 // -------------------------------
    rule <k> #halt ~> #catchHaltTx => . ... </k>

    syntax KItem ::= "#clearLogs"
 // -----------------------------
    rule <k> #clearLogs => . ... </k>
         <log> _ => .List </log>
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

    syntax KItem ::= "#firefly_addAccount" | "#firefly_addAccountByAddress" Int | "#firefly_addAccountByKey" String
 // ---------------------------------------------------------------------------------------------------------------
    rule <k> #firefly_addAccount => #firefly_addAccountByAddress #parseHexWord(#getString("address", J)) ... </k>
         <params> [ ({ _ } #as J), .JSONList ] </params>
      requires isString(#getJSON("address", J))

    rule <k> #firefly_addAccount => #firefly_addAccountByKey #getString("key", J) ... </k>
         <params> [ ({ _ } #as J), .JSONList ] </params>
      requires isString(#getJSON("key", J))

    rule <k> #firefly_addAccountByAddress ACCT_ADDR => #newAccount ACCT_ADDR ~> #loadAccountData ACCT_ADDR J ~> #sendResponse( "result": true ) ... </k>
         <params> [ ({ _ } #as J), .JSONList ] </params>
         <activeAccounts> ACCTS </activeAccounts>
      requires notBool ACCT_ADDR in ACCTS

    rule <k> #firefly_addAccountByAddress ACCT_ADDR => #sendResponse( "result": false ) ... </k>
         <params> [ ({ _ } #as J), .JSONList ] </params>
         <activeAccounts> ACCTS </activeAccounts>
      requires ACCT_ADDR in ACCTS

    rule <k> #firefly_addAccountByKey ACCT_KEY => #acctFromPrivateKey ACCT_KEY ~> #loadAccountData #addrFromPrivateKey(ACCT_KEY) J ~> #sendResponse( "result": true ) ... </k>
         <params> [ ({ _ } #as J), .JSONList ] </params>
         <activeAccounts> ACCTS </activeAccounts>
      requires notBool #addrFromPrivateKey(ACCT_KEY) in ACCTS

    rule <k> #firefly_addAccountByKey ACCT_KEY => #sendResponse( "result": false ) ... </k>
         <params> [ ({ _ } #as J), .JSONList ] </params>
          <activeAccounts> ACCTS </activeAccounts>
      requires #addrFromPrivateKey(ACCT_KEY) in ACCTS

    rule <k> #firefly_addAccount => #sendResponse( "error": {"code": -32025, "message":"Method 'firefly_addAccount' has invalid arguments"} ) ... </k> [owise]

    syntax KItem ::= "#loadAccountData" Int JSON
 // --------------------------------------------
    rule <k> #loadAccountData _ { .JSONList } => . ... </k>

    rule <k> #loadAccountData _ { "address": _, REST => REST } ... </k>
    rule <k> #loadAccountData _ { "key"    : _, REST => REST } ... </k>

    rule <k> #loadAccountData ACCTID { ("balance": BALANCE_STRING, REST) => REST } ... </k>
         <account>
           <acctID> ACCTID </acctID>
           <balance> _ => #parseHexWord(BALANCE_STRING) </balance>
           ...
         </account>

    rule <k> #loadAccountData ACCTID { ("code": CODE_STRING, REST) => REST } ... </k>
         <account>
           <acctID> ACCTID </acctID>
           <code> _ => #parseByteStack(CODE_STRING) </code>
           ...
         </account>

    rule <k> #loadAccountData ACCTID { ("nonce": NONCE_STRING, REST) => REST } ... </k>
         <account>
           <acctID> ACCTID </acctID>
           <nonce> _ => #parseHexWord(NONCE_STRING) </nonce>
           ...
         </account>

    rule <k> #loadAccountData ACCTID { ("storage": { STORAGE_JSON }, REST) => REST } ... </k>
         <account>
           <acctID> ACCTID </acctID>
           <storage>     _ => #parseMap({ STORAGE_JSON }) </storage>
           <origStorage> _ => #parseMap({ STORAGE_JSON }) </origStorage>
           ...
         </account>

    rule <k> #loadAccountData _ _ =>  #sendResponse( "error": {"code": -32026, "message":"Method 'firefly_addAccount' has invalid arguments"} ) ... </k> [owise]
```

- `#eth_call`
 **TODO**: add logic for the case in which "from" field is not present

```k
    syntax KItem ::= "#eth_call"
 // ----------------------------
    rule <k> #eth_call
          => #pushNetworkState
          ~> mkTX !ID:Int
          ~> #loadNonce #parseHexWord(#getString("from", J)) !ID
          ~> load "transaction" : { !ID : J }
          ~> signTX !ID #parseHexWord(#getString("from", J))
          ~> #prepareTx !ID
          ~> #eth_call_finalize
         ...
         </k>
         <params> [ ({ _ } #as J), TAG, .JSONList ] </params>
      requires isString( #getJSON("to", J) )
        andBool isString(#getJSON("from",J) )

    rule <k> #eth_call => #sendResponse( "error": {"code": -32027, "message":"Method 'eth_call' has invalid arguments"} ) ...  </k>
         <params> [ ({ _ } #as J), TAG, .JSONList ] </params>
      requires notBool isString( #getJSON("from", J) )

    syntax KItem ::= "#eth_call_finalize"
 // -------------------------------------
    rule <k> #eth_call_finalize => #popNetworkState ~> #sendResponse ("result": #unparseDataByteArray( OUTPUT )) ... </k>
         <output> OUTPUT </output>
endmodule
```
