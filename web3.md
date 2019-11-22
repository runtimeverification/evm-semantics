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
        <execPhase> .Phase </execPhase>
        <opcodeCoverage> .Map </opcodeCoverage>
        <opcodeLists> .Map </opcodeLists>
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
            <txID>            0          </txID>
            <sender>          .Account   </sender>
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

    syntax BlockchainItem ::= #getBlockByNumber ( BlockIdentifier , List ) [function]
 // ---------------------------------------------------------------------------------
    rule #getBlockByNumber( ( _:String => "pending" ) , .List) [owise]
    rule #getBlockByNumber( _:Int, .List) => .BlockchainItem
    rule #getBlockByNumber("earliest", _ ListItem( BLOCK )) => BLOCK
    rule #getBlockByNumber("latest", ListItem( BLOCK ) _) => BLOCK

    rule [[ #getBlockByNumber("pending",  BLOCKLIST) => {<network> NETWORK </network> | <block> BLOCK </block>} ]]
         <network> NETWORK </network>
         <block>   BLOCK   </block>

    rule #getBlockByNumber(BLOCKNUM:Int,  ListItem({ _ | <block> <number> BLOCKNUM </number> ... </block> } #as BLOCKCHAINITEM) REST ) => BLOCKCHAINITEM
    rule #getBlockByNumber(BLOCKNUM':Int, ListItem({ _ | <block> <number> BLOCKNUM </number> ... </block> }                   ) REST ) => #getBlockByNumber(BLOCKNUM', REST)
      requires BLOCKNUM =/=Int BLOCKNUM'

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
    rule <k> #getAccountAtBlock(BLOCKNUM , ACCTID) => #getAccountFromBlockchainItem(#getBlockByNumber(BLOCKNUM, BLOCKLIST), ACCTID) ... </k>
         <blockList> BLOCKLIST </blockList>

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
      requires CALLID =/=K undef

    rule <k> #sendResponse(_) ~> _ => #loadFromBatch </k>
         <callid> undef </callid>
         <batch> [ _ ] </batch>

    syntax Bool ::= isProperJson     ( JSON     ) [function]
                  | isProperJsonList ( JSONList ) [function]
 // --------------------------------------------------------
    rule isProperJson(_) => false [owise]

    rule isProperJson(null) => true

    rule isProperJson(_:Int)    => true
    rule isProperJson(_:Bool)   => true
    rule isProperJson(_:String) => true

    rule isProperJson(_:JSONKey : J) => isProperJson(J)

    rule isProperJson([ JS ]) => isProperJsonList(JS)
    rule isProperJson({ JS }) => isProperJsonList(JS)

    rule isProperJsonList(.JSONList) => true
    rule isProperJsonList(J, JS)     => isProperJson(J) andBool isProperJsonList(JS)

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
    rule <k> #runRPCCall => #eth_estimateGas ... </k>
         <method> "eth_estimateGas" </method>
    rule <k> #runRPCCall => #firefly_getCoverageData ... </k>
         <method> "firefly_getCoverageData" </method>
    rule <k> #runRPCCall => #firefly_getStateRoot ... </k>
         <method> "firefly_getStateRoot" </method>
    rule <k> #runRPCCall => #firefly_getTxRoot ... </k>
         <method> "firefly_getTxRoot" </method>
    rule <k> #runRPCCall => #firefly_getReceiptsRoot ... </k>
         <method> "firefly_getReceiptsRoot" </method>
    rule <k> #runRPCCall => #firefly_getTime ... </k>
         <method> "firefly_getTime" </method>
    rule <k> #runRPCCall => #firefly_setTime ... </k>
         <method> "firefly_setTime" </method>
    rule <k> #runRPCCall => #eth_getTransactionReceipt ... </k>
         <method> "eth_getTransactionReceipt" </method>
    rule <k> #runRPCCall => #eth_getBlockByNumber ... </k>
         <method> "eth_getBlockByNumber" </method>
    rule <k> #runRPCCall => #firefly_genesisBlock ... </k>
         <method> "firefly_genesisBlock" </method>
    rule <k> #runRPCCall => #evm_mine ... </k>
         <method> "evm_mine" </method>
    rule <k> #runRPCCall => #firefly_setGasLimit ... </k>
         <method> "firefly_setGasLimit" </method>

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
    rule <k> #eth_accounts => #sendResponse( "result" : [ #acctsToJArray( qsort(Set2List(ACCTS)) ) ] ) ... </k>
         <activeAccounts> ACCTS </activeAccounts>

    syntax JSONList ::= #acctsToJArray ( List ) [function]
 // ------------------------------------------------------
    rule #acctsToJArray( .List                       ) => .JSONList
    rule #acctsToJArray( ListItem( ACCT ) ACCTS:List ) => #unparseData( ACCT, 20 ), #acctsToJArray( ACCTS )

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

    syntax SnapshotItem ::= "{" BlockListCell "|" NetworkCell "|" BlockCell "|" TxReceiptsCell "}"
 // ----------------------------------------------------------------------------------------------

    syntax KItem ::= "#evm_snapshot"
 // --------------------------------
    rule <k> #evm_snapshot => #pushNetworkState ~> #sendResponse( "result" : #unparseQuantity( size ( SNAPSHOTS ) +Int 1 )) ... </k>
         <snapshots> SNAPSHOTS </snapshots>

    syntax KItem ::= "#pushNetworkState"
 // ------------------------------------
    rule <k> #pushNetworkState => . ... </k>
         <snapshots> ... (.List => ListItem({ <blockList> BLOCKLIST </blockList> | <network> NETWORK </network> | <block> BLOCK </block> | <txReceipts> RECEIPTS </txReceipts>})) </snapshots>
         <network>    NETWORK   </network>
         <block>      BLOCK     </block>
         <blockList>  BLOCKLIST </blockList>
         <txReceipts> RECEIPTS  </txReceipts>

    syntax KItem ::= "#popNetworkState"
 // -----------------------------------
    rule <k> #popNetworkState => . ... </k>
         <snapshots> ... ( ListItem({ <blockList> BLOCKLIST </blockList> | <network> NETWORK </network> | <block> BLOCK </block> | <txReceipts> RECEIPTS </txReceipts>}) => .List ) </snapshots>
         <network>    ( _ => NETWORK )   </network>
         <block>      ( _ => BLOCK )     </block>
         <blockList>  ( _ => BLOCKLIST ) </blockList>
         <txReceipts> ( _ => RECEIPTS )  </txReceipts>

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

    rule <k> #eth_sendTransaction_load J => mkTX !ID:Int ~> #loadNonce #parseHexWord( #getString("from",J) ) !ID ~> loadTransaction !ID J ~> signTX !ID #parseHexWord( #getString("from",J) ) ~> #prepareTx !ID #parseHexWord( #getString("from",J) ) ~> #eth_sendTransaction_final !ID ... </k>

    rule <k> #eth_sendTransaction_final TXID => #sendResponse( "result": "0x" +String #hashSignedTx( TXID ) ) ... </k>
        <statusCode> EVMC_SUCCESS </statusCode>

    rule <k> #eth_sendTransaction_final TXID => #sendResponse( "result": "0x" +String #hashSignedTx( TXID ) ) ... </k>
        <statusCode> EVMC_REVERT </statusCode>

    rule <k> #eth_sendTransaction_final TXID => #sendResponse( "error": {"code": -32000, "message": "base fee exceeds gas limit"} ) ... </k>
         <statusCode> EVMC_OUT_OF_GAS </statusCode>

    rule <k> #eth_sendTransaction_final TXID => #sendResponse( "error": {"code": -32000, "message":"sender doesn't have enough funds to send tx."} ) ... </k>
         <statusCode> EVMC_BALANCE_UNDERFLOW </statusCode>

    rule <k> #eth_sendTransaction_final TXID => #sendResponse( "error": { "code": -32000, "message": "VM exception: " +String StatusCode2String( SC ) } ) ... </k>
        <statusCode> SC:ExceptionalStatusCode </statusCode> [owise]

    rule <k> loadTransaction _ { "gas"      : (TG:String => #parseHexWord(TG)), _                 } ... </k>
    rule <k> loadTransaction _ { "gasPrice" : (TP:String => #parseHexWord(TP)), _                 } ... </k>
    rule <k> loadTransaction _ { "nonce"    : (TN:String => #parseHexWord(TN)), _                 } ... </k>
    rule <k> loadTransaction _ { "v"        : (TW:String => #parseHexWord(TW)), _                 } ... </k>
    rule <k> loadTransaction _ { "value"    : (TV:String => #parseHexWord(TV)), _                 } ... </k>
    rule <k> loadTransaction _ { "to"       : (TT:String => #parseHexWord(TT)), _                 } ... </k>
    rule <k> loadTransaction _ { "data"     : (TI:String => #parseByteStack(TI)), _               } ... </k>
    rule <k> loadTransaction _ { "r"        : (TR:String => #padToWidth(32, #parseByteStack(TR))), _ } ... </k>
    rule <k> loadTransaction _ { "s"        : (TS:String => #padToWidth(32, #parseByteStack(TS))), _ } ... </k>
    rule <k> loadTransaction _ { ("from"    : _, REST => REST) } ... </k>

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
    rule #hashSignedTx( TXID ) => Keccak256( #rlpEncodeTransaction( TXID ) )

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
          ~> loadTransaction !ID { "data"  : Raw2Hex(TI) , "gas"      : Raw2Hex(TG) , "gasPrice" : Raw2Hex(TP)
                                 , "nonce" : Raw2Hex(TN) , "r"        : Raw2Hex(TR) , "s"        : Raw2Hex(TS)
                                 , "to"    : Raw2Hex(TT) , "v"        : Raw2Hex(TW) , "value"    : Raw2Hex(TV)
                                 , .JSONList
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

Retrieving Blocks
-----------------

**TODO**
- <logsBloom> defaults to .ByteArray, but maybe it should be 256 zero bytes? It also doesn't get updated.
- Ganache's gasLimit defaults to 6721975 (0x6691b7), but we default it at 0.
- After each txExecution which is not `eth_call`:
   - use `#setBlockchainItem` 
   - clear <txPending> and <txOrder>
- Some initialization still needs to be done, like the trie roots and the 0 block in <blockList>
   - I foresee issues with firefly_addAccount and personal_importRawKey if we want those accounts
     in the stateRoot of the initial block

```k
    syntax KItem ::= "#eth_getBlockByNumber"
 // ----------------------------------------
    rule <k> #eth_getBlockByNumber => #eth_getBlockByNumber_finalize( #getBlockByNumber( #parseBlockIdentifier(TAG), BLOCKLIST)) ... </k>
         <params> [ TAG:String, TXOUT:Bool, .JSONList ] </params>
         <blockList> BLOCKLIST </blockList>
    rule <k> #eth_getBlockByNumber => #sendResponse ( "error": { "code":-32000, "message":"Incorrect number of arguments. Method 'eth_getBlockByNumber' requires exactly 2 arguments." } ) ... </k>
         <params> [ VALUE, .JSONList ] </params>
      requires notBool isJSONList( VALUE )

    rule <k> #eth_getBlockByNumber => #sendResponse ( "error": { "code":-32000, "message":"Incorrect number of arguments. Method 'eth_getBlockByNumber' requires exactly 2 arguments." } ) ... </k>
         <params> [ VALUE, VALUE2, _, .JSONList ] </params>
      requires notBool isJSONList( VALUE ) andBool notBool isJSONList( VALUE2 )

    syntax KItem ::= "#eth_getBlockByNumber_finalize" "(" BlockchainItem ")"
 // ------------------------------------------------------------------------
    rule <k> #eth_getBlockByNumber_finalize ({ _ |
         <block>
           <previousHash>      PARENTHASH  </previousHash>
           <ommersHash>        OMMERSHASH  </ommersHash>
           <coinbase>          MINER       </coinbase>
           <stateRoot>         STATEROOT   </stateRoot>
           <transactionsRoot>  TXROOT      </transactionsRoot>
           <receiptsRoot>      RCPTROOT    </receiptsRoot>
           <logsBloom>         LOGSBLOOM   </logsBloom> //#bloomFilter(<log> LOGS </>)
           <difficulty>        DFFCLTY     </difficulty>
           <number>            NUM         </number>
           <gasLimit>          GLIMIT      </gasLimit>
           <gasUsed>           GUSED       </gasUsed>
           <timestamp>         TIME        </timestamp>
           <extraData>         DATA        </extraData>
           <mixHash>           MIXHASH     </mixHash>
           <blockNonce>        NONCE       </blockNonce>
           ...
         </block> } #as BLOCKITEM)
          => #sendResponse ( "result":
             {
               "number": #unparseQuantity( NUM ),
               "hash": "0x" +String Keccak256( #rlpEncodeBlock( BLOCKITEM ) ),
               "parentHash": #unparseData( PARENTHASH, 32 ),
               "mixHash": #unparseData( MIXHASH, 32 ),
               "nonce": #unparseData( NONCE, 8 ),
               "sha3Uncles": #unparseData( OMMERSHASH, 32 ),
               "logsBloom": #unparseDataByteArray( LOGSBLOOM ),
               "transactionsRoot": #unparseData( TXROOT, 32),
               "stateRoot": #unparseData( STATEROOT, 32),
               "receiptsRoot": #unparseData( RCPTROOT, 32),
               "miner": #unparseData( MINER, 20 ),
               "difficulty": #unparseQuantity( DFFCLTY ),
               "totalDifficulty": #unparseQuantity( DFFCLTY ),
               "extraData": #unparseDataByteArray( DATA ),
               "size": "0x3e8", // Ganache always returns 1000
               "gasLimit": #unparseQuantity( GLIMIT ),
               "gasUsed": #unparseQuantity( GUSED ),
               "timestamp": #unparseQuantity( TIME ),
               "transactions": [ #getTransactionList( BLOCKITEM ) ],
               "uncles": [ .JSONList ]
             }
                           )
          ...
         </k>

    rule <k> #eth_getBlockByNumber_finalize ( .BlockchainItem )=> #sendResponse ( "result": null ) ... </k>

    syntax JSONList ::= "#getTransactionList" "(" BlockchainItem ")" [function]
                      | #getTransactionHashList ( List, JSONList ) [function]
 // ---------------------------------------------------------------------------
    rule [[ #getTransactionList ( { <network> <txOrder> TXIDLIST </txOrder> ... </network> | _ } )
         => #getTransactionHashList (TXIDLIST, .JSONList)
         ]]
         <params> [ _ , false, .JSONList ] </params>

    rule #getTransactionHashList ( .List, RESULT ) => RESULT
    rule [[ #getTransactionHashList ( ( ListItem(TXID) => .List ) TXIDLIST, ( RESULT => TXHASH, RESULT ) ) ]]
         <txReceipt>
           <txID>   TXID   </txID>
           <txHash> TXHASH </txHash>
           ...
         </txReceipt>
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
               <txID> TXID </txID>
               <sender> #parseHexWord(#unparseDataByteArray(#ecrecAddr(#sender(TN, TP, TG, TT, TV, #unparseByteStack(DATA), TW , TR, TS)))) </sender>
             </txReceipt>
           )
           ...
         </txReceipts>
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
         <statusCode> STATUSCODE </statusCode>
         <gasUsed> CGAS </gasUsed>
         <log> LOGS </log>

    syntax KItem ::= "#eth_getTransactionReceipt"
 // ---------------------------------------------
    rule <k> #eth_getTransactionReceipt => #sendResponse( "result": {
                                                                     "transactionHash": TXHASH,
                                                                     "transactionIndex": #unparseQuantity(getIndexOf(TXID, TXLIST)),
                                                                     "blockHash": #unparseQuantity(1),
                                                                     "blockNumber": #unparseQuantity(BN),
                                                                     "from": #unparseQuantity(TXFROM),
                                                                     "to": #unparseAccount(TT),
                                                                     "gasUsed": #unparseQuantity(CGAS),
                                                                     "cumulativeGasUsed": #unparseQuantity(CGAS),
                                                                     "contractAddress": #if TT ==K .Account #then #unparseQuantity(#newAddr(TXFROM, NONCE -Int 1)) #else null #fi,
                                                                     "logs": [#serializeLogs(LOGS, 0, TXID, TXHASH, BN, 1)],
                                                                     "status": #unparseQuantity(TXSTATUS),
                                                                     "logsBloom": #unparseDataByteArray(BLOOM),
                                                                     "v": #unparseQuantity(TW),
                                                                     "r": #unparseDataByteArray(TR),
                                                                     "s": #unparseDataByteArray(TS)
                                                                     }) ... </k>
         <params> [TXHASH:String, .JSONList] </params>
         <txReceipt>
           <txHash>          TXHASH </txHash>
           <txID>            TXID </txID>
           <txCumulativeGas> CGAS </txCumulativeGas>
           <logSet>          LOGS </logSet>
           <bloomFilter>     BLOOM </bloomFilter>
           <txStatus>        TXSTATUS </txStatus>
           <sender>          TXFROM </sender>
         </txReceipt>
         <number>  BN     </number>
         <txOrder> TXLIST </txOrder>
         <message>
           <msgID>      TXID     </msgID>
           <txNonce>    TN       </txNonce>
           <to>         TT:Account </to>
           <sigV>       TW       </sigV>
           <sigR>       TR       </sigR>
           <sigS>       TS       </sigS>
           ...
         </message>
         <account>
           <acctID> TXFROM </acctID>
           <nonce>  NONCE  </nonce>
           ...
         </account>
         <log> LOGS </log>

    rule <k> #eth_getTransactionReceipt => #sendResponse( "result": null ) ... </k> [owise]

    syntax Int ::= getIndexOf ( Int, List ) [function]
 // --------------------------------------------------
    rule getIndexOf(X:Int, L) => getIndexOfAux(X:Int, L, 0)

    syntax Int ::= getIndexOfAux (Int, List, Int) [function]
 // --------------------------------------------------------
    rule getIndexOfAux (X:Int, .List,         _:Int) => -1
    rule getIndexOfAux (X:Int, ListItem(X) L, INDEX) => INDEX
    rule getIndexOfAux (X:Int, ListItem(I) L, INDEX) => getIndexOfAux(X, L, INDEX +Int 1) requires X =/=Int I

    syntax JSON ::= #unparseAccount ( Account ) [function]
 // ------------------------------------------------------
    rule #unparseAccount (.Account) => null
    rule #unparseAccount (ACCT:Int) => #unparseQuantity(ACCT)

    syntax JSONList ::= #unparseIntList ( List ) [function]
 // -------------------------------------------------------
    rule #unparseIntList (L) => #unparseIntListAux( L, .JSONList)

    syntax JSONList ::= #unparseIntListAux ( List, JSONList ) [function]
 // --------------------------------------------------------------------
    rule #unparseIntListAux(.List, RESULT) => RESULT
    rule #unparseIntListAux(L ListItem(I), RESULT) => #unparseIntListAux(L, (#unparseQuantity(I), RESULT))

    syntax JSONList ::= #serializeLogs ( List, Int, Int, String, Int, Int ) [function]
 // ----------------------------------------------------------------------------------
    rule #serializeLogs (.List, _, _, _, _, _)  => .JSONList
    rule #serializeLogs (ListItem({ ACCT | TOPICS:List | DATA }) L, LI, TI, TH, BH, BN) => {
                                                                         "logIndex": #unparseQuantity(LI),
                                                                         "transactionIndex": #unparseQuantity(TI),
                                                                         "transactionHash": TH,
                                                                         "blockHash": #unparseQuantity(BH),
                                                                         "blockNumber": #unparseQuantity(BN),
                                                                         "address": #unparseQuantity(ACCT),
                                                                         "data": #unparseDataByteArray(DATA),
                                                                         "topics": [#unparseIntList(TOPICS)],
                                                                         "type" : "mined"
                                                                                           }, #serializeLogs(L, LI +Int 1, TI, TH, BH, BN)
```

- loadCallState: web3.md specific rules

```k
    rule <k> loadCallState { "from" : ( ACCTFROM:String => #parseHexWord( ACCTFROM ) ), REST } ... </k>
    rule <k> loadCallState { "to" : ( ACCTTO:String => #parseHexWord( ACCTTO ) ), REST } ... </k>
    rule <k> loadCallState { "gas" : ( GLIMIT:String => #parseHexWord( GLIMIT ) ), REST } ... </k>
    rule <k> loadCallState { "gasPrice" : ( GPRICE:String => #parseHexWord( GPRICE ) ), REST } ... </k>
    rule <k> loadCallState { "value" : ( VALUE:String => #parseHexWord( VALUE ) ), REST } ... </k>
    rule <k> loadCallState { "nonce" : _, REST => REST } ... </k>

    rule <k> loadCallState { "from" : ACCTFROM:Int, REST => REST } ... </k>
         <caller> _ => ACCTFROM </caller>
         <origin> _ => ACCTFROM </origin>

    rule <k> loadCallState { "to" : .Account   , REST => REST } ... </k>
    rule <k> loadCallState { ("to" : ACCTTO:Int => "code" : CODE), REST } ... </k>
         <id> _ => ACCTTO </id>
         <account>
           <acctID> ACCTTO </acctID>
           <code> CODE </code>
           ...
         </account>

    rule <k> ( . => #newAccount ACCTTO ) ~> loadCallState { "to" : ACCTTO:Int, REST } ... </k> [owise]

    rule <k> loadCallState TXID:Int
          => loadCallState {
               "from":     #unparseDataByteArray(#ecrecAddr(#sender(TN, TP, TG, TT, TV, #unparseByteStack(DATA), TW , TR, TS))),
               "to":       TT,
               "gas":      TG,
               "gasPrice": TP,
               "value":    TV,
               "data":     DATA
             }
         ...
         </k>
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
    syntax KItem ::= "#prepareTx" Int Account
 // -----------------------------------------
    rule <k> #prepareTx TXID:Int ACCTFROM
          => #clearLogs
          ~> #validateTx TXID
         ...
         </k>
         <origin> _ => ACCTFROM </origin>

    syntax KItem ::= "#validateTx" Int
 // ----------------------------------
    rule <k> #validateTx TXID => . ... </k>
         <statusCode> ( _ => EVMC_OUT_OF_GAS) </statusCode>
         <schedule> SCHED </schedule>
         <message>
           <msgID>      TXID   </msgID>
           <txGasLimit> GLIMIT </txGasLimit>
           <data>       DATA   </data>
           <to>         ACCTTO </to>
           ...
         </message>
      requires ( GLIMIT -Int G0(SCHED, DATA, (ACCTTO ==K .Account)) ) <Int 0

    rule <k> #validateTx TXID => #executeTx TXID ~> #makeTxReceipt TXID ~> #finishTx ... </k>
         <schedule> SCHED </schedule>
         <callGas> _ => GLIMIT -Int G0(SCHED, DATA, (ACCTTO ==K .Account) ) </callGas>
         <message>
           <msgID>      TXID   </msgID>
           <txGasLimit> GLIMIT </txGasLimit>
           <data>       DATA   </data>
           <to>         ACCTTO </to>
           ...
         </message>
      requires ( GLIMIT -Int G0(SCHED, DATA, (ACCTTO ==K .Account)) ) >=Int 0

    syntax KItem ::= "#executeTx" Int
 // ---------------------------------
    rule <k> #executeTx TXID:Int
          => #create ACCTFROM #newAddr(ACCTFROM, NONCE) VALUE CODE
          ~> #catchHaltTx #newAddr(ACCTFROM, NONCE)
          ~> #finalizeTx(false)
         ...
         </k>
         <gasPrice> _ => GPRICE </gasPrice>
         <origin> ACCTFROM </origin>
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
          ~> #catchHaltTx .Account
          ~> #finalizeTx(false)
         ...
         </k>
         <origin> ACCTFROM </origin>
         <gasPrice> _ => GPRICE </gasPrice>
         <txPending> ListItem(TXID) ... </txPending>
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

    syntax KItem ::= "#finishTx"
 // ----------------------------
    rule <statusCode> STATUSCODE </statusCode>
         <k> #finishTx => #mineBlock ... </k>
         <mode> EXECMODE </mode>
      requires EXECMODE =/=K NOGAS
       andBool ( STATUSCODE ==K EVMC_SUCCESS orBool STATUSCODE ==K EVMC_REVERT )

    rule <k> #finishTx => #clearGas ... </k> [owise]

    syntax KItem ::= "#catchHaltTx" Account
 // ---------------------------------------
    rule <statusCode> _:ExceptionalStatusCode </statusCode>
         <k> #halt ~> #catchHaltTx _ => #popCallStack ~> #popWorldState ... </k>

    rule <statusCode> EVMC_REVERT </statusCode>
         <k> #halt ~> #catchHaltTx _ => #popCallStack ~> #popWorldState ~> #refund GAVAIL ... </k>
         <gas> GAVAIL </gas>

    rule <statusCode> EVMC_SUCCESS </statusCode>
         <k> #halt ~> #catchHaltTx .Account => . ... </k>

    rule <statusCode> EVMC_SUCCESS </statusCode>
         <k> #halt ~> #catchHaltTx ACCT => #mkCodeDeposit ACCT ... </k>
      requires ACCT =/=K .Account

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

    rule <k> #firefly_addAccountByAddress ACCT_ADDR => #newAccount ACCT_ADDR ~> loadAccount ACCT_ADDR J ~> #sendResponse( "result": true ) ... </k>
         <params> [ ({ _ } #as J), .JSONList ] </params>
         <activeAccounts> ACCTS </activeAccounts>
      requires notBool ACCT_ADDR in ACCTS

    rule <k> #firefly_addAccountByAddress ACCT_ADDR => #sendResponse( "result": false ) ... </k>
         <params> [ ({ _ } #as J), .JSONList ] </params>
         <activeAccounts> ACCTS </activeAccounts>
      requires ACCT_ADDR in ACCTS

    rule <k> #firefly_addAccountByKey ACCT_KEY => #acctFromPrivateKey ACCT_KEY ~> loadAccount #addrFromPrivateKey(ACCT_KEY) J ~> #sendResponse( "result": true ) ... </k>
         <params> [ ({ _ } #as J), .JSONList ] </params>
         <activeAccounts> ACCTS </activeAccounts>
      requires notBool #addrFromPrivateKey(ACCT_KEY) in ACCTS

    rule <k> #firefly_addAccountByKey ACCT_KEY => #sendResponse( "result": false ) ... </k>
         <params> [ ({ _ } #as J), .JSONList ] </params>
          <activeAccounts> ACCTS </activeAccounts>
      requires #addrFromPrivateKey(ACCT_KEY) in ACCTS

    rule <k> #firefly_addAccount => #sendResponse( "error": {"code": -32025, "message":"Method 'firefly_addAccount' has invalid arguments"} ) ... </k> [owise]

    rule <k> loadAccount _ { "balance" : ((VAL:String)         => #parseHexWord(VAL)),     _ } ... </k>
    rule <k> loadAccount _ { "nonce"   : ((VAL:String)         => #parseHexWord(VAL)),     _ } ... </k>
    rule <k> loadAccount _ { "code"    : ((CODE:String)        => #parseByteStack(CODE)),  _ } ... </k>
    rule <k> loadAccount _ { "storage" : ({ STORAGE:JSONList } => #parseMap({ STORAGE })), _ } ... </k>
    rule <k> loadAccount _ { "key" : _, REST => REST } ... </k>
    rule <k> loadAccount _ { "address" : _, REST => REST } ... </k>
```

- `#eth_call`
 **TODO**: add logic for the case in which "from" field is not present

```k
    syntax KItem ::= "#eth_call"
 // ----------------------------
    rule <k> #eth_call
          => #pushNetworkState
          ~> #setMode NOGAS
          ~> mkTX !ID:Int
          ~> #loadNonce #parseHexWord(#getString("from", J)) !ID
          ~> loadTransaction !ID J
          ~> signTX !ID #parseHexWord(#getString("from", J))
          ~> #prepareTx !ID #parseHexWord(#getString("from", J))
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
    rule <k> #eth_call_finalize => #setMode NORMAL ~> #popNetworkState ~> #sendResponse ("result": #unparseDataByteArray( OUTPUT )) ... </k>
         <output> OUTPUT </output>
```

- `#eth_estimateGas`
**TODO**: add test for EVMC_OUT_OF_GAS
**TODO**: implement funcionality for block number argument

```k
    syntax KItem ::= "#eth_estimateGas"
 // -----------------------------------
    rule <k> #eth_estimateGas
          => #pushNetworkState
          ~> mkTX !ID:Int
          ~> #loadNonce #parseHexWord(#getString("from", J)) !ID
          ~> loadTransaction !ID J
          ~> signTX !ID #parseHexWord(#getString("from", J))
          ~> #prepareTx !ID #parseHexWord(#getString("from", J))
          ~> #eth_estimateGas_finalize GUSED
         ...
         </k>
         <params> [ ({ _ } #as J), TAG, .JSONList ] </params>
         <gasUsed>  GUSED  </gasUsed>
      requires isString(#getJSON("from", J) )

    rule <k> #eth_estimateGas => #sendResponse( "error": {"code": -32028, "message":"Method 'eth_estimateGas' has invalid arguments"} ) ...  </k>
         <params> [ ({ _ } #as J), TAG, .JSONList ] </params>
      requires notBool isString( #getJSON("from", J) )

    syntax KItem ::= "#eth_estimateGas_finalize" Int
 // ------------------------------------------------
    rule <k> #eth_estimateGas_finalize INITGUSED:Int => #popNetworkState ~> #sendResponse ("result": #unparseQuantity( #getGasUsed( #getBlockByNumber( "latest", BLOCKLIST ) ) -Int INITGUSED )) ... </k>
         <statusCode> STATUSCODE </statusCode>
         <blockList> BLOCKLIST </blockList>
      requires STATUSCODE =/=K EVMC_OUT_OF_GAS

    rule <k> #eth_estimateGas_finalize _ => #popNetworkState ~> #sendResponse ( "error": {"code": -32000, "message":"base fee exceeds gas limit"}) ... </k>
         <statusCode> EVMC_OUT_OF_GAS </statusCode>

    syntax Int ::= #getGasUsed( BlockchainItem ) [function]
 // -------------------------------------------------------
    rule #getGasUsed( { _ | <block> <gasUsed> GUSED </gasUsed> ... </block> } ) => GUSED
```

NOGAS Mode
----------

- Used for `eth_call` RPC messages

```k
    syntax Mode ::= "NOGAS"
 // -----------------------
    rule <k> #gas [ OP , AOP ] => . ... </k>
         <mode> NOGAS </mode>
     [priority(25)]

    rule <k> #validateTx TXID => #executeTx TXID ~> #makeTxReceipt TXID ... </k>
         <mode> NOGAS </mode>
     [priority(25)]
```

Collecting Coverage Data
------------------------

- `<execPhase>` cell is used to differentiate between the generated code used for contract deployment and the bytecode of the contract.
- `<opcodeCoverage>` cell is a map which stores the program counters which were hit during the execution of a program. The key, named `CoverageIdentifier`, contains the hash of the bytecode which is executed, and the phase of the execution.
- `<opcodeLists>` cell is a map similar to `<opcodeCoverage>` which stores instead a list containing all the `OpcodeItem`s of the executed bytecode for each contract.
- `OpcodeItem` is a tuple which contains the Program Counter and the Opcode name.

**TODO**: instead of having both `#serializeCoverage` and `#serializePrograms` we could keep only the first rule as `#serializeCoverageMap` if `<opcodeLists>` would store `Sets` instead of `Lists`.
**TODO**: compute coverage percentages in `Float` instead of `Int`
**TODO**: `Set2List` won't return `ListItems` in order, causing tests to fail.

```k
    syntax Phase ::= ".Phase"
                   | "CONSTRUCTOR"
                   | "RUNTIME"

    syntax CoverageIdentifier ::= "{" Int "|" Phase "}"

    rule <k> #mkCall _ _ _ _ _ _ _ ... </k>
         <execPhase> ( EPHASE => RUNTIME ) </execPhase>
      requires EPHASE =/=K RUNTIME
      [priority(25)]

    rule <k> #mkCreate _ _ _ _ ... </k>
         <execPhase> ( EPHASE => CONSTRUCTOR ) </execPhase>
      requires EPHASE =/=K CONSTRUCTOR
      [priority(25)]

    rule <k> #initVM ... </k>
         <opcodeCoverage> OC => OC [ {keccak(PGM) | EPHASE} <- .Set ] </opcodeCoverage>
         <execPhase> EPHASE </execPhase>
         <program> PGM </program>
      requires notBool {keccak(PGM) | EPHASE} in_keys(OC)
      [priority(25)]


    rule <k> #initVM ... </k>
         <opcodeLists> OL => OL [ {keccak(PGM) | EPHASE} <- #parseByteCode(PGM,SCHED) ] </opcodeLists>
         <execPhase> EPHASE </execPhase>
         <schedule> SCHED </schedule>
         <program> PGM </program>
      requires notBool {keccak(PGM) | EPHASE} in_keys(OL)
      [priority(25)]

    syntax OpcodeItem ::= "{" Int "|" OpCode "}"

    syntax List ::= #parseByteCode( ByteArray, Schedule ) [function]
 // ----------------------------------------------------------------
    rule #parseByteCode(PGM , SCHED) => #parseByteCodeAux(0, #sizeByteArray(PGM), PGM, SCHED, .List)

    syntax List ::= #parseByteCodeAux ( Int, Int, ByteArray, Schedule, List ) [function]
 // ------------------------------------------------------------------------------------
    rule #parseByteCodeAux(PCOUNT, SIZE, _, _, OPLIST) => OPLIST
      requires PCOUNT >=Int SIZE
    rule #parseByteCodeAux(PCOUNT, SIZE, PGM, SCHED, OPLIST) => #parseByteCodeAux(PCOUNT +Int #widthOp(#dasmOpCode(PGM [ PCOUNT ], SCHED)), SIZE, PGM, SCHED, OPLIST ListItem({ PCOUNT | #dasmOpCode(PGM [ PCOUNT ], SCHED) } ) )
      requires PCOUNT <Int SIZE

    rule <k> #execute ... </k>
         <pc> PCOUNT </pc>
         <execPhase> EPHASE </execPhase>
         <program> PGM </program>
         <opcodeCoverage> ... { keccak(PGM) | EPHASE } |-> (PCS (.Set => SetItem(PCOUNT))) ... </opcodeCoverage>
      requires notBool PCOUNT in PCS
      [priority(25)]

    syntax KItem ::= "#firefly_getCoverageData"
 // -------------------------------------------
    rule <k> #firefly_getCoverageData => #sendResponse ("result": #makeCoverageReport(COVERAGE, PGMS)) ... </k>
         <opcodeCoverage> COVERAGE </opcodeCoverage>
         <opcodeLists>    PGMS     </opcodeLists>

    syntax JSON ::= #makeCoverageReport ( Map, Map ) [function]
 // -----------------------------------------------------------
    rule #makeCoverageReport (COVERAGE, PGMS) => {
                                                  "coverages": [#coveragePercentages(keys_list(PGMS),COVERAGE,PGMS)],
                                                  "coveredOpcodes": [#serializeCoverage(keys_list(COVERAGE),COVERAGE)],
                                                  "programs": [#serializePrograms(keys_list(PGMS),PGMS)] 
                                                 }

    syntax JSONList ::= #serializeCoverage ( List, Map ) [function]
 // ---------------------------------------------------------------
    rule #serializeCoverage (.List, _ ) => .JSONList
    rule #serializeCoverage ((ListItem({ CODEHASH | EPHASE } #as KEY) KEYS), KEY |-> X:Set COVERAGE:Map ) => { Int2String(CODEHASH):{ Phase2String(EPHASE): [IntList2JSONList(qsort(Set2List(X)))] }}, #serializeCoverage(KEYS, COVERAGE)

    syntax JSONList ::= #serializePrograms ( List, Map ) [function]
 // ---------------------------------------------------------------
    rule #serializePrograms (.List, _ ) => .JSONList
    rule #serializePrograms ((ListItem({ CODEHASH | EPHASE } #as KEY) KEYS), KEY |-> X:List PGMS:Map ) => { Int2String(CODEHASH):{ Phase2String(EPHASE): [CoverageIDList2JSONList(X)] }}, #serializePrograms(KEYS, PGMS)

    syntax String ::= Phase2String ( Phase ) [function]
 // ----------------------------------------------------
    rule Phase2String (CONSTRUCTOR) => "CONSTRUCTOR"
    rule Phase2String (RUNTIME)     => "RUNTIME"

    syntax JSONList ::= CoverageIDList2JSONList ( List ) [function]
 // ---------------------------------------------------------------
    rule CoverageIDList2JSONList (.List)                           => .JSONList
    rule CoverageIDList2JSONList (ListItem({I:Int | _:OpCode }) L) => I, CoverageIDList2JSONList(L)

    syntax JSONList ::= IntList2JSONList ( List ) [function]
 // --------------------------------------------------------
    rule IntList2JSONList (.List)             => .JSONList
    rule IntList2JSONList (ListItem(I:Int) L) => I, IntList2JSONList(L)

    syntax List ::= getIntElementsSmallerThan ( Int, List, List ) [function]
 // ------------------------------------------------------------------------
    rule getIntElementsSmallerThan (_, .List,               RESULTS) => RESULTS
    rule getIntElementsSmallerThan (X, (ListItem(I:Int) L), RESULTS) => getIntElementsSmallerThan (X, L, ListItem(I) RESULTS) requires I  <Int X
    rule getIntElementsSmallerThan (X, (ListItem(I:Int) L), RESULTS) => getIntElementsSmallerThan (X, L, RESULTS)             requires I >=Int X

    syntax List ::= getIntElementsGreaterThan ( Int, List, List ) [function]
 // ------------------------------------------------------------------------
    rule getIntElementsGreaterThan (_, .List ,              RESULTS) => RESULTS
    rule getIntElementsGreaterThan (X, (ListItem(I:Int) L), RESULTS) => getIntElementsGreaterThan (X, L, ListItem(I) RESULTS) requires I  >Int X
    rule getIntElementsGreaterThan (X, (ListItem(I:Int) L), RESULTS) => getIntElementsGreaterThan (X, L, RESULTS)             requires I <=Int X

    syntax List ::= qsort ( List ) [function]
 // -----------------------------------------
    rule qsort ( .List )           => .List
    rule qsort (ListItem(I:Int) L) => qsort(getIntElementsSmallerThan(I, L, .List)) ListItem(I) qsort(getIntElementsGreaterThan(I, L, .List))

    syntax JSONList ::= #coveragePercentages ( List, Map, Map) [function]
 // ---------------------------------------------------------------------
    rule #coveragePercentages (.List, _, _) => .JSONList
    rule #coveragePercentages ((ListItem({ CODEHASH | EPHASE } #as KEY) KEYS), KEY |-> X:Set COVERAGE:Map, KEY |-> Y:List PGMS:Map) => { Int2String(CODEHASH):{ Phase2String(EPHASE): #computePercentage(size(X),size(Y)) }}, #coveragePercentages(KEYS,COVERAGE,PGMS)

    syntax Int ::= #computePercentage ( Int, Int ) [function]
 // ---------------------------------------------------------
    rule #computePercentage (EXECUTED, TOTAL) => (100 *Int EXECUTED) /Int TOTAL
```

Helper Funcs
------------

```k
    syntax AccountData ::= #getAcctData( Account ) [function]
 // ---------------------------------------------------------
    rule [[ #getAcctData( ACCT ) => AcctData(NONCE, BAL, STORAGE, CODE) ]]
         <account>
           <acctID>  ACCT    </acctID>
           <nonce>   NONCE   </nonce>
           <balance> BAL     </balance>
           <storage> STORAGE </storage>
           <code>    CODE    </code>
           ...
         </account>

    syntax String ::= #rlpEncodeBlock( BlockchainItem ) [function]
 // --------------------------------------------------------------
    rule #rlpEncodeBlock( { _ |
         <block>
           <previousHash>      PARENTHASH  </previousHash>
           <ommersHash>        OMMERSHASH  </ommersHash>
           <coinbase>          MINER       </coinbase>
           <stateRoot>         STATEROOT   </stateRoot>
           <transactionsRoot>  TXROOT      </transactionsRoot>
           <receiptsRoot>      RCPTROOT    </receiptsRoot>
           <logsBloom>         LOGSBLOOM   </logsBloom>
           <difficulty>        DFFCLTY     </difficulty>
           <number>            NUM         </number>
           <gasLimit>          GLIMIT      </gasLimit>
           <gasUsed>           GUSED       </gasUsed>
           <timestamp>         TIME        </timestamp>
           <extraData>         DATA        </extraData>
           <mixHash>           MIXHASH     </mixHash>
           <blockNonce>        NONCE       </blockNonce>
           ...
         </block> } )
         => #rlpEncodeLength(         #rlpEncodeBytes( PARENTHASH, 32 )
                              +String #rlpEncodeBytes( OMMERSHASH, 32 )
                              +String #rlpEncodeBytes( MINER, 20 )
                              +String #rlpEncodeBytes( STATEROOT, 32 )
                              +String #rlpEncodeBytes( TXROOT, 32 )
                              +String #rlpEncodeBytes( RCPTROOT, 32 )
                              +String #rlpEncodeBytes( #asInteger( LOGSBLOOM ), 256 )
                              +String #rlpEncodeWord ( DFFCLTY )
                              +String #rlpEncodeWord ( NUM )
                              +String #rlpEncodeWord ( GLIMIT )
                              +String #rlpEncodeWord ( GUSED )
                              +String #rlpEncodeWord ( TIME )
                              +String #rlpEncodeBytes( #asInteger( DATA ), #sizeByteArray( DATA ) )
                              +String #rlpEncodeBytes( MIXHASH, 32 )
                              +String #rlpEncodeBytes( NONCE, 8 )
                            , 192
                            )

    syntax String ::= #rlpEncodeTransaction( Int ) [function]
 // ---------------------------------------------------------
    rule [[ #rlpEncodeTransaction( TXID )
         => #rlpEncodeLength(         #rlpEncodeWord( TXNONCE )
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

    syntax String ::= #rlpEncodeReceipt( Int )       [function]
                    | #rlpEncodeReceiptAux( String ) [function]
 // -----------------------------------------------------------
    rule #rlpEncodeReceipt( I ) => #rlpEncodeReceiptAux( "0x" +String #hashSignedTx( I ) )
    rule [[ #rlpEncodeReceiptAux( TXHASH ) =>
            #rlpEncodeLength(         #rlpEncodeWord( STATUS )
                              +String #rlpEncodeWord( CGAS )
                              +String #rlpEncodeString( #asString( BLOOM ) )
                              +String #rlpEncodeLogs( LOGS )
                            , 192
                            )
         ]]
         <txReceipt>
           <txHash> TXHASH </txHash>
           <txCumulativeGas> CGAS   </txCumulativeGas>
           <logSet>          LOGS   </logSet>
           <bloomFilter>     BLOOM  </bloomFilter>
           <txStatus>        STATUS </txStatus>
           ...
         </txReceipt>

    syntax String ::= #rlpEncodeLogs   ( List ) [function]
                    | #rlpEncodeLogsAux( List ) [function]
 // ------------------------------------------------------
    rule #rlpEncodeLogs( .List ) => "\xc0"
    rule #rlpEncodeLogs( LOGS )  => #rlpEncodeLength( #rlpEncodeLogsAux( LOGS ), 192 )
      requires LOGS =/=K .List

    rule #rlpEncodeLogsAux( .List ) => ""
    rule #rlpEncodeLogsAux( ListItem({ ACCT | TOPICS | DATA }) LOGS )
      => #rlpEncodeLength(         #rlpEncodeBytes( ACCT, 20 )
                           +String #rlpEncodeTopics( TOPICS )
                           +String #rlpEncodeString( #asString( DATA ) )
                         , 192 )
         +String #rlpEncodeLogsAux( LOGS )

    syntax String ::= #rlpEncodeTopics   ( List ) [function]
                    | #rlpEncodeTopicsAux( List ) [function]
 // --------------------------------------------------------
    rule #rlpEncodeTopics( .List )  => "\xc0"
    rule #rlpEncodeTopics( TOPICS ) => #rlpEncodeLength( #rlpEncodeTopicsAux( TOPICS ), 192 )
      requires TOPICS =/=K .List

    rule #rlpEncodeTopicsAux( .List ) => ""
    rule #rlpEncodeTopicsAux( ListItem( X:Int ) TOPICS ) => #rlpEncodeWord( X ) +String #rlpEncodeTopicsAux( TOPICS )
```

State Root
----------

```k
    syntax MerkleTree ::= "#stateRoot" [function]
 // ---------------------------------------------
    rule #stateRoot => MerkleUpdateMap( .MerkleTree, #precompiledContracts #activeAccounts )

    syntax Map ::= "#activeAccounts"   [function]
                 | #accountsMap( Set ) [function]
 // ---------------------------------------------
    rule [[ #activeAccounts => #accountsMap( ACCTS ) ]]
         <activeAccounts> ACCTS </activeAccounts>

    rule #accountsMap( .Set ) => .Map
    rule #accountsMap( SetItem( ACCT:Int ) S ) => #parseByteStack( #unparseData( ACCT, 20 ) ) |-> #rlpEncodeFullAccount( #getAcctData( ACCT ) ) #accountsMap( S )

    syntax KItem ::= "#firefly_getStateRoot"
 // ----------------------------------------
    rule <k> #firefly_getStateRoot => #sendResponse("result": { "stateRoot" : "0x" +String Keccak256( #rlpEncodeMerkleTree( #stateRoot ) ) } ) ... </k>
```

Transactions Root
-----------------

```k
    syntax MerkleTree ::= "#transactionsRoot" [function]
 // ----------------------------------------------------
    rule #transactionsRoot => MerkleUpdateMap( .MerkleTree, #transactionsMap )

    syntax Map ::= "#transactionsMap"         [function]
                 | #transactionsMapAux( Int ) [function]
 // ----------------------------------------------------
    rule #transactionsMap => #transactionsMapAux( 0 )

    rule #transactionsMapAux( _ )    => .Map [owise]
    rule [[ #transactionsMapAux( I ) => #parseByteStackRaw( #rlpEncodeWord( I ) )[0 .. 1] |-> #rlpEncodeTransaction( { TXLIST[ I ] }:>Int ) #transactionsMapAux( I +Int 1 ) ]]
         <txOrder> TXLIST </txOrder>
      requires size(TXLIST) >Int I

    syntax KItem ::= "#firefly_getTxRoot"
 // -------------------------------------
    rule <k> #firefly_getTxRoot => #sendResponse("result": { "transactionsRoot" : #getTxRoot( #getBlockByNumber( "latest", BLOCKLIST ) ) } ) ... </k>
         <blockList> BLOCKLIST </blockList>

    syntax String ::= #getTxRoot( BlockchainItem ) [function]
 // ---------------------------------------------------------
    rule #getTxRoot( { _ | <block> <transactionsRoot> TXROOT </transactionsRoot> ... </block> } ) => #unparseData( TXROOT, 32 )
```

Receipts Root
-------------

```k
    syntax MerkleTree ::= "#receiptsRoot" [function]
 // ------------------------------------------------
    rule #receiptsRoot => MerkleUpdateMap( .MerkleTree, #receiptsMap )

    syntax Map ::= "#receiptsMap"         [function]
                 | #receiptsMapAux( Int ) [function]
 // ------------------------------------------------
    rule #receiptsMap => #receiptsMapAux( 0 )

    rule    #receiptsMapAux( _ ) => .Map [owise]
    rule [[ #receiptsMapAux( I ) => #parseByteStackRaw( #rlpEncodeWord( I ) )[0 .. 1] |-> #rlpEncodeReceipt( { TXLIST[ I ] }:>Int ) #receiptsMapAux( I +Int 1 ) ]]
         <txOrder> TXLIST </txOrder>
      requires size(TXLIST) >Int I

    syntax KItem ::= "#firefly_getReceiptsRoot"
 // -------------------------------------------
    rule <k> #firefly_getReceiptsRoot => #sendResponse("result": { "receiptsRoot" : #getReceiptRoot( #getBlockByNumber( "latest", BLOCKLIST ) ) } ) ... </k>
         <blockList> BLOCKLIST </blockList>

    syntax String ::= #getReceiptRoot( BlockchainItem ) [function]
 // --------------------------------------------------------------
    rule #getReceiptRoot( { _ | <block> <receiptsRoot> RCPTROOT </receiptsRoot> ... </block> } ) => #unparseData( RCPTROOT, 32 )
```

Timestamp Calls
---------------

```k
    syntax KItem ::= "#firefly_getTime"
 // -----------------------------------
    rule <k> #firefly_getTime => #sendResponse( "result": #unparseQuantity( TIME ) ) ... </k>
         <timestamp> TIME </timestamp>

    syntax KItem ::= "#firefly_setTime"
 // -----------------------------------
    rule <k> #firefly_setTime => #sendResponse( "result": true ) ... </k>
         <params> [ TIME:String, .JSONList ] </params>
         <timestamp> _ => #parseHexWord( TIME ) </timestamp>

    rule <k> #firefly_setTime => #sendResponse( "result": false ) ... </k> [owise]
```

Gas Limit Call
--------------

```k
    syntax KItem ::= "#firefly_setGasLimit"
 // ---------------------------------------
    rule <k> #firefly_setGasLimit => #sendResponse( "result": true ) ... </k>
         <params> [ GLIMIT:String, .JSONList ] </params>
         <gasLimit> _ => #parseWord( GLIMIT ) </gasLimit>

    rule <k> #firefly_setGasLimit => #sendResponse( "result": true ) ... </k>
         <params> [ GLIMIT:Int, .JSONList ] </params>
         <gasLimit> _ => GLIMIT </gasLimit>

    rule <k> #firefly_setGasLimit => #sendResponse( "error": { "code": -32000, "message": "firefly_setGasLimit requires exactly 1 argument" } ) ... </k> [owise]
```

Mining
------

```k
    syntax KItem ::= "#evm_mine"
 // ----------------------------
    rule <k> #evm_mine => #mineBlock ~> #sendResponse( "result": "0x0" ) ... </k> [owise]

    rule <k> #evm_mine => #mineBlock ~> #sendResponse( "result": "0x0" ) ... </k>
         <params> [ TIME:String, .JSONList ] </params>
         <timestamp> _ => #parseWord( TIME ) </timestamp>

    rule <k> #evm_mine => #sendResponse( "error": "Incorrect number of arguments. Method 'evm_mine' requires between 0 and 1 arguments." ) ... </k>
         <params> [ _, _, _:JSONList ] </params>

    syntax KItem ::= "#firefly_genesisBlock"
 // ----------------------------------------
    rule <k> #firefly_genesisBlock => #updateTrieRoots ~> #pushBlockchainState ~> #getParentHash ~> #sendResponse ("result": true) ... </k>
         <logsBloom> _ => #padToWidth( 256, .ByteArray ) </logsBloom>
         <ommersHash> _ => 13478047122767188135818125966132228187941283477090363246179690878162135454535 </ommersHash>

    syntax KItem ::= "#mineBlock"
 // -----------------------------
    rule <k> #mineBlock => #finalizeBlock ~> #updateTrieRoots ~> #saveState ~> #startBlock ~> #cleanTxLists ~> #clearGas ~> #getParentHash ... </k>

    syntax KItem ::= "#saveState"
                   | "#incrementBlockNumber"
                   | "#cleanTxLists"
                   | "#clearGas"
                   | "#getParentHash"
                   | "#updateTrieRoots"
 // ----------------------------------------
    rule <k> #saveState => #incrementBlockNumber ~> #pushBlockchainState ... </k>

    rule <k> #incrementBlockNumber => . ... </k>
         <number> BN => BN +Int 1 </number>

    rule <k> #cleanTxLists => . ... </k>
         <txPending> _ => .List </txPending>
         <txOrder>   _ => .List </txOrder>

    rule <k> #clearGas => . ... </k>
         <gas> _ => 0 </gas>

    rule <k> #getParentHash => . ... </k>
         <blockList> BLOCKLIST </blockList>
         <previousHash> _ => #parseHexWord( Keccak256( #rlpEncodeBlock( #getBlockByNumber( "latest", BLOCKLIST ) ) ) ) </previousHash>

    rule <k> #updateTrieRoots => . ... </k>
         <stateRoot> _ => #parseHexWord( Keccak256( #rlpEncodeMerkleTree( #stateRoot ) ) ) </stateRoot>
         <transactionsRoot> _ => #parseHexWord( Keccak256( #rlpEncodeMerkleTree( #transactionsRoot ) ) ) </transactionsRoot>
         <receiptsRoot> _ => #parseHexWord( Keccak256( #rlpEncodeMerkleTree( #receiptsRoot ) ) ) </receiptsRoot>

endmodule
```
