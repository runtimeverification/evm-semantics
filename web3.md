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
         <params> [ (DATA => #parseHexWord(DATA)), _ ] </params>

    rule <k> #eth_getBalance => #sendResponse( "result" : #unparseQuantity( ACCTBALANCE ) ) ... </k>
         <params> [ DATA, TAG, .JSONList ] </params>
         <account>
           <acctID> DATA </acctID>
           <balance> ACCTBALANCE </balance>
           ...
         </account>

    syntax KItem ::= "#eth_getStorageAt"
 // ------------------------------------
    rule <k> #eth_getStorageAt ... </k>
         <params> [ (DATA => #parseHexWord(DATA)), QUANTITY:Int, _ ] </params>

    rule <k> #eth_getStorageAt => #sendResponse( "result" : #unparseQuantity( #lookup (STORAGE, QUANTITY) ) ) ... </k>
         <params> [ DATA, QUANTITY, TAG, .JSONList ] </params>
         <account>
           <acctID> DATA </acctID>
           <storage> STORAGE </storage>
           ...
         </account>

    syntax KItem ::= "#eth_getCode"
 // -------------------------------
    rule <k> #eth_getCode ... </k>
         <params> [ (DATA => #parseHexWord(DATA)), _ ] </params>

    rule <k> #eth_getCode => #sendResponse( "result" : #unparseDataByteArray( CODE ) ) ... </k>
         <params> [ DATA, TAG, .JSONList ] </params>
         <account>
           <acctID> DATA </acctID>
           <code> CODE </code>
           ...
         </account>

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

    syntax KItem ::= "#personal_importRawKey"
 // -----------------------------------------
    rule <k> #personal_importRawKey => StoreKey( #parseHexWord( PRIKEY ), #addr( #parseHexWord( Keccak256 ( Hex2Binary( ECDSAPubKey( Hex2Binary( PRIKEY ) ) ) ) ) ) ) ... </k>
         <params> [ PRIKEY, _ ] </params> // TODO: This takes another parameter with the passphrase for the unencrypted key

    syntax KItem ::= StoreKey ( Int, Int )
 // --------------------------------------
    rule <k> StoreKey ( PRIKEY, ACCTADDR ) => #sendResponse ( "result": #unparseData( ACCTADDR, 20 ) ) ... </k>
         <accountKeys> M => M[ACCTADDR <- PRIKEY] </accountKeys>

endmodule
```
