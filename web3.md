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
        <web3socket> $SOCK:Int </web3socket>
        <web3clientsocket> 0:IOInt </web3clientsocket>
        <web3request>
          <jsonrpc> "":JSON </jsonrpc>
          <callid> 0:JSON </callid>
          <method> "":JSON </method>
          <params> [ .JSONList ] </params>
        </web3request>
      </kevm-client>

    syntax JSON ::= Int | Bool | "null" | "undef"
                  | #getJSON ( JSONKey, JSON ) [function]
 // -----------------------------------------------------
    rule #getJSON( KEY, { KEY : J, _ } )     => J
    rule #getJSON( _, { .JSONList } )        => undef
    rule #getJSON( KEY, { KEY2 : _, REST } ) => #getJSON( KEY, { REST } )
      requires KEY =/=K KEY2

    syntax Int ::= #getInt ( JSONKey, JSON ) [function]
 // ---------------------------------------------------
    rule #getInt( KEY, J ) => {#getJSON( KEY, J )}:>Int

    syntax String ::= #getString ( JSONKey, JSON ) [function]
 // ---------------------------------------------------------
    rule #getString( KEY, J ) => {#getJSON( KEY, J )}:>String

    syntax IOJSON ::= JSON | IOError

    syntax EthereumSimulation ::= accept() [symbol]
 // -----------------------------------------------

    rule <k> accept() => getRequest() ... </k>
         <web3socket> SOCK </web3socket>
         <web3clientsocket> _ => #accept(SOCK) </web3clientsocket>

    syntax KItem ::= getRequest()
 // -----------------------------

    rule <k> getRequest() => #loadRPCCall(#getRequest(SOCK)) ... </k>
         <web3clientsocket> SOCK </web3clientsocket>

    syntax IOJSON ::= #getRequest(Int) [function, hook(JSON.read)] 
    syntax K ::= #putResponse(JSON, Int) [function, hook(JSON.write)]

    syntax KItem ::= #loadRPCCall(IOJSON)
 // -------------------------------------
    rule <k> #loadRPCCall({ _ } #as J) => #runRPCCall ... </k>
         <jsonrpc> _             => #getJSON("jsonrpc", J) </jsonrpc>
         <callid>  _             => #getJSON("id"     , J) </callid>
         <method>  _             => #getJSON("method" , J) </method>
         <params>  _             => #getJSON("params" , J) </params>

    rule <k> #loadRPCCall(#EOF) => #shutdownWrite(SOCK) ~> #close(SOCK) ~> accept() ... </k>
         <web3clientsocket> SOCK </web3clientsocket>

    syntax KItem ::= #sendResponse( JSON )
 // --------------------------------------
    rule <k> #sendResponse(J) => #putResponse(J, SOCK) ~> getRequest() ... </k>
         <web3clientsocket> SOCK </web3clientsocket>

    syntax KItem ::= "#runRPCCall"
 // ------------------------------
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

    syntax KItem ::= "#net_version"
 // -------------------------------
    rule <k> #net_version => #sendResponse( { "id" : CALLID, "jsonrpc" : JSONRPC, "result" : Int2String( CHAINID ) } ) ... </k>
         <jsonrpc> JSONRPC </jsonrpc>
         <callid> CALLID </callid>
         <chainID> CHAINID </chainID>

    syntax KItem ::= "#web3_clientVersion"
 // -------------------------------
    rule <k> #web3_clientVersion => #sendResponse( { "id" : CALLID, "jsonrpc" : JSONRPC, "result" : "Firefly RPC/v0.0.1/kevm" } ) ... </k>
         <jsonrpc> JSONRPC </jsonrpc>
         <callid> CALLID </callid>

    syntax KItem ::= "#eth_gasPrice"
 // --------------------------------
    rule <k> #eth_gasPrice => #sendResponse( { "id" : CALLID, "jsonrpc" : JSONRPC, "result" : #unparseQuantity( PRICE ) } ) ... </k>
         <jsonrpc> JSONRPC </jsonrpc>
         <callid> CALLID </callid>
         <gasPrice> PRICE </gasPrice>

    syntax KItem ::= "#eth_blockNumber"
 // -----------------------------------
    rule <k> #eth_blockNumber => #sendResponse( { "id" : CALLID, "jsonrpc" : JSONRPC, "result" : #unparseQuantity( BLOCKNUM ) } ) ... </k>
         <jsonrpc> JSONRPC </jsonrpc>
         <callid> CALLID </callid>
         <number> BLOCKNUM </number>

    syntax KItem ::= "#eth_accounts"
 // --------------------------------
    rule <k> #eth_accounts => #sendResponse( { "id" : CALLID, "jsonrpc" : JSONRPC, "result" : [ #acctsToJArray( ACCTS ) ] } ) ... </k>
         <jsonrpc> JSONRPC </jsonrpc>
         <callid> CALLID </callid>
         <activeAccounts> ACCTS </activeAccounts>

    syntax JSONList ::= #acctsToJArray ( Set ) [function]
 // -----------------------------------------------------
    rule #acctsToJArray( .Set ) => .JSONList
    rule #acctsToJArray( SetItem( ACCT ) ACCTS:Set ) => #unparseData( ACCT, 20 ), #acctsToJArray( ACCTS )

    syntax KItem ::= "#eth_getBalance"
 // ----------------------------------
    rule <k> #eth_getBalance ... </k>
         <params> [ (DATA => #parseHexWord(DATA)), _ ] </params>

    rule <k> #eth_getBalance => #sendResponse( { "id" : CALLID, "jsonrpc" : JSONRPC, "result" : #unparseQuantity( ACCTBALANCE ) } ) ... </k>
         <jsonrpc> JSONRPC </jsonrpc>
         <callid> CALLID </callid>
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

    rule <k> #eth_getStorageAt => #sendResponse( { "id" : CALLID, "jsonrpc" : JSONRPC, "result" : #unparseQuantity( #lookup (STORAGE, QUANTITY) ) } ) ... </k>
         <jsonrpc> JSONRPC </jsonrpc>
         <callid> CALLID </callid>
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

    rule <k> #eth_getCode => #sendResponse( { "id" : CALLID, "jsonrpc" : JSONRPC, "result" : #unparseDataByteArray( CODE ) } ) ... </k>
         <jsonrpc> JSONRPC </jsonrpc>
         <callid> CALLID </callid>
         <params> [ DATA, TAG, .JSONList ] </params>
         <account>
           <acctID> DATA </acctID>
           <code> CODE </code>
           ...
         </account>
endmodule
```
