Web3 RPC JSON Handler
====================
```k
requires "evm.k"
requires "data.k"

module WEB3
    imports EVM
    imports EVM-DATA
    // LOGIC GOES HERE

    configuration
      <kevm-client>
        <kevm />
        <web3request>
          <jsonrpc> "" </jsonrpc>
          <callid> 0 </callid>
          <method> "" </method>
          <params> [ .JSONList ] </params>
        </web3request>
        <web3result> .List </web3result>
      </kevm-client>

    syntax EthereumSimulation ::= List{JSON, " "}
    syntax JSON ::= Int | Bool

    rule <k> J:JSON REST:EthereumSimulation => #loadRPCCall J ~> REST ... </k>
    rule <k> J:JSON => #loadRPCCall J ... </k>

    syntax KItem ::= "#loadRPCCall" JSON
 // ------------------------------------
    rule <k> #loadRPCCall J:JSON => #runRPCCall ... </k>
         <jsonrpc> _ => #getVersion(J) </jsonrpc>
         <callid> _ => #getId(J) </callid>
         <method> _ => #getMethod(J) </method>
         <params> _ => #getParams(J) </params>

    syntax Int ::= #getId( JSON ) [function]
 // ----------------------------------------
    rule #getId( { "id" : VALUE:Int, _ } ) => VALUE
    rule #getId( { KEY : _, REST } => { REST } )
        requires KEY =/=String "id"

    syntax String ::= #getVersion( JSON ) [function]
                    | #getMethod( JSON )  [function]
 // ------------------------------------------------
    rule #getVersion( { "jsonrpc" : VALUE:String, _ } ) => VALUE
    rule #getVersion( { KEY : _, REST } => { REST } )
        requires KEY =/=String "jsonrpc"
    rule #getMethod( { "method" : VALUE:String, _ } ) => VALUE
    rule #getMethod( { KEY : _, REST } => { REST } )
        requires KEY =/=String "method"

    syntax JSON ::= #getParams( JSON ) [function]
 // ---------------------------------------------
    rule #getParams( { "params" : VALUE:JSON, _ } ) => VALUE
    rule #getParams( { KEY : _, REST } => { REST } )
        requires KEY =/=String "params"

    syntax KItem ::= #sendResponse( JSON )
 // --------------------------------------
    rule <k> #sendResponse( J:JSON ) => . ... </k>
         <web3result> ... ( .List => ListItem( J ) ) </web3result>

    syntax KItem ::= "#runRPCCall"
 // ------------------------------
    rule <k> #runRPCCall => #net_version ... </k>
         <method> "net_version" </method>
    rule <k> #runRPCCall => #eth_gasPrice ... </k>
         <method> "eth_gasPrice" </method>
    rule <k> #runRPCCall => #eth_blockNumber ... </k>
         <method> "eth_blockNumber" </method>

    syntax KItem ::= "#net_version"
 // -------------------------------
    rule <k> #net_version => #sendResponse( { "id" : CALLID, "jsonrpc" : JSONRPC, "result" : Int2String( CHAINID ) } ) ... </k>
         <jsonrpc> JSONRPC </jsonrpc>
         <callid> CALLID </callid>
         <chainID> CHAINID </chainID>

    syntax KItem ::= "#eth_gasPrice"
 // --------------------------------
    rule <k> #eth_gasPrice => #sendResponse( { "id" : CALLID, "jsonrpc" : JSONRPC, "result" : Int2String( PRICE ) } ) ... </k> // TODO: Decide to have output in hex form here or convert it later
         <jsonrpc> JSONRPC </jsonrpc>
         <callid> CALLID </callid>
         <gasPrice> PRICE </gasPrice>

    syntax KItem ::= "#eth_blockNumber"
 // -----------------------------------
    rule <k> #eth_blockNumber => #sendResponse( { "id" : CALLID, "jsonrpc" : JSONRPC, "result" : Int2String( BLOCKNUM ) } ) ... </k>
         <jsonrpc> JSONRPC </jsonrpc>
         <callid> CALLID </callid>
         <number> BLOCKNUM </number>

endmodule
```
