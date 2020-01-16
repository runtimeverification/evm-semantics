### JSON Formatting

The JSON format is used extensively for communication in the Ethereum circles.
Writing a JSON-ish parser in K takes 6 lines.

```k
module JSON
    imports INT
    imports STRING
    imports BOOL

    syntax JSONs   ::= List{JSON,","}      [klabel(JSONs)      , symbol]
    syntax JSONKey ::= String
    syntax JSON    ::= "null"              [klabel(JSONnull)   , symbol]
                     | String | Int | Bool
                     | JSONKey ":" JSON    [klabel(JSONEntry)  , symbol]
                     | "{" JSONs "}"       [klabel(JSONObject) , symbol]
                     | "[" JSONs "]"       [klabel(JSONList)   , symbol]
 // --------------------------------------------------------------------
```

**TODO**: Adding `Int` to `JSONKey` is a hack to make certain parts of semantics easier.

```k
    syntax JSONKey ::= Int
 // ----------------------

endmodule
```

JSON-RPC
--------

```k
module JSON-RPC
    imports K-IO
    imports LIST
    imports JSON

    configuration
      <json-rpc>
        <web3socket> $SOCK:Int </web3socket>
        <web3clientsocket> 0:IOInt </web3clientsocket>
        <web3request>
          <jsonrpc> "":JSON </jsonrpc>
          <callid> 0:JSON </callid>
          <method> "":JSON </method>
          <params> [ .JSONs ] </params>
          <batch> undef </batch>
        </web3request>
        <web3response> .List </web3response>
      </json-rpc>

    syntax JSON ::= "undef" [klabel(JSON-RPCundef), symbol]
 // -------------------------------------------------------

    syntax Bool ::= isProperJson     ( JSON  ) [function]
                  | isProperJsonList ( JSONs ) [function]
 // -----------------------------------------------------
    rule isProperJson(_) => false [owise]

    rule isProperJson(null) => true

    rule isProperJson(_:Int)    => true
    rule isProperJson(_:Bool)   => true
    rule isProperJson(_:String) => true

    rule isProperJson(_:JSONKey : J) => isProperJson(J)

    rule isProperJson([ JS ]) => isProperJsonList(JS)
    rule isProperJson({ JS }) => isProperJsonList(JS)

    rule isProperJsonList(.JSONs) => true
    rule isProperJsonList(J, JS)  => isProperJson(J) andBool isProperJsonList(JS)

    syntax JSONs ::= flattenJSONs ( JSONs ) [function]
 // --------------------------------------------------
    rule flattenJSONs(.JSONs      ) => .JSONs
    rule flattenJSONs([.JSONs], JL) => flattenJSONs(JL)
    rule flattenJSONs([J,JS]  , JL) => J, flattenJSONs([JS], JL)
endmodule
```
