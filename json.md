KJSON
=====

This is a near-faithful implementation of the [ECMA-404 JSON Data Interchange Format](http://www.ecma-international.org/publications/files/ECMA-ST/ECMA-404.pdf).
There are issues with how `JSONNumber` and `JSONString` are specified here, because we use K's `String` and `Int` sort directly, which are not quite correct.

### JSON Syntax

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

-   `reverseJSONs` reverses a JSON list.

```k
    syntax JSONs ::= reverseJSONs    ( JSONs         ) [function]
                   | reverseJSONsAux ( JSONs , JSONs ) [function]
 // -------------------------------------------------------------
    rule reverseJSONs(JS) => reverseJSONsAux(JS, .JSONs)

    rule reverseJSONsAux(.JSONs, JS') => JS'
    rule reverseJSONsAux((J, JS:JSONs), JS') => reverseJSONsAux(JS, (J, JS'))
```

-   `qsortJSONs` quick-sorts a list of key-value pairs.
-   `sortedJSONs` is a predicate saying whether a given list of JSONs is sorted or not.

```k
    syntax JSONs ::= qsortJSONs ( JSONs )          [function]
                   | #entriesLT ( String , JSONs ) [function]
                   | #entriesGE ( String , JSONs ) [function]
 // ---------------------------------------------------------
    rule qsortJSONS(.JSONs)              => .JSONs
    rule qsortJSONS((KEY : VALUE), REST) => qsortJSONs(#entriesLT(KEY, REST)) , KEY : VALUE , qsortJSONs(#entriesGT(KEY, REST))

    rule #entriesLT(KEY, .JSONs)              => .JSONs
    rule #entriesLT(KEY, (KEY': VALUE, REST)) => KEY': VALUE , #entriesLT(KEY, REST) requires         KEY' <String KEY
    rule #entriesLT(KEY, (KEY': VALUE, REST)) => KEY': VALUE , #entriesLT(KEY, REST) requires notBool KEY' <String KEY

    rule #entriesGE(KEY, .JSONs)              => .JSONs
    rule #entriesGE(KEY, (KEY': VALUE, REST)) => KEY': VALUE , #entriesGE(KEY, REST) requires         KEY' >=String KEY
    rule #entriesGE(KEY, (KEY': VALUE, REST)) => KEY': VALUE , #entriesGE(KEY, REST) requires notBool KEY' >=String KEY

    syntax Bool ::= sortedJSONs ( JSONs ) [function]
 // ------------------------------------------------
    rule sortedJSONs( .JSONs  ) => true
    rule sortedJSONs( KEY : _ ) => true
    rule sortedJSONs( (KEY : _) , (KEY' : VAL) , REST ) => KEY <=String KEY' andThenBool sortedJSONs((KEY' : VAL) , REST)
```

**TODO**: Adding `Int` to `JSONKey` is a hack to make certain parts of semantics easier.

```k
    syntax JSONKey ::= Int
 // ----------------------
```

```k
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
