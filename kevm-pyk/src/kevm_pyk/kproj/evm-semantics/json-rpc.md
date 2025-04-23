JSON RPC
========

```k
requires "json.md"
```

JSON Extensions
---------------

Some common functions and extensions of JSON are provided here.

```k
module JSON-EXT
    imports JSON
    imports STRING
    imports BOOL
```

-   `+JSONs` appends two JSON lists.
-   `reverseJSONs` reverses a JSON list.

```k
    syntax JSONs ::= JSONs "+JSONs" JSONs [function]
 // ------------------------------------------------
    rule .JSONs   +JSONs JS' => JS'
    rule (J , JS) +JSONs JS' => J , (JS +JSONs JS')

    syntax JSONs ::= reverseJSONs    ( JSONs         ) [symbol(reverseJSONs), function]
                   | reverseJSONsAux ( JSONs , JSONs ) [symbol(reverseJSONsAux), function]
 // --------------------------------------------------------------------------------------
    rule reverseJSONs(JS) => reverseJSONsAux(JS, .JSONs)

    rule reverseJSONsAux(.JSONs, JS') => JS'
    rule reverseJSONsAux((J, JS:JSONs), JS') => reverseJSONsAux(JS, (J, JS'))
```

-   `qsortJSONs` quick-sorts a list of key-value pairs.
-   `sortedJSONs` is a predicate saying whether a given list of JSONs is sorted or not.

```k
    syntax JSONs ::= qsortJSONs ( JSONs )          [symbol(qsortJSONs), function]
                   | #entriesLT ( String , JSONs ) [symbol(#entriesLT), function]
                   | #entriesGE ( String , JSONs ) [symbol(#entriesGE), function]
 // -----------------------------------------------------------------------------
    rule qsortJSONs(.JSONs)            => .JSONs
    rule qsortJSONs(KEY : VALUE, REST) => qsortJSONs(#entriesLT(KEY, REST)) +JSONs (KEY : VALUE , qsortJSONs(#entriesGE(KEY, REST)))

    rule #entriesLT(_KEY, .JSONs)              => .JSONs
    rule #entriesLT( KEY, (KEY': VALUE, REST)) => KEY': VALUE , #entriesLT(KEY, REST) requires         KEY' <String KEY
    rule #entriesLT( KEY, (KEY':     _, REST)) =>               #entriesLT(KEY, REST) requires notBool KEY' <String KEY

    rule #entriesGE(_KEY, .JSONs)              => .JSONs
    rule #entriesGE( KEY, (KEY': VALUE, REST)) => KEY': VALUE , #entriesGE(KEY, REST) requires         KEY' >=String KEY
    rule #entriesGE( KEY, (KEY':     _, REST)) =>               #entriesGE(KEY, REST) requires notBool KEY' >=String KEY

    syntax Bool ::= sortedJSONs ( JSONs ) [symbol(sortedJSONs), function]
 // ---------------------------------------------------------------------
    rule sortedJSONs( .JSONs   ) => true
    rule sortedJSONs( _KEY : _ ) => true
    rule sortedJSONs( (KEY : _) , (KEY' : VAL) , REST ) => KEY <=String KEY' andThenBool sortedJSONs((KEY' : VAL) , REST)
```

**TODO**: Adding `Int` to `JSONKey` is a hack to make certain parts of semantics easier.

```k
    syntax JSONKey ::= Int
 // ----------------------
```

 - in_keys - returns true if a key is present in a JSON object.

```k
    syntax Bool ::= inKeys ( String , JSONs ) [symbol(in_keys_json), function]
 // --------------------------------------------------------------------------
    rule inKeys(_KEY, .JSONs) => false
    rule inKeys(KEY, (KEY  : _, _REST)) => true
    rule inKeys(KEY, (KEY' : _,  REST)) => inKeys(KEY, REST) requires KEY =/=String KEY'
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
    imports JSON-EXT

    configuration
      <json-rpc>
        <web3input> $INPUT:Int </web3input>
        <web3output> $OUTPUT:Int </web3output>
        <web3request>
          <jsonrpc> "":JSON </jsonrpc>
          <callid> 0:JSON </callid>
          <method> "":JSON </method>
          <params> [ .JSONs ] </params>
          <batch> undef </batch>
        </web3request>
        <web3response> .List </web3response>
      </json-rpc>

    syntax JSON ::= "undef" [symbol(JSON-RPCundef)]
 // -----------------------------------------------

    syntax Bool ::= isProperJson     ( JSON  ) [symbol(isProperJson), function]
                  | isProperJsonList ( JSONs ) [symbol(isProperJsonList), function]
 // -------------------------------------------------------------------------------
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

    syntax JSONs ::= flattenJSONs ( JSONs ) [symbol(flattenJSONs), function]
 // ------------------------------------------------------------------------
    rule flattenJSONs(.JSONs      ) => .JSONs
    rule flattenJSONs([.JSONs], JL) => flattenJSONs(JL)
    rule flattenJSONs([J,JS]  , JL) => J, flattenJSONs([JS], JL)
endmodule
```
