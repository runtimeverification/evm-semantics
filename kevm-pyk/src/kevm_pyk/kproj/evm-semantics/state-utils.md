State Manager
-------------

```k
requires "evm.md"
requires "asm.md"

module STATE-UTILS
    imports EVM
    imports EVM-ASSEMBLY

    syntax JSON ::= Bytes | OpCodes | Map | SubstateLogEntry | Account
 // ------------------------------------------------------------------

```

### Clearing State

-   `clear` clears all the execution state of the machine.
-   `clearX` clears the substate `X`, for `TX`, `BLOCK`, and `NETWORK`.

```k
    syntax EthereumCommand ::= "clear"
 // ----------------------------------
    rule <k> clear => clearTX ~> clearBLOCK ~> clearNETWORK ... </k>

    syntax EthereumCommand ::= "clearTX"
 // ------------------------------------
    rule <k> clearTX => .K ... </k>
         <output>           _ => .Bytes     </output>
         <memoryUsed>       _ => 0          </memoryUsed>
         <program>          _ => .Bytes     </program>
         <jumpDests>        _ => .Bytes     </jumpDests>
         <wordStack>        _ => .List      </wordStack>
         <localMem>         _ => .Bytes     </localMem>
         <pc>               _ => 0          </pc>
         <gas>              _ => 0          </gas>
         <callGas>          _ => 0          </callGas>

    syntax EthereumCommand ::= "clearBLOCK"
 // ---------------------------------------
    rule <k> clearBLOCK => .K ... </k>

    syntax EthereumCommand ::= "clearNETWORK"
 // -----------------------------------------
    rule <k> clearNETWORK => .K ... </k>
         <statusCode>     _ => .StatusCode </statusCode>
         <schedule>       _ => HOMESTEAD   </schedule>

```

### Loading State

-   `load` loads an account or transaction into the world state.

```k
    syntax EthereumCommand ::= "load" JSON
 // --------------------------------------
    rule <k> load _DATA : { .JSONs }             => .K                                                   ... </k>
    rule <k> load  DATA : { KEY : VALUE , REST } => load DATA : { KEY : VALUE } ~> load DATA : { REST } ... </k>
      requires REST =/=K .JSONs andBool DATA =/=String "transaction"

    rule <k> load _DATA : [ .JSONs ]          => .K                                            ... </k>
    rule <k> load  DATA : [ { TEST } , REST ] => load DATA : { TEST } ~> load DATA : [ REST ] ... </k>
```

The `"network"` key allows setting the fee schedule inside the test.

```k
    rule <k> load "network" : SCHEDSTRING => .K ... </k>
         <schedule> _ => #asScheduleString(SCHEDSTRING) </schedule>

    syntax Schedule ::= #asScheduleString ( String ) [symbol(#asScheduleString), function]
 // --------------------------------------------------------------------------------------
    rule #asScheduleString("Frontier")                  => FRONTIER
    rule #asScheduleString("Homestead")                 => HOMESTEAD
    rule #asScheduleString("EIP150")                    => TANGERINE_WHISTLE
    rule #asScheduleString("EIP158")                    => SPURIOUS_DRAGON
    rule #asScheduleString("Byzantium")                 => BYZANTIUM
    rule #asScheduleString("Constantinople")            => CONSTANTINOPLE
    rule #asScheduleString("ConstantinopleFix")         => PETERSBURG
    rule #asScheduleString("Istanbul")                  => ISTANBUL
    rule #asScheduleString("Berlin")                    => BERLIN
    rule #asScheduleString("London")                    => LONDON
    rule #asScheduleString("Merge")                     => MERGE
    rule #asScheduleString("Paris")                     => MERGE
    rule #asScheduleString("Shanghai")                  => SHANGHAI
    rule #asScheduleString("Cancun")                    => CANCUN
    rule #asScheduleString("ShanghaiToCancunAtTime15k") => CANCUN
    rule #asScheduleString("Prague")                    => PRAGUE
```

### Block Identifiers

```k
    syntax BlockIdentifier ::= Int
                             | "LATEST"
                             | "PENDING"
                             | "EARLIEST"
 // -------------------------------------

    syntax BlockIdentifier ::= #parseBlockIdentifier ( JSON ) [symbol(#parseBlockIdentifier), function]
 // ---------------------------------------------------------------------------------------------------
    rule #parseBlockIdentifier(BLOCKNUM:Int) => BLOCKNUM
    rule #parseBlockIdentifier("pending")    => PENDING
    rule #parseBlockIdentifier("latest")     => LATEST
    rule #parseBlockIdentifier("earliest")   => EARLIEST
    rule #parseBlockIdentifier(BLOCKNUM)     => #parseWord(BLOCKNUM) [owise]
```
```k
endmodule
```
