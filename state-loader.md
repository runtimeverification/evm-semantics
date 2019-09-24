State Manager
-------------

```{.k}
requires "evm.k"
requires "asm.k"

module STATE-LOADER
    imports EVM
    imports EVM-ASSEMBLY

    syntax JSON ::= ByteArray | OpCodes | Map | Call | SubstateLogEntry | Account
 // -----------------------------------------------------------------------------

```

### Clearing State

-   `clear` clears all the execution state of the machine.
-   `clearX` clears the substate `X`, for `TX`, `BLOCK`, and `NETWORK`.

```{.k}
    syntax EthereumCommand ::= "clear"
 // ----------------------------------
    rule <k> clear => clearTX ~> clearBLOCK ~> clearNETWORK ... </k>

    syntax EthereumCommand ::= "clearTX"
 // ------------------------------------
    rule <k> clearTX => . ... </k>
         <output>          _ => .ByteArray </output>
         <memoryUsed>      _ => 0          </memoryUsed>
         <callDepth>       _ => 0          </callDepth>
         <callStack>       _ => .List      </callStack>
         <program>         _ => .ByteArray </program>
         <jumpDests>       _ => .Set       </jumpDests>
         <id>              _ => .Account   </id>
         <caller>          _ => .Account   </caller>
         <callData>        _ => .ByteArray </callData>
         <callValue>       _ => 0          </callValue>
         <wordStack>       _ => .WordStack </wordStack>
         <localMem>        _ => .Map       </localMem>
         <pc>              _ => 0          </pc>
         <gas>             _ => 0          </gas>
         <callGas>         _ => 0          </callGas>
         <selfDestruct>    _ => .Set       </selfDestruct>
         <log>             _ => .List      </log>
         <refund>          _ => 0          </refund>
         <gasPrice>        _ => 0          </gasPrice>
         <origin>          _ => .Account   </origin>
         <touchedAccounts> _ => .Set       </touchedAccounts>

    syntax EthereumCommand ::= "clearBLOCK"
 // ---------------------------------------
    rule <k> clearBLOCK => . ... </k>
         <previousHash>      _ => 0             </previousHash>
         <ommersHash>        _ => 0             </ommersHash>
         <coinbase>          _ => 0             </coinbase>
         <stateRoot>         _ => 0             </stateRoot>
         <transactionsRoot>  _ => 0             </transactionsRoot>
         <receiptsRoot>      _ => 0             </receiptsRoot>
         <logsBloom>         _ => .ByteArray    </logsBloom>
         <difficulty>        _ => 0             </difficulty>
         <number>            _ => 0             </number>
         <gasLimit>          _ => 0             </gasLimit>
         <gasUsed>           _ => 0             </gasUsed>
         <timestamp>         _ => 0             </timestamp>
         <extraData>         _ => .ByteArray    </extraData>
         <mixHash>           _ => 0             </mixHash>
         <blockNonce>        _ => 0             </blockNonce>
         <ommerBlockHeaders> _ => [ .JSONList ] </ommerBlockHeaders>
         <blockhashes>       _ => .List         </blockhashes>

    syntax EthereumCommand ::= "clearNETWORK"
 // -----------------------------------------
    rule <k> clearNETWORK => . ... </k>
         <statusCode>     _ => .StatusCode </statusCode>
         <activeAccounts> _ => .Set        </activeAccounts>
         <accounts>       _ => .Bag        </accounts>
         <messages>       _ => .Bag        </messages>
         <schedule>       _ => DEFAULT     </schedule>
```

### Loading State

-   `mkAcct_` creates an account with the supplied ID (assuming it's already been chopped to 160 bits).

```{.k}
    syntax EthereumCommand ::= "mkAcct" Int
 // ---------------------------------------
    rule <k> mkAcct ACCT => #newAccount ACCT ... </k>
```

-   `load` loads an account or transaction into the world state.

```{.k}
    syntax EthereumCommand ::= "load" JSON
 // --------------------------------------
    rule <k> load DATA : { .JSONList }          => .                                                   ... </k>
    rule <k> load DATA : { KEY : VALUE , REST } => load DATA : { KEY : VALUE } ~> load DATA : { REST } ... </k>
      requires REST =/=K .JSONList andBool DATA =/=String "transaction"

    rule <k> load DATA : [ .JSONList ]       => .                                            ... </k>
    rule <k> load DATA : [ { TEST } , REST ] => load DATA : { TEST } ~> load DATA : [ REST ] ... </k>
```

Here we perform pre-proccesing on account data which allows "pretty" specification of input.

```{.k}
    rule <k> load "pre" : { (ACCTID:String) : ACCT }             => mkAcct #parseAddr(ACCTID) ~> load "account" : { ACCTID : ACCT }                         ... </k>
    rule <k> load "account" : { ACCTID: { KEY : VALUE , REST } } => load "account" : { ACCTID : { KEY : VALUE } } ~> load "account" : { ACCTID : { REST } } ... </k> requires REST =/=K .JSONList

    rule <k> load "account" : { ((ACCTID:String) => #parseAddr(ACCTID)) : ACCT }                                ... </k>
    rule <k> load "account" : { (ACCT:Int) : { "balance" : ((VAL:String)         => #parseWord(VAL)) } }        ... </k>
    rule <k> load "account" : { (ACCT:Int) : { "nonce"   : ((VAL:String)         => #parseWord(VAL)) } }        ... </k>
    rule <k> load "account" : { (ACCT:Int) : { "code"    : ((CODE:String)        => #parseByteStack(CODE)) } }  ... </k>
    rule <k> load "account" : { (ACCT:Int) : { "storage" : ({ STORAGE:JSONList } => #parseMap({ STORAGE })) } } ... </k>
```

The individual fields of the accounts are dealt with here.

```{.k}
    rule <k> load "account" : { ACCT : { "balance" : (BAL:Int) } } => . ... </k>
         <account>
           <acctID> ACCT </acctID>
           <balance> _ => BAL </balance>
           ...
         </account>

    rule <k> load "account" : { ACCT : { "code" : (CODE:ByteArray) } } => . ... </k>
         <account>
           <acctID> ACCT </acctID>
           <code> _ => CODE </code>
           ...
         </account>

    rule <k> load "account" : { ACCT : { "nonce" : (NONCE:Int) } } => . ... </k>
         <account>
           <acctID> ACCT </acctID>
           <nonce> _ => NONCE </nonce>
           ...
         </account>

    rule <k> load "account" : { ACCT : { "storage" : (STORAGE:Map) } } => . ... </k>
         <account>
           <acctID> ACCT </acctID>
           <storage> _ => STORAGE </storage>
           <origStorage> _ => STORAGE </origStorage>
           ...
         </account>
```

Here we load the environmental information.

```{.k}
    rule <k> load "env" : { KEY : ((VAL:String) => #parseWord(VAL)) } ... </k>
      requires KEY in (SetItem("currentTimestamp") SetItem("currentGasLimit") SetItem("currentNumber") SetItem("currentDifficulty"))
    rule <k> load "env" : { KEY : ((VAL:String) => #parseHexWord(VAL)) } ... </k>
      requires KEY in (SetItem("currentCoinbase") SetItem("previousHash"))
 // ----------------------------------------------------------------------
    rule <k> load "env" : { "currentCoinbase"   : (CB:Int)     } => . ... </k> <coinbase>     _ => CB     </coinbase>
    rule <k> load "env" : { "currentDifficulty" : (DIFF:Int)   } => . ... </k> <difficulty>   _ => DIFF   </difficulty>
    rule <k> load "env" : { "currentGasLimit"   : (GLIMIT:Int) } => . ... </k> <gasLimit>     _ => GLIMIT </gasLimit>
    rule <k> load "env" : { "currentNumber"     : (NUM:Int)    } => . ... </k> <number>       _ => NUM    </number>
    rule <k> load "env" : { "previousHash"      : (HASH:Int)   } => . ... </k> <previousHash> _ => HASH   </previousHash>
    rule <k> load "env" : { "currentTimestamp"  : (TS:Int)     } => . ... </k> <timestamp>    _ => TS     </timestamp>

    syntax KItem ::= "loadCallState" JSON
 // -------------------------------------
    rule <k> loadCallState { "caller" : (ACCTFROM:Int), REST => REST } ... </k> <caller> _ => ACCTFROM </caller>
    rule <k> loadCallState { "origin" : (ORIG:Int), REST => REST } ... </k> <origin> _ => ORIG </origin>
    rule <k> loadCallState { "address" : (ACCTTO:Int), REST => REST } ... </k> <id> _ => ACCTTO </id>

    rule <k> loadCallState { "code" : (CODE:OpCodes), REST => REST} ... </k>
         <program> _ => #asmOpCodes(CODE) </program>
         <jumpDests> _ => #computeValidJumpDests(#asmOpCodes(CODE)) </jumpDests>

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

    rule <k> loadCallState { "code" : CODE:ByteArray, REST => REST } ... </k>
         <program> _ => CODE </program>
         <jumpDests> _ => #computeValidJumpDests(CODE) </jumpDests>

    rule <k> loadCallState { "gas" : GLIMIT:Int, REST => REST }      ... </k> <gas>       _ => GLIMIT </gas>
    rule <k> loadCallState { "gasPrice" : GPRICE:Int, REST => REST } ... </k> <gasPrice>  _ => GPRICE </gasPrice>
    rule <k> loadCallState { "value" : VALUE:Int, REST => REST }     ... </k> <callValue> _ => VALUE  </callValue>
    rule <k> loadCallState { "data" : DATA:ByteArray, REST => REST } ... </k> <callData>  _ => DATA   </callData>
    rule <k> loadCallState { "nonce" : _, REST => REST } ... </k>

    rule <k> loadCallState { .JSONList } => . ... </k>

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

The `"network"` key allows setting the fee schedule inside the test.

```{.k}
    rule <k> load "network" : SCHEDSTRING => . ... </k>
         <schedule> _ => #asScheduleString(SCHEDSTRING) </schedule>

    syntax Schedule ::= #asScheduleString ( String ) [function]
 // -----------------------------------------------------------
    rule #asScheduleString("Frontier")          => FRONTIER
    rule #asScheduleString("Homestead")         => HOMESTEAD
    rule #asScheduleString("EIP150")            => TANGERINE_WHISTLE
    rule #asScheduleString("EIP158")            => SPURIOUS_DRAGON
    rule #asScheduleString("Byzantium")         => BYZANTIUM
    rule #asScheduleString("Constantinople")    => CONSTANTINOPLE
    rule #asScheduleString("ConstantinopleFix") => PETERSBURG
```

The `"rlp"` key loads the block information.

```{.k}
    rule <k> load "rlp"        : (VAL:String => #rlpDecode(#unparseByteStack(#parseByteStack(VAL)))) ... </k>
    rule <k> load "genesisRLP" : (VAL:String => #rlpDecode(#unparseByteStack(#parseByteStack(VAL)))) ... </k>
 // ---------------------------------------------------------------------------------------------------------
    rule <k> load "rlp" : [ [ HP , HO , HC , HR , HT , HE , HB , HD , HI , HL , HG , HS , HX , HM , HN , .JSONList ] , BT , BU , .JSONList ]
          => load "transaction" : BT
         ...
         </k>
         <previousHash>      _ => #asWord(#parseByteStackRaw(HP)) </previousHash>
         <ommersHash>        _ => #asWord(#parseByteStackRaw(HO)) </ommersHash>
         <coinbase>          _ => #asWord(#parseByteStackRaw(HC)) </coinbase>
         <stateRoot>         _ => #asWord(#parseByteStackRaw(HR)) </stateRoot>
         <transactionsRoot>  _ => #asWord(#parseByteStackRaw(HT)) </transactionsRoot>
         <receiptsRoot>      _ => #asWord(#parseByteStackRaw(HE)) </receiptsRoot>
         <logsBloom>         _ => #parseByteStackRaw(HB)          </logsBloom>
         <difficulty>        _ => #asWord(#parseByteStackRaw(HD)) </difficulty>
         <number>            _ => #asWord(#parseByteStackRaw(HI)) </number>
         <gasLimit>          _ => #asWord(#parseByteStackRaw(HL)) </gasLimit>
         <gasUsed>           _ => #asWord(#parseByteStackRaw(HG)) </gasUsed>
         <timestamp>         _ => #asWord(#parseByteStackRaw(HS)) </timestamp>
         <extraData>         _ => #parseByteStackRaw(HX)          </extraData>
         <mixHash>           _ => #asWord(#parseByteStackRaw(HM)) </mixHash>
         <blockNonce>        _ => #asWord(#parseByteStackRaw(HN)) </blockNonce>
         <ommerBlockHeaders> _ => BU                              </ommerBlockHeaders>

    rule <k> load "genesisRLP": [ [ HP, HO, HC, HR, HT, HE:String, HB, HD, HI, HL, HG, HS, HX, HM, HN, .JSONList ], _, _, .JSONList ] => .K ... </k>
         <blockhashes> .List => ListItem(#blockHeaderHash(HP, HO, HC, HR, HT, HE, HB, HD, HI, HL, HG, HS, HX, HM, HN)) ListItem(#asWord(#parseByteStackRaw(HP))) ... </blockhashes>

    syntax EthereumCommand ::= "mkTX" Int
 // -------------------------------------
    rule <k> mkTX TXID => . ... </k>
         <txOrder>   ... (.List => ListItem(TXID)) </txOrder>
         <txPending> ... (.List => ListItem(TXID)) </txPending>
         <messages>
            ( .Bag
           => <message>
                <msgID> TXID:Int   </msgID>
                <txGasPrice> 1     </txGasPrice>
                <txGasLimit> 90000 </txGasLimit>
                ...
              </message>
            )
          ...
          </messages>

    rule <k> load "transaction" : [ [ TN , TP , TG , TT , TV , TI , TW , TR , TS ] , REST ]
          => mkTX !ID:Int
          ~> load "transaction" : { !ID : { "data"  : TI   ,   "gasLimit" : TG   ,   "gasPrice" : TP
                                          , "nonce" : TN   ,   "r"        : TR   ,   "s"        : TS
                                          , "to"    : TT   ,   "v"        : TW   ,   "value"    : TV
                                          , .JSONList
                                          }
                                  }
          ~> load "transaction" : [ REST ]
          ...
          </k>

    rule <k> load "transaction" : { ACCTID: { KEY : VALUE , REST } }
          => load "transaction" : { ACCTID : { KEY : VALUE } }
          ~> load "transaction" : { ACCTID : { REST } }
          ...
         </k>
      requires REST =/=K .JSONList

    rule <k> load "transaction" : { TXID : { GLIMIT     : TG:Int } } => . ... </k>
         <message> <msgID> TXID </msgID> <txGasLimit> _ => TG </txGasLimit> ... </message>
      requires GLIMIT in (SetItem("gas") SetItem("gasLimit"))

    rule <k> load "transaction" : { TXID : { "gasPrice" : TP:Int } } => . ... </k>
         <message> <msgID> TXID </msgID> <txGasPrice> _ => TP </txGasPrice> ... </message>

    rule <k> load "transaction" : { TXID : { "nonce" : TN:Int } } => . ... </k>
         <message> <msgID> TXID </msgID> <txNonce> _ => TN </txNonce> ... </message>

    rule <k> load "transaction" : { TXID : { "value" : TV:Int } } => . ... </k>
         <message> <msgID> TXID </msgID> <value> _ => TV </value> ... </message>

    rule <k> load "transaction" : { TXID : { "to" : TT:Account } } => . ... </k>
         <message> <msgID> TXID </msgID> <to> _ => TT </to> ... </message>

    rule <k> load "transaction" : { TXID : { "data" : TI:ByteArray } } => . ... </k>
         <message> <msgID> TXID </msgID> <data> _ => TI </data> ... </message>

    rule <k> load "transaction" : { TXID : { "v" : TW:Int } } => . ... </k>
         <message> <msgID> TXID </msgID> <sigV> _ => TW </sigV> ... </message>

    rule <k> load "transaction" : { TXID : { "r" : TR:ByteArray } } => . ... </k>
         <message> <msgID> TXID </msgID> <sigR> _ => TR </sigR> ... </message>

    rule <k> load "transaction" : { TXID : { "s" : TS:ByteArray } } => . ... </k>
         <message> <msgID> TXID </msgID> <sigS> _ => TS </sigS> ... </message>
```

```{.k}
endmodule
```
