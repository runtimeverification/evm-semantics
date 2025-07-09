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
         <blockhashes> _ => .List </blockhashes>

    syntax EthereumCommand ::= "clearTX"
 // ------------------------------------
    rule <k> clearTX => .K ... </k>
         <output>           _ => .Bytes     </output>
         <memoryUsed>       _ => 0          </memoryUsed>
         <callDepth>        _ => 0          </callDepth>
         <callStack>        _ => .List      </callStack>
         <program>          _ => .Bytes     </program>
         <jumpDests>        _ => .Bytes     </jumpDests>
         <id>               _ => .Account   </id>
         <caller>           _ => .Account   </caller>
         <callData>         _ => .Bytes     </callData>
         <callValue>        _ => 0          </callValue>
         <wordStack>        _ => .WordStack </wordStack>
         <localMem>         _ => .Bytes     </localMem>
         <pc>               _ => 0          </pc>
         <gas>              _ => 0          </gas>
         <callGas>          _ => 0          </callGas>
         <selfDestruct>     _ => .Set       </selfDestruct>
         <log>              _ => .List      </log>
         <refund>           _ => 0          </refund>
         <gasPrice>         _ => 0          </gasPrice>
         <origin>           _ => .Account   </origin>
         <touchedAccounts>  _ => .Set       </touchedAccounts>
         <accessedAccounts> _ => .Set       </accessedAccounts>
         <createdAccounts>  _ => .Set       </createdAccounts>
         <versionedHashes>  _ => .List      </versionedHashes>

    syntax EthereumCommand ::= "clearBLOCK"
 // ---------------------------------------
    rule <k> clearBLOCK => .K ... </k>
         <previousHash>      _ => 0          </previousHash>
         <ommersHash>        _ => 0          </ommersHash>
         <coinbase>          _ => 0          </coinbase>
         <stateRoot>         _ => 0          </stateRoot>
         <transactionsRoot>  _ => 0          </transactionsRoot>
         <receiptsRoot>      _ => 0          </receiptsRoot>
         <logsBloom>         _ => .Bytes     </logsBloom>
         <difficulty>        _ => 0          </difficulty>
         <number>            _ => 0          </number>
         <gasLimit>          _ => 0          </gasLimit>
         <gasUsed>           _ => 0          </gasUsed>
         <timestamp>         _ => 0          </timestamp>
         <extraData>         _ => .Bytes     </extraData>
         <mixHash>           _ => 0          </mixHash>
         <blockNonce>        _ => 0          </blockNonce>
         <ommerBlockHeaders> _ => [ .JSONs ] </ommerBlockHeaders>
         <baseFee>           _ => 0          </baseFee>
         <withdrawalsRoot>   _ => 0          </withdrawalsRoot>
         <blobGasUsed>       _ => 0          </blobGasUsed>
         <excessBlobGas>     _ => 0          </excessBlobGas>
         <beaconRoot>        _ => 0          </beaconRoot>
         <requestsRoot>      _ => 0          </requestsRoot>
         <depositRequests>       _ => .Bytes </depositRequests>
         <withdrawalRequests>    _ => .Bytes </withdrawalRequests>
         <consolidationRequests> _ => .Bytes </consolidationRequests>

    syntax EthereumCommand ::= "clearNETWORK"
 // -----------------------------------------
    rule <k> clearNETWORK => .K ... </k>
         <statusCode>     _ => .StatusCode </statusCode>
         <accounts>       _ => .Bag        </accounts>
         <messages>       _ => .Bag        </messages>
         <withdrawals>    _ => .Bag        </withdrawals>
         <schedule>       _ => DEFAULT     </schedule>

```

### Loading State

-   `mkAcct_` creates an account with the supplied ID (assuming it's already been chopped to 160 bits).

```k
    syntax EthereumCommand ::= "mkAcct" Int
 // ---------------------------------------
    rule <k> mkAcct ACCT => #newAccount ACCT ... </k>
```

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

Here we perform pre-proccesing on account data which allows "pretty" specification of input.

```k
    rule <k> load "pre" : { (ACCTID:String) : ACCT } => mkAcct #parseAddr(ACCTID) ~> loadAccount #parseAddr(ACCTID) ACCT ... </k>

    syntax EthereumCommand ::= "loadAccount" Int JSON
 // -------------------------------------------------
    rule <k> loadAccount _ { .JSONs } => .K ... </k>

    rule <k> loadAccount ACCT { "balance" : (BAL:Int), REST => REST } ... </k>
         <account> <acctID> ACCT </acctID> <balance> _ => BAL </balance> ... </account>

    rule <k> loadAccount ACCT { "code" : (CODE:Bytes), REST => REST } ... </k>
         <account> <acctID> ACCT </acctID> <code> _ => CODE </code> ... </account>

    rule <k> loadAccount ACCT { "nonce" : (NONCE:Int), REST => REST } ... </k>
         <account> <acctID> ACCT </acctID> <nonce> _ => NONCE </nonce> ... </account>

    rule <k> loadAccount ACCT { "storage" : (STORAGE:Map), REST => REST } ... </k>
         <account> <acctID> ACCT </acctID> <origStorage> _ => STORAGE </origStorage> <storage> _ => STORAGE </storage> ... </account>
```

Here we load the environmental information.

```k
    rule <k> load "env" : { KEY : ((VAL:String) => #parseWord(VAL)) } ... </k>
      requires KEY in (SetItem("currentTimestamp") SetItem("currentGasLimit") SetItem("currentNumber") SetItem("currentDifficulty") SetItem("currentBaseFee") SetItem("currentRandom") SetItem("currentExcessBlobGas"))
    rule <k> load "env" : { KEY : ((VAL:String) => #parseHexWord(VAL)) } ... </k>
      requires KEY in (SetItem("currentCoinbase") SetItem("previousHash"))
 // ----------------------------------------------------------------------
    rule <k> load "env" : { "currentCoinbase"      : (CB:Int)     } => .K ... </k> <coinbase>      _ => CB     </coinbase>
    rule <k> load "env" : { "currentDifficulty"    : (DIFF:Int)   } => .K ... </k> <difficulty>    _ => DIFF   </difficulty>
    rule <k> load "env" : { "currentGasLimit"      : (GLIMIT:Int) } => .K ... </k> <gasLimit>      _ => GLIMIT </gasLimit>
    rule <k> load "env" : { "currentNumber"        : (NUM:Int)    } => .K ... </k> <number>        _ => NUM    </number>
    rule <k> load "env" : { "previousHash"         : (HASH:Int)   } => .K ... </k> <previousHash>  _ => HASH   </previousHash>
    rule <k> load "env" : { "currentTimestamp"     : (TS:Int)     } => .K ... </k> <timestamp>     _ => TS     </timestamp>
    rule <k> load "env" : { "currentBaseFee"       : (BF:Int)     } => .K ... </k> <baseFee>       _ => BF     </baseFee>
    rule <k> load "env" : { "currentRandom"        : (RANDAO:Int) } => .K ... </k> <mixHash>       _ => RANDAO </mixHash>
    rule <k> load "env" : { "currentExcessBlobGas" : (BGAS:Int)   } => .K ... </k> <excessBlobGas> _ => BGAS   </excessBlobGas>

    syntax KItem ::= "loadCallState" JSON
 // -------------------------------------
    rule <k> loadCallState { "data" : ( DATA:String => #parseByteStack( DATA ) ), _REST } ... </k>

    rule <k> loadCallState { "code" : CODE:Bytes, REST } => #loadProgram CODE ~> loadCallState { REST } ... </k>

    rule <k> loadCallState { "gas"      : GLIMIT:Int, REST => REST } ... </k> <gas> _ => GLIMIT </gas> <useGas> true  </useGas>
    rule <k> loadCallState { "gas"      :      _:Int, REST => REST } ... </k>                          <useGas> false </useGas>

    rule <k> loadCallState { "gasPrice" : GPRICE:Int, REST => REST } ... </k> <gasPrice>  _ => GPRICE </gasPrice>
    rule <k> loadCallState { "value"    : VALUE:Int , REST => REST } ... </k> <callValue> _ => VALUE  </callValue>
    rule <k> loadCallState { "data"     : DATA:Bytes, REST => REST } ... </k> <callData>  _ => DATA   </callData>

    rule <k> loadCallState { .JSONs } => .K ... </k>
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
    rule #asScheduleString("CancunToPragueAtTime15k")   => PRAGUE
```

- `#parseJSONs2List` parse a JSON object with string values into a list of value.
```k
   syntax List ::= "#parseJSONs2List" "(" JSONs ")" [function]
 // ----------------------------------------------------------
    rule #parseJSONs2List ( .JSONs ) => .List
    rule #parseJSONs2List ( (VAL:Bytes) , REST ) => ListItem(VAL) #parseJSONs2List ( REST )
    rule #parseJSONs2List ( [VS:JSONs], REST ) => ListItem(#parseJSONs2List(VS)) #parseJSONs2List ( REST )
```

The `"rlp"` key loads the block information.

```k
    rule <k> load "rlp"        : (VAL:String => #rlpDecode(#parseByteStack(VAL))) ... </k>
    rule <k> load "genesisRLP" : (VAL:String => #rlpDecode(#parseByteStack(VAL))) ... </k>
 // --------------------------------------------------------------------------------------
    rule <k> load "rlp" : [ [ HP, HO, HC, HR, HT, HE, HB, HD, HI, HL, HG, HS, HX, HM, HN, .JSONs ], BT, BU, .JSONs ]
          => load "transaction" : BT
         ...
         </k>
         <previousHash>      _ => #asWord(HP) </previousHash>
         <ommersHash>        _ => #asWord(HO) </ommersHash>
         <coinbase>          _ => #asWord(HC) </coinbase>
         <stateRoot>         _ => #asWord(HR) </stateRoot>
         <transactionsRoot>  _ => #asWord(HT) </transactionsRoot>
         <receiptsRoot>      _ => #asWord(HE) </receiptsRoot>
         <logsBloom>         _ => HB          </logsBloom>
         <difficulty>        _ => #asWord(HD) </difficulty>
         <number>            _ => #asWord(HI) </number>
         <gasLimit>          _ => #asWord(HL) </gasLimit>
         <gasUsed>           _ => #asWord(HG) </gasUsed>
         <timestamp>         _ => #asWord(HS) </timestamp>
         <extraData>         _ => HX          </extraData>
         <mixHash>           _ => #asWord(HM) </mixHash>
         <blockNonce>        _ => #asWord(HN) </blockNonce>
         <ommerBlockHeaders> _ => BU          </ommerBlockHeaders>

    rule <k> load "rlp" : [ [ HP, HO, HC, HR, HT, HE, HB, HD, HI, HL, HG, HS, HX, HM, HN, HF, .JSONs ], BT, BU, .JSONs ]
          => load "rlp" : [ [ HP, HO, HC, HR, HT, HE, HB, HD, HI, HL, HG, HS, HX, HM, HN, .JSONs ], BT, BU, .JSONs ]
         ...
         </k>
         <baseFee> _ => #asWord(HF) </baseFee>

    rule <k> load "rlp" : [ [ HP, HO, HC, HR, HT, HE, HB, HD, HI, HL, HG, HS, HX, HM, HN, HF, WR, .JSONs ], BT, BU, BW, .JSONs ]
          => load "rlp" : [ [ HP, HO, HC, HR, HT, HE, HB, HD, HI, HL, HG, HS, HX, HM, HN, HF, .JSONs ], BT, BU, .JSONs ]
          ~> load "withdraw" : BW
         ...
         </k>
         <withdrawalsRoot> _ => #asWord(WR) </withdrawalsRoot>

    rule <k> load "rlp" : [ [ HP, HO, HC, HR, HT, HE, HB, HD, HI, HL, HG, HS, HX, HM, HN, HF, WR, UB, EB, BR, .JSONs ], BT, BU, BW, .JSONs ]
          => load "rlp" : [ [ HP, HO, HC, HR, HT, HE, HB, HD, HI, HL, HG, HS, HX, HM, HN, HF, WR, .JSONs ], BT, BU, BW, .JSONs ]
         ...
         </k>
         <blobGasUsed>   _ => #asWord(UB)      </blobGasUsed>
         <excessBlobGas> _ => #asWord(EB)      </excessBlobGas>
         <beaconRoot>    _ => #asWord(BR)      </beaconRoot>

    rule <k> load "rlp" : [ [ HP, HO, HC, HR, HT, HE, HB, HD, HI, HL, HG, HS, HX, HM, HN, HF, WR, UB, EB, BR, RR, .JSONs ], BT, BU, BW, .JSONs ]
          => load "rlp" : [ [ HP, HO, HC, HR, HT, HE, HB, HD, HI, HL, HG, HS, HX, HM, HN, HF, WR, UB, EB, BR, .JSONs ], BT, BU, BW, .JSONs ]
         ...
         </k>
         <requestsRoot> _ => #asWord(RR) </requestsRoot>

    rule <k> load "genesisRLP": [ [ HP, HO, HC, HR, HT, HE, HB, HD, HI, HL, HG, HS, HX, HM, HN, HF, WR, UB, EB, BR, RR, .JSONs ], _, _, _, .JSONs ] => .K ... </k>
         <blockhashes> .List => ListItem(#blockHeaderHash(HP, HO, HC, HR, HT, HE, HB, HD, HI, HL, HG, HS, HX, HM, HN, HF, WR, UB, EB, BR, RR)) ListItem(#asWord(HP)) </blockhashes>

    rule <k> load "genesisRLP": [ [ HP, HO, HC, HR, HT, HE, HB, HD, HI, HL, HG, HS, HX, HM, HN, HF, WR, UB, EB, BR, .JSONs ], _, _, _, .JSONs ] => .K ... </k>
         <blockhashes> .List => ListItem(#blockHeaderHash(HP, HO, HC, HR, HT, HE, HB, HD, HI, HL, HG, HS, HX, HM, HN, HF, WR, UB, EB, BR)) ListItem(#asWord(HP)) </blockhashes>
         <previousExcessBlobGas> 0 => #asWord(EB) </previousExcessBlobGas>
         <previousBlobGasUsed>   0 => #asWord(UB) </previousBlobGasUsed>

    rule <k> load "genesisRLP": [ [ HP, HO, HC, HR, HT, HE:Bytes, HB, HD, HI, HL, HG, HS, HX, HM, HN, HF, WR, .JSONs ], _, _, _, .JSONs ] => .K ... </k>
         <blockhashes> .List => ListItem(#blockHeaderHash(HP, HO, HC, HR, HT, HE, HB, HD, HI, HL, HG, HS, HX, HM, HN, HF, WR)) ListItem(#asWord(HP)) ... </blockhashes>

    rule <k> load "genesisRLP": [ [ HP, HO, HC, HR, HT, HE:Bytes, HB, HD, HI, HL, HG, HS, HX, HM, HN, .JSONs ], _, _, .JSONs ] => .K ... </k>
         <blockhashes> .List => ListItem(#blockHeaderHash(HP, HO, HC, HR, HT, HE, HB, HD, HI, HL, HG, HS, HX, HM, HN)) ListItem(#asWord(HP)) ... </blockhashes>

    rule <k> load "genesisRLP": [ [ HP, HO, HC, HR, HT, HE:Bytes, HB, HD, HI, HL, HG, HS, HX, HM, HN, HF, .JSONs ], _, _, .JSONs ] => .K ... </k>
         <blockhashes> .List => ListItem(#blockHeaderHash(HP, HO, HC, HR, HT, HE, HB, HD, HI, HL, HG, HS, HX, HM, HN, HF)) ListItem(#asWord(HP)) ... </blockhashes>

    syntax Int ::= "#newWithdrawalID" "(" List ")" [function]
 // ---------------------------------------------------------
    rule #newWithdrawalID (.List) => 0
    rule #newWithdrawalID (_ ListItem(I)) => I +Int 1

    syntax EthereumCommand ::= "mkWD" Int
 // -------------------------------------
    rule <k> mkWD (WDID => WDID +Int 1) ... </k>
         <withdrawal> <withdrawalID> WDID </withdrawalID> ... </withdrawal>

    rule <k> mkWD WDID => .K ... </k>
         <withdrawalsOrder>   ... (.List => ListItem(WDID)) </withdrawalsOrder>
         <withdrawalsPending> ... (.List => ListItem(WDID)) </withdrawalsPending>
         <withdrawals>
            ( .Bag
           => <withdrawal>
                <withdrawalID> WDID </withdrawalID>
                ...
              </withdrawal>
            )
            ...
          </withdrawals> [owise]

    syntax EthereumCommand ::= "loadWithdraw" JSON
 // ----------------------------------------------
    rule <k> loadWithdraw [ INDEX , VALIDATOR , ACCT , VALUE , .JSONs ] => .K ... </k>
         <withdrawalsOrder> ... ListItem(WID) </withdrawalsOrder>
         <withdrawal>
              <withdrawalID>   WID                     </withdrawalID>
              <index>          _ => #asWord(INDEX)     </index>
              <validatorIndex> _ => #asWord(VALIDATOR) </validatorIndex>
              <address>        _ => #asAccount(ACCT)   </address>
              <amount>         _ => #asWord(VALUE)     </amount>
         </withdrawal>

    rule <k> load "withdraw" : [ .JSONs ]          => .K ... </k>
    rule <k> load "withdraw" : [ WITHDRAW , REST ] => mkWD #newWithdrawalID(WIDS) ~> loadWithdraw WITHDRAW ~> load "withdraw" : [ REST ] ... </k>
         <withdrawalsOrder> WIDS </withdrawalsOrder>

    syntax EthereumCommand ::= "mkTX" Int
 // -------------------------------------
    rule <k> mkTX TXID => .K ... </k>
         <chainID> CID </chainID>
         <txOrder>   ... (.List => ListItem(TXID)) </txOrder>
         <txPending> ... (.List => ListItem(TXID)) </txPending>
         <messages>
            ( .Bag
           => <message>
                <msgID>      TXID:Int </msgID>
                <txGasPrice> 20000000000   </txGasPrice>
                <txGasLimit> 90000         </txGasLimit>
                <txChainID>  CID           </txChainID>
                ...
              </message>
            )
          ...
          </messages>

    rule <k> load "transaction" : [ (T => [#rlpDecodeTransaction(T)]) , _ ] ... </k>

    rule <k> load "transaction" : [ [ TN , TP , TG , TT , TV , TI , TW , TR , TS ] , REST ]
          => mkTX !ID:Int
          ~> loadTransaction !ID { "data"  : TI   ,   "gasLimit" : TG   ,   "gasPrice"             : TP
                                 , "nonce" : TN   ,   "r"        : TR   ,   "s"                    : TS
                                 , "to"    : TT   ,   "v"        : TW   ,   "value"                : TV
                                 , "type"  : #dasmTxPrefix(Legacy)      ,   "maxPriorityFeePerGas" : TP
                                 , "maxFeePerGas": TP                   ,   "maxFeePerBlobGas"     : 0
                                 , "blobVersionedHashes" : [ .JSONs ]   , .JSONs
                                 }
          ~> load "transaction" : [ REST ]
          ...
          </k>

    rule <k> load "transaction" : [ [TYPE , [TC, TN, TP, TG, TT, TV, TI, TA, TY , TR, TS ]] , REST ]
          => mkTX !ID:Int
          ~> loadTransaction !ID { "data"       : TI   ,   "gasLimit" : TG   ,   "gasPrice"          : TP
                                 , "nonce"      : TN   ,   "r"        : TR   ,   "s"                 : TS
                                 , "to"         : TT   ,   "v"        : TY   ,   "value"             : TV
                                 , "accessList" : TA   ,   "type"     : TYPE ,   "chainID"           : TC
                                 , "maxPriorityFeePerGas" : TP               , "maxFeePerGas"        : TP
                                 , "maxFeePerBlobGas"     : 0                , "blobVersionedHashes" : [ .JSONs ] 
                                 , .JSONs
                                 }
          ~> load "transaction" : [ REST ]
          ...
         </k>
    requires #asWord(TYPE) ==Int #dasmTxPrefix(AccessList)


    rule <k> load "transaction" : [ [TYPE , [TC, TN, TP, TF, TG, TT, TV, TI, TA, TY , TR, TS ]] , REST ]
          => mkTX !ID:Int
          ~> loadTransaction !ID { "data"         : TI   ,   "gasLimit" : TG   ,   "maxPriorityFeePerGas" : TP
                                 , "nonce"        : TN   ,   "r"        : TR   ,   "s"                    : TS
                                 , "to"           : TT   ,   "v"        : TY   ,   "value"                : TV
                                 , "accessList"   : TA   ,   "type"     : TYPE ,   "chainID"              : TC
                                 , "maxFeePerGas" : TF   ,   "maxFeePerBlobGas"                           : 0
                                 , "blobVersionedHashes" : [ .JSONs ]          , .JSONs
                                 }
          ~> load "transaction" : [ REST ]
          ...
         </k>
    requires #asWord(TYPE) ==Int #dasmTxPrefix(DynamicFee)

     rule <k> load "transaction" : [ [TYPE , [TC, TN, TP, TF, TG, TT, TV, TI, TA, TB, TVH, TY, TR, TS ]] , REST ]
          => mkTX !ID:Int
          ~> loadTransaction !ID { "data"         : TI   ,   "gasLimit"         : TG   ,   "maxPriorityFeePerGas" : TP
                                 , "nonce"        : TN   ,   "r"                : TR   ,   "s"                    : TS
                                 , "to"           : TT   ,   "v"                : TY   ,   "value"                : TV
                                 , "accessList"   : TA   ,   "type"             : TYPE ,   "chainID"              : TC
                                 , "maxFeePerGas" : TF   ,   "maxFeePerBlobGas" : TB   ,   "blobVersionedHashes"  : TVH
                                 , .JSONs
                                 }
          ~> load "transaction" : [ REST ]
          ...
         </k>
    requires #asWord(TYPE) ==Int #dasmTxPrefix(Blob)

     rule <k> load "transaction" : [ [TYPE , [TC, TN, TP, TF, TG, TT, TV, TI, TA, AUTH , TY, TR, TS ]] , REST ]
          => mkTX !ID:Int
          ~> loadTransaction !ID { "data"         : TI   ,   "gasLimit"         : TG   ,   "maxPriorityFeePerGas" : TP
                                 , "nonce"        : TN   ,   "r"                : TR   ,   "s"                    : TS
                                 , "to"           : TT   ,   "v"                : TY   ,   "value"                : TV
                                 , "accessList"   : TA   ,   "type"             : TYPE ,   "chainID"              : TC
                                 , "maxFeePerGas" : TF   ,   "authList"         : AUTH , .JSONs }
          ~> load "transaction" : [ REST ]
          ...
         </k>
    requires #asWord(TYPE) ==Int #dasmTxPrefix(SetCode)

    syntax EthereumCommand ::= "loadTransaction" Int JSON
 // -----------------------------------------------------
    rule <k> loadTransaction _ { .JSONs } => .K ... </k>

    rule <k> loadTransaction TXID { GLIMIT : TG:Int, REST => REST } ... </k>
         <message> <msgID> TXID </msgID> <txGasLimit> _ => TG </txGasLimit> ... </message>
      requires GLIMIT in (SetItem("gas") SetItem("gasLimit"))

    rule <k> loadTransaction TXID { "gasPrice" : TP:Int, REST => REST } ... </k>
         <message> <msgID> TXID </msgID> <txGasPrice> _ => TP </txGasPrice> ... </message>

    rule <k> loadTransaction TXID { "nonce" : TN:Int, REST => REST } ... </k>
         <message> <msgID> TXID </msgID> <txNonce> _ => TN </txNonce> ... </message>

    rule <k> loadTransaction TXID { "value" : TV:Int, REST => REST } ... </k>
         <message> <msgID> TXID </msgID> <value> _ => TV </value> ... </message>

    rule <k> loadTransaction TXID { "to" : TT:Account, REST => REST } ... </k>
         <message> <msgID> TXID </msgID> <to> _ => TT </to> ... </message>

    rule <k> loadTransaction TXID { "data" : TI:Bytes, REST => REST } ... </k>
         <message> <msgID> TXID </msgID> <data> _ => TI </data> ... </message>

    rule <k> loadTransaction TXID { "v" : TW:Int, REST => REST } ... </k>
         <message> <msgID> TXID </msgID> <sigV> _ => TW </sigV> ... </message>

    rule <k> loadTransaction TXID { "r" : TR:Bytes, REST => REST } ... </k>
         <message> <msgID> TXID </msgID> <sigR> _ => TR </sigR> ... </message>

    rule <k> loadTransaction TXID { "s" : TS:Bytes, REST => REST } ... </k>
         <message> <msgID> TXID </msgID> <sigS> _ => TS </sigS> ... </message>

    rule <k> loadTransaction TXID { "type" : T:Int, REST => REST } ... </k>
         <message> <msgID> TXID </msgID> <txType> _ => #asmTxPrefix(T) </txType> ... </message>

    rule <k> loadTransaction TXID { "chainID" : TC:Int, REST => REST } ... </k>
         <message> <msgID> TXID </msgID> <txChainID> _ => TC </txChainID> ... </message>

    rule <k> loadTransaction TXID { "accessList" : [TA:JSONs], REST => REST } ... </k>
         <message> <msgID> TXID </msgID> <txAccess> _ => [TA] </txAccess> ... </message>

    rule <k> loadTransaction TXID { "maxPriorityFeePerGas" : TP:Int, REST => REST } ... </k>
         <message> <msgID> TXID </msgID> <txPriorityFee> _ => TP </txPriorityFee> ... </message>

    rule <k> loadTransaction TXID { "maxFeePerGas" : TF:Int, REST => REST } ... </k>
         <message> <msgID> TXID </msgID> <txMaxFee> _ => TF </txMaxFee> ... </message>

    rule <k> loadTransaction TXID { "maxFeePerBlobGas" : TB:Int, REST => REST } ... </k>
         <message> <msgID> TXID </msgID> <txMaxBlobFee> _ => TB </txMaxBlobFee> ... </message>

    rule <k> loadTransaction TXID { "blobVersionedHashes" : [TVH:JSONs], REST => REST } ... </k>
         <message> <msgID> TXID </msgID> <txVersionedHashes> _ => #parseJSONs2List(TVH) </txVersionedHashes> ... </message>

    rule <k> loadTransaction TXID { "authList" : [AUTH:JSONs], REST => REST } ... </k>
         <message> <msgID> TXID </msgID> <txAuthList> _ => #parseJSONs2List(AUTH) </txAuthList> ... </message>
```

### Getting State

- `#getTxData` will pull the parameters of TXID into an appropriate `TxData` sort

```k
    syntax TxData ::= #getTxData ( Int ) [symbol(getTxData), function]
 // ------------------------------------------------------------------
    rule [[ #getTxData( TXID ) => LegacyTxData(TN, TP, TG, TT, TV, DATA) ]]
         <message>
           <msgID>      TXID </msgID>
           <txNonce>    TN   </txNonce>
           <txGasPrice> TP   </txGasPrice>
           <txGasLimit> TG   </txGasLimit>
           <to>         TT   </to>
           <value>      TV   </value>
           <sigV>       TW   </sigV>
           <data>       DATA </data>
           <txType> Legacy </txType>
           ...
         </message>
      requires TW ==Int 0 orBool TW ==Int 1 orBool TW ==Int 27 orBool TW ==Int 28

    rule [[ #getTxData( TXID ) => LegacySignedTxData(TN, TP, TG, TT, TV, DATA, B) ]]
         <chainID> B </chainID>
         <message>
           <msgID>      TXID </msgID>
           <txNonce>    TN   </txNonce>
           <txGasPrice> TP   </txGasPrice>
           <txGasLimit> TG   </txGasLimit>
           <to>         TT   </to>
           <value>      TV   </value>
           <sigV>       TW   </sigV>
           <data>       DATA </data>
           <txType> Legacy </txType>
           ...
         </message>
      requires TW ==Int 2 *Int B +Int 35 orBool TW ==Int 2 *Int B +Int 36

    rule [[ #getTxData( TXID ) => AccessListTxData(TN, TP, TG, TT, TV, DATA, CID, TA) ]]
         <message>
           <msgID>      TXID </msgID>
           <txNonce>    TN   </txNonce>
           <txGasPrice> TP   </txGasPrice>
           <txGasLimit> TG   </txGasLimit>
           <to>         TT   </to>
           <value>      TV   </value>
           <data>       DATA </data>
           <txChainID>  CID  </txChainID>
           <txAccess>   TA   </txAccess>
           <txType> AccessList </txType>
           ...
         </message>

    rule [[ #getTxData( TXID ) => DynamicFeeTxData(TN, TPF, TM, TG, TT, TV, DATA, CID, TA) ]]
         <message>
           <msgID>         TXID </msgID>
           <txNonce>       TN   </txNonce>
           <txGasLimit>    TG   </txGasLimit>
           <to>            TT   </to>
           <value>         TV   </value>
           <data>          DATA </data>
           <txChainID>     CID  </txChainID>
           <txAccess>      TA   </txAccess>
           <txPriorityFee> TPF  </txPriorityFee>
           <txMaxFee>      TM   </txMaxFee>
           <txType> DynamicFee </txType>
           ...
         </message>

    rule [[ #getTxData( TXID ) => BlobTxData(TN, TPF, TM, TG, TT, TV, DATA, CID, TA, TB, TVH) ]]
         <message>
           <msgID>             TXID </msgID>
           <txNonce>           TN   </txNonce>
           <txGasLimit>        TG   </txGasLimit>
           <to>                TT   </to>
           <value>             TV   </value>
           <data>              DATA </data>
           <txChainID>         CID  </txChainID>
           <txAccess>          TA   </txAccess>
           <txPriorityFee>     TPF  </txPriorityFee>
           <txMaxFee>          TM   </txMaxFee>
           <txMaxBlobFee>      TB   </txMaxBlobFee>
           <txVersionedHashes> TVH  </txVersionedHashes>
           <txType> Blob </txType>
           ...
         </message>

    rule [[ #getTxData( TXID ) => SetCodeTxData(TN, TPF, TM, TG, TT, TV, DATA, CID, TA, AUTH) ]]
         <message>
           <msgID>             TXID </msgID>
           <txNonce>           TN   </txNonce>
           <txGasLimit>        TG   </txGasLimit>
           <to>                TT   </to>
           <value>             TV   </value>
           <data>              DATA </data>
           <txChainID>         CID  </txChainID>
           <txAccess>          TA   </txAccess>
           <txPriorityFee>     TPF  </txPriorityFee>
           <txMaxFee>          TM   </txMaxFee>
           <txAuthList>        AUTH </txAuthList>
           <txType> SetCode </txType>
           ...
         </message>
```

- `#effectiveGasPrice` will compute the gas price for TXID, as specified by EIP-1559

```k
    syntax Int ::= #effectiveGasPrice( Int ) [symbol(#effectiveGasPrice), function]
 // -------------------------------------------------------------------------------
    rule [[ #effectiveGasPrice( TXID )
         => #if ( notBool Ghasbasefee << SCHED >> )
                orBool TXTYPE ==K Legacy
                orBool TXTYPE ==K AccessList
              #then GPRICE
              #else BFEE +Int minInt(TPF, TM -Int BFEE)
            #fi
         ]]
         <schedule> SCHED </schedule>
         <baseFee> BFEE </baseFee>
         <message>
           <msgID>         TXID   </msgID>
           <txGasPrice>    GPRICE </txGasPrice>
           <txType>        TXTYPE </txType>
           <txPriorityFee> TPF    </txPriorityFee>
           <txMaxFee>      TM     </txMaxFee>
           ...
         </message>
```

- `#isValidTransaction(TXID, SENDER)` - validate each defined transaction type.
 1. Check if the tx nonce matches the nonce of the sender.
 2. Check that the gas fees are properly structured and that the fee caps are not higher than the max amount.
 3. Check that there is enough balance for gas, value and blob fees (where applicable) and that the gas limit is within the block limits.

```k
    syntax Bool ::= #isValidTransaction( Int , Account ) [symbol(#isValidTransaction), function]
 // --------------------------------------------------------------------------------------------
    rule [[ #isValidTransaction (TXID, ACCTFROM) => true ]]
         <schedule> SCHED </schedule>
         <baseFee> BASE_FEE </baseFee>
         <gasLimit> BLOCK_GAS_LIMIT </gasLimit>
         <account>
           <acctID>  ACCTFROM  </acctID>
           <balance> BAL       </balance>
           <code>    ACCTCODE  </code>
           <nonce>   ACCTNONCE </nonce>
           ...
         </account>
         <message>
           <msgID>             TXID                </msgID>
           <txNonce>           TX_NONCE            </txNonce>
           <txGasLimit>        TX_GAS_LIMIT        </txGasLimit>
           <to>                ACCTTO              </to>
           <value>             VALUE               </value>
           <txPriorityFee>     TX_MAX_PRIORITY_FEE </txPriorityFee>
           <txMaxFee>          TX_MAX_FEE          </txMaxFee>
           <txAuthList>        TX_AUTH_LIST        </txAuthList>
           <txType> SetCode </txType>
           ...
         </message>
     requires (ACCTCODE ==K .Bytes orBool Ghasauthority << SCHED >>)
      andBool notBool ACCTTO ==K .Account
      andBool ACCTNONCE ==Int TX_NONCE
      andBool BASE_FEE <=Int TX_MAX_FEE
      andBool TX_MAX_PRIORITY_FEE <=Int TX_MAX_FEE
      andBool BAL >=Int TX_GAS_LIMIT *Int TX_MAX_FEE +Int VALUE
      andBool TX_GAS_LIMIT <=Int BLOCK_GAS_LIMIT
      andBool size(TX_AUTH_LIST) >Int 0 andBool #checkAuthorityList(TX_AUTH_LIST)

    rule [[ #isValidTransaction (TXID, ACCTFROM) => true ]]
         <schedule> SCHED </schedule>
         <baseFee> BASE_FEE </baseFee>
         <excessBlobGas> EXCESS_BLOB_GAS </excessBlobGas>
         <gasLimit> BLOCK_GAS_LIMIT </gasLimit>
         <account>
           <acctID>  ACCTFROM  </acctID>
           <balance> BAL       </balance>
           <code>    ACCTCODE  </code>
           <nonce>   ACCTNONCE </nonce>
           ...
         </account>
         <message>
           <msgID>             TXID                </msgID>
           <txNonce>           TX_NONCE            </txNonce>
           <txGasLimit>        TX_GAS_LIMIT        </txGasLimit>
           <to>                ACCTTO              </to>
           <value>             VALUE               </value>
           <txPriorityFee>     TX_MAX_PRIORITY_FEE </txPriorityFee>
           <txMaxFee>          TX_MAX_FEE          </txMaxFee>
           <txMaxBlobFee>      TX_MAX_BLOB_FEE     </txMaxBlobFee>
           <txVersionedHashes> TVH                 </txVersionedHashes>
           <txType> Blob </txType>
           ...
         </message>
     requires (ACCTCODE ==K .Bytes orBool Ghasauthority << SCHED >>)
      andBool notBool ACCTTO ==K .Account
      andBool ACCTNONCE ==Int TX_NONCE
      andBool BASE_FEE <=Int TX_MAX_FEE
      andBool TX_MAX_PRIORITY_FEE <=Int TX_MAX_FEE
      andBool size(TVH) >Int 0 andBool #checkTxVersionedHashes(TVH)
      andBool TX_MAX_BLOB_FEE >=Int Cbasefeeperblob(SCHED, EXCESS_BLOB_GAS)
      andBool BAL >=Int TX_GAS_LIMIT *Int TX_MAX_FEE +Int (Ctotalblob(SCHED, size(TVH)) *Int TX_MAX_BLOB_FEE) +Int VALUE
      andBool TX_GAS_LIMIT <=Int BLOCK_GAS_LIMIT
      andBool Ctotalblob(SCHED, size(TVH)) <=Int Gmaxblobgas < SCHED>

    rule [[ #isValidTransaction (TXID, ACCTFROM) => true ]]
         <schedule> SCHED </schedule>
         <baseFee> BASE_FEE </baseFee>
         <gasLimit> BLOCK_GAS_LIMIT </gasLimit>
         <account>
           <acctID>  ACCTFROM  </acctID>
           <balance> BAL       </balance>
           <code>    ACCTCODE  </code>
           <nonce>   ACCTNONCE </nonce>
           ...
         </account>
         <message>
           <msgID>             TXID                </msgID>
           <txNonce>           TX_NONCE            </txNonce>
           <txGasLimit>        TX_GAS_LIMIT        </txGasLimit>
           <value>             VALUE               </value>
           <txPriorityFee>     TX_MAX_PRIORITY_FEE </txPriorityFee>
           <txMaxFee>          TX_MAX_FEE          </txMaxFee>
           <txType> DynamicFee </txType>
           ...
         </message>
     requires (ACCTCODE ==K .Bytes orBool Ghasauthority << SCHED >>)
      andBool ACCTNONCE ==Int TX_NONCE
      andBool BASE_FEE <=Int TX_MAX_FEE
      andBool TX_MAX_PRIORITY_FEE <=Int TX_MAX_FEE
      andBool BAL >=Int TX_GAS_LIMIT *Int TX_MAX_FEE +Int VALUE
      andBool TX_GAS_LIMIT <=Int BLOCK_GAS_LIMIT

    rule [[ #isValidTransaction (TXID, ACCTFROM) => true ]]
         <schedule> SCHED </schedule>
         <baseFee> BASE_FEE </baseFee>
         <gasLimit> BLOCK_GAS_LIMIT </gasLimit>
         <account>
           <acctID>  ACCTFROM  </acctID>
           <balance> BAL       </balance>
           <code>    ACCTCODE   </code>
           <nonce>   ACCTNONCE </nonce>
           ...
         </account>
         <message>
           <msgID>             TXID                </msgID>
           <txNonce>           TX_NONCE            </txNonce>
           <txGasPrice>        TX_GAS_PRICE        </txGasPrice>
           <txGasLimit>        TX_GAS_LIMIT        </txGasLimit>
           <value>             VALUE               </value>
           <txType> TXTYPE </txType>
           ...
         </message>
     requires #dasmTxPrefix(TXTYPE) <Int 2
      andBool (ACCTCODE ==K .Bytes orBool Ghasauthority << SCHED >>)
      andBool ACCTNONCE ==Int TX_NONCE
      andBool BASE_FEE <=Int TX_GAS_PRICE
      andBool BAL >=Int TX_GAS_LIMIT *Int TX_GAS_PRICE +Int VALUE
      andBool TX_GAS_LIMIT <=Int BLOCK_GAS_LIMIT

    rule #isValidTransaction (_, _) => false [owise]
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
