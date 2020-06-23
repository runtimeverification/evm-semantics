Web3 RPC JSON Handler
=====================

```k
requires "evm.md"
requires "state-loader.md"
requires "json.md"
```

```k
module WEB3
    imports STATE-LOADER
    imports JSON-RPC
    imports K-IO

    configuration
      <kevm-client>
        <kevm/>
        <json-rpc/>
        <blockchain>
          <blockList> .List </blockList>
        </blockchain>
        <stateTrie> .MerkleTree </stateTrie>
        <defaultGasPrice> 20000000000 </defaultGasPrice>
        <defaultGasLimit> 90000       </defaultGasLimit>
        <timeDiff>        0           </timeDiff> // Gets added to #time() when updating <timestamp>
        <accountKeys>     .Map        </accountKeys>
        <nextFilterSlot>  0           </nextFilterSlot>
        <txReceipts>
          <txReceipt multiplicity ="*" type="Map">
            <txHash>          "":String  </txHash>
            <txCumulativeGas> 0          </txCumulativeGas>
            <logSet>          .List      </logSet>
            <bloomFilter>     .ByteArray </bloomFilter>
            <txStatus>        0          </txStatus>
            <txID>            0          </txID>
            <sender>          .Account   </sender>
            <txBlockNumber>   0          </txBlockNumber>
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
        <web3shutdownable>  $SHUTDOWNABLE:Bool  </web3shutdownable>
        <web3notifications> $NOTIFICATIONS:Bool </web3notifications>
      </kevm-client>
```

The Blockchain State
--------------------

A `BlockchainItem` contains the information of a block and its network state.
The `blockList` cell stores a list of previous blocks and network states.
-   `#pushBlockchainState` saves a copy of the block state and network state as a `BlockchainItem` in the `blockList` cell.
-   `#getBlockByNumber(BlockIdentifier, List, Block)` retrieves a specific `BlockchainItem` from the `blockList` cell.

```k
    syntax BlockchainItem ::= ".BlockchainItem"
                            | "{" NetworkCell "|" BlockCell "}"
 // -----------------------------------------------------------

    syntax KItem ::= "#pushBlockchainState"
 // ---------------------------------------
    rule <k> #pushBlockchainState => . ... </k>
         <blockList> (.List => ListItem({ <network> NETWORK </network> | <block> BLOCK </block> })) ... </blockList>
         <network> NETWORK </network>
         <blockhashes> (.List => ListItem(#blockchainItemHash({ <network> NETWORK </network> | <block> BLOCK </block> }))) ... </blockhashes>
         <block>   BLOCK   </block>

    syntax BlockchainItem ::= #getBlockByNumber ( BlockIdentifier , List , BlockchainItem ) [function]
 // --------------------------------------------------------------------------------------------------
    rule #getBlockByNumber( _:Int            , .List                 , _     ) => .BlockchainItem
    rule #getBlockByNumber( LATEST           , .List                 , BLOCK ) => BLOCK
    rule #getBlockByNumber( LATEST           ,   ListItem( BLOCK ) _ , _     ) => BLOCK
    rule #getBlockByNumber( PENDING => LATEST, _                     , _     )
    rule #getBlockByNumber( EARLIEST         , .List                 , BLOCK ) => BLOCK
    rule #getBlockByNumber( EARLIEST         , _ ListItem( BLOCK )   , _     ) => BLOCK

    rule #getBlockByNumber(BLOCKNUM:Int ,  ListItem({ _ | <block> <number> BLOCKNUM </number> ... </block> } #as BLOCK)           REST, _ ) => BLOCK
    rule #getBlockByNumber(BLOCKNUM':Int, (ListItem({ _ | <block> <number> BLOCKNUM </number> ... </block> }          ) => .List)    _, _ )
      requires BLOCKNUM =/=Int BLOCKNUM'

    syntax AccountItem ::= AccountCell | ".AccountItem"
 // ---------------------------------------------------

    syntax AccountItem ::= #getAccountFromBlockchainItem( BlockchainItem , Int ) [function]
 // ---------------------------------------------------------------------------------------
    rule #getAccountFromBlockchainItem ( { <network> <accounts> (<account> <acctID> ACCT </acctID> ACCOUNTDATA </account>) ... </accounts>  ... </network> | _ } , ACCT ) => <account> <acctID> ACCT </acctID> ACCOUNTDATA </account>
    rule #getAccountFromBlockchainItem(_, _) => .AccountItem [owise]

    syntax KItem ::= #getAccountAtBlock ( BlockIdentifier , Int )
 // -------------------------------------------------------------
    rule <k> #getAccountAtBlock(BLOCKNUM , ACCTID)
          => #getAccountFromBlockchainItem(#getBlockByNumber(BLOCKNUM, BLOCKLIST, {<network> NETWORK </network> | <block> BLOCK </block>}), ACCTID) ... </k>
         <blockList> BLOCKLIST </blockList>
         <network>   NETWORK   </network>
         <block>     BLOCK     </block>

    syntax Int ::= #getNumberFromBlockchainItem (BlockchainItem) [function]
 // -----------------------------------------------------------------------
    rule #getNumberFromBlockchainItem({ _ | <block> <number> BLOCKNUM </number> ... </block> }) => BLOCKNUM

    syntax Int ::= #getNumberAtBlock ( BlockIdentifier , List , BlockchainItem ) [function]
 // ---------------------------------------------------------------------------------------
    rule #getNumberAtBlock (X:Int     , _        , _     ) => X
    rule #getNumberAtBlock (BLOCKID   , BLOCKLIST, BLOCK ) => #getNumberFromBlockchainItem(#getBlockByNumber(BLOCKID, BLOCKLIST, BLOCK)) [owise]
```

WEB3 JSON RPC
-------------

```k
    syntax JSON ::= #getJSON ( JSONKey , JSON ) [function]
 // ------------------------------------------------------
    rule #getJSON( KEY, { KEY : J, _ } )     => J
    rule #getJSON( _, { .JSONs } )           => undef
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

    syntax KItem ::= getRequest()
 // -----------------------------
    rule <k> getRequest() => #loadRPCCall(#getRequest(FD)) ... </k>
         <web3input> FD </web3input>
         <batch> _ => undef </batch>

    syntax IOJSON ::= #getRequest(Int) [function, hook(JSON.read)]
 // --------------------------------------------------------------

    syntax K ::= #putResponse(JSON, Int) [function, hook(JSON.write)]
 // -----------------------------------------------------------------

    syntax IOJSON ::= #putResponseError ( JSON ) [klabel(JSON-RPC_putResponseError), symbol]
 // ----------------------------------------------------------------------------------------

    syntax KItem ::= #loadRPCCall(IOJSON)
 // -------------------------------------
    rule <k> #loadRPCCall({ _ } #as J) => #checkRPCCall ~> #runRPCCall ... </k>
         <jsonrpc> _ => #getJSON("jsonrpc", J) </jsonrpc>
         <callid>  _ => #getJSON("id"     , J) </callid>
         <method>  _ => #getJSON("method" , J) </method>
         <params>  _ => #getJSON("params" , J) </params>

    rule <k> #loadRPCCall(#EOF) => accept() ... </k>

    rule <k> #loadRPCCall([ _, _ ] #as J) => #loadFromBatch ... </k>
         <batch> _ => J </batch>
         <web3response> _ => .List </web3response>

    rule <k> #loadRPCCall(_:String #Or null #Or _:Int #Or [ .JSONs ]) => #rpcResponseError(-32600,  "Invalid Request") ... </k>
         <callid> _ => null </callid>

    rule <k> #loadRPCCall(undef) => #rpcResponseError(-32700,  "Parse error") ... </k>
         <callid> _ => null </callid>

    syntax KItem ::= "#loadFromBatch"
 // ---------------------------------
    rule <k> #loadFromBatch ~> _ => #loadRPCCall(J) </k>
         <batch> [ J , JS => JS ] </batch>

    rule <k> #loadFromBatch ~> _ => #putResponse(List2JSON(RESPONSE), FD) ~> getRequest() </k>
         <batch> [ .JSONs ] </batch>
         <web3output> FD </web3output>
         <web3response> RESPONSE </web3response>
      requires size(RESPONSE) >Int 0

    rule <k> #loadFromBatch ~> _ => getRequest() </k>
         <batch> [ .JSONs ] </batch>
         <web3response> .List </web3response>

    syntax JSON ::= List2JSON(List)        [function]
                  | List2JSON(List, JSONs) [function, klabel(List2JSONAux)]
 // -----------------------------------------------------------------------
    rule List2JSON(L) => List2JSON(L, .JSONs)

    rule List2JSON(L ListItem(J), JS) => List2JSON(L, (J, JS))
    rule List2JSON(.List        , JS) => [ JS ]

    syntax KItem ::= #sendResponse ( JSONs )
 // ----------------------------------------
    rule <k> #sendResponse(J) ~> _ => #putResponse({ "jsonrpc": "2.0", "id": CALLID, J }, FD) ~> getRequest() </k>
         <callid>     CALLID </callid>
         <web3output> FD     </web3output>
         <batch>      undef  </batch>
      requires CALLID =/=K undef

    rule <k> #sendResponse(J) ~> _ => #putResponse({ "jsonrpc": "2.0", J }, FD) ~> getRequest() </k>
         <callid>            undef </callid>
         <web3output>        FD    </web3output>
         <batch>             undef </batch>
         <web3notifications> true  </web3notifications>

    rule <k> #sendResponse(_) ~> _ => getRequest() </k>
         <callid>            undef </callid>
         <batch>             undef </batch>
         <web3notifications> false </web3notifications>

    rule <k> #sendResponse(J) ~> _ => #loadFromBatch </k>
         <callid>           CALLID                                                   </callid>
         <batch>            [ _ ]                                                    </batch>
         <web3response> ... .List => ListItem({ "jsonrpc": "2.0", "id": CALLID, J }) </web3response>
      requires CALLID =/=K undef

    rule <k> #sendResponse(J) ~> _ => #loadFromBatch </k>
         <callid>           undef                                      </callid>
         <batch>            [ _ ]                                      </batch>
         <web3response> ... .List => ListItem({ "jsonrpc": "2.0", J }) </web3response>
         <web3notifications> true                                      </web3notifications>

    rule <k> #sendResponse(_) ~> _ => #loadFromBatch </k>
         <callid>            undef </callid>
         <batch>             [ _ ] </batch>
         <web3notifications> false </web3notifications>

    syntax KItem ::= #rpcResponseSuccess          ( JSON                )
                   | #rpcResponseSuccessException ( JSON , JSON         )
                   | #rpcResponseError            ( JSON                )
                   | #rpcResponseError            ( Int , String        )
                   | #rpcResponseError            ( Int , String , JSON )
                   | "#rpcResponseUnimplemented"
 // --------------------------------------------
    rule <k> #rpcResponseSuccess(J)                 => #sendResponse( "result" : J )                                                ... </k> requires isProperJson(J)
    rule <k> #rpcResponseSuccessException(RES, ERR) => #sendResponse( ( "result" : RES, "error": ERR ) )                            ... </k> requires isProperJson(RES) andBool isProperJson(ERR)
    rule <k> #rpcResponseError(ERR)                 => #sendResponse( "error" : ERR )                                               ... </k>
    rule <k> #rpcResponseError(CODE, MSG)           => #sendResponse( "error" : { "code": CODE , "message": MSG } )                 ... </k>
    rule <k> #rpcResponseError(CODE, MSG, DATA)     => #sendResponse( "error" : { "code": CODE , "message": MSG , "data" : DATA } ) ... </k> requires isProperJson(DATA)
    rule <k> #rpcResponseUnimplemented              => #sendResponse( "unimplemented" : RPCCALL )                                   ... </k> <method> RPCCALL </method>

    syntax KItem ::= "#checkRPCCall"
 // --------------------------------
    rule <k> #checkRPCCall => . ...</k>
         <jsonrpc> "2.0" </jsonrpc>
         <method> _:String </method>
         <params> undef #Or [ _ ] #Or { _ } </params>
         <callid> _:String #Or null #Or _:Int #Or undef </callid>

    rule <k> #checkRPCCall => #rpcResponseError(-32600, "Invalid Request") ... </k>
         <callid> undef #Or [ _ ] #Or { _ } => null </callid> [owise]

    rule <k> #checkRPCCall => #rpcResponseError(-32600, "Invalid Request") ... </k>
         <callid> _:Int </callid> [owise]

    rule <k> #checkRPCCall => #rpcResponseError(-32600, "Invalid Request") ... </k>
         <callid> _:String </callid> [owise]

    syntax KItem ::= "#runRPCCall"
 // ------------------------------
    rule <k> #runRPCCall => #net_version                             ... </k> <method> "net_version"                             </method>
    rule <k> #runRPCCall => #shh_version                             ... </k> <method> "shh_version"                             </method>

    rule <k> #runRPCCall => #web3_clientVersion                      ... </k> <method> "web3_clientVersion"                      </method>
    rule <k> #runRPCCall => #web3_sha3                               ... </k> <method> "web3_sha3"                               </method>

    rule <k> #runRPCCall => #eth_gasPrice                            ... </k> <method> "eth_gasPrice"                            </method>
    rule <k> #runRPCCall => #eth_blockNumber                         ... </k> <method> "eth_blockNumber"                         </method>
    rule <k> #runRPCCall => #eth_accounts                            ... </k> <method> "eth_accounts"                            </method>
    rule <k> #runRPCCall => #eth_getBalance                          ... </k> <method> "eth_getBalance"                          </method>
    rule <k> #runRPCCall => #eth_getStorageAt                        ... </k> <method> "eth_getStorageAt"                        </method>
    rule <k> #runRPCCall => #eth_getCode                             ... </k> <method> "eth_getCode"                             </method>
    rule <k> #runRPCCall => #eth_getTransactionCount                 ... </k> <method> "eth_getTransactionCount"                 </method>
    rule <k> #runRPCCall => #eth_sign                                ... </k> <method> "eth_sign"                                </method>
    rule <k> #runRPCCall => #eth_newBlockFilter                      ... </k> <method> "eth_newBlockFilter"                      </method>
    rule <k> #runRPCCall => #eth_uninstallFilter                     ... </k> <method> "eth_uninstallFilter"                     </method>
    rule <k> #runRPCCall => #eth_sendTransaction                     ... </k> <method> "eth_sendTransaction"                     </method>
    rule <k> #runRPCCall => #eth_sendRawTransaction                  ... </k> <method> "eth_sendRawTransaction"                  </method>
    rule <k> #runRPCCall => #eth_call                                ... </k> <method> "eth_call"                                </method>
    rule <k> #runRPCCall => #eth_estimateGas                         ... </k> <method> "eth_estimateGas"                         </method>
    rule <k> #runRPCCall => #eth_getTransactionReceipt               ... </k> <method> "eth_getTransactionReceipt"               </method>
    rule <k> #runRPCCall => #eth_getBlockByNumber                    ... </k> <method> "eth_getBlockByNumber"                    </method>
    rule <k> #runRPCCall => #eth_coinbase                            ... </k> <method> "eth_coinbase"                            </method>
    rule <k> #runRPCCall => #eth_getBlockByHash                      ... </k> <method> "eth_getBlockByHash"                      </method>
    rule <k> #runRPCCall => #eth_getBlockTransactionCountByHash      ... </k> <method> "eth_getBlockTransactionCountByHash"      </method>
    rule <k> #runRPCCall => #eth_getBlockTransactionCountByNumber    ... </k> <method> "eth_getBlockTransactionCountByNumber"    </method>
    rule <k> #runRPCCall => #eth_getCompilers                        ... </k> <method> "eth_getCompilers"                        </method>
    rule <k> #runRPCCall => #eth_getFilterChanges                    ... </k> <method> "eth_getFilterChanges"                    </method>
    rule <k> #runRPCCall => #eth_getFilterLogs                       ... </k> <method> "eth_getFilterLogs"                       </method>
    rule <k> #runRPCCall => #eth_getLogs                             ... </k> <method> "eth_getLogs"                             </method>
    rule <k> #runRPCCall => #eth_getTransactionByHash                ... </k> <method> "eth_getTransactionByHash"                </method>
    rule <k> #runRPCCall => #eth_getTransactionByBlockHashAndIndex   ... </k> <method> "eth_getTransactionByBlockHashAndIndex"   </method>
    rule <k> #runRPCCall => #eth_getTransactionByBlockNumberAndIndex ... </k> <method> "eth_getTransactionByBlockNumberAndIndex" </method>
    rule <k> #runRPCCall => #eth_hashrate                            ... </k> <method> "eth_hashrate"                            </method>
    rule <k> #runRPCCall => #eth_newFilter                           ... </k> <method> "eth_newFilter"                           </method>
    rule <k> #runRPCCall => #eth_protocolVersion                     ... </k> <method> "eth_protocolVersion"                     </method>
    rule <k> #runRPCCall => #eth_signTypedData                       ... </k> <method> "eth_signTypedData"                       </method>
    rule <k> #runRPCCall => #eth_subscribe                           ... </k> <method> "eth_subscribe"                           </method>
    rule <k> #runRPCCall => #eth_unsubscribe                         ... </k> <method> "eth_unsubscribe"                         </method>
    rule <k> #runRPCCall => #net_peerCount                           ... </k> <method> "net_peerCount"                           </method>
    rule <k> #runRPCCall => #net_listening                           ... </k> <method> "net_listening"                           </method>
    rule <k> #runRPCCall => #eth_syncing                             ... </k> <method> "eth_syncing"                             </method>
    rule <k> #runRPCCall => #bzz_hive                                ... </k> <method> "bzz_hive"                                </method>
    rule <k> #runRPCCall => #bzz_info                                ... </k> <method> "bzz_info"                                </method>

    rule <k> #runRPCCall => #evm_snapshot                            ... </k> <method> "evm_snapshot"                            </method>
    rule <k> #runRPCCall => #evm_revert                              ... </k> <method> "evm_revert"                              </method>
    rule <k> #runRPCCall => #evm_increaseTime                        ... </k> <method> "evm_increaseTime"                        </method>
    rule <k> #runRPCCall => #evm_mine                                ... </k> <method> "evm_mine"                                </method>

    rule <k> #runRPCCall => #firefly_shutdown                        ... </k> <method> "firefly_shutdown"                        </method>
    rule <k> #runRPCCall => #firefly_addAccount                      ... </k> <method> "firefly_addAccount"                      </method>
    rule <k> #runRPCCall => #firefly_getStateRoot                    ... </k> <method> "firefly_getStateRoot"                    </method>
    rule <k> #runRPCCall => #firefly_getTxRoot                       ... </k> <method> "firefly_getTxRoot"                       </method>
    rule <k> #runRPCCall => #firefly_getReceiptsRoot                 ... </k> <method> "firefly_getReceiptsRoot"                 </method>
    rule <k> #runRPCCall => #firefly_getTime                         ... </k> <method> "firefly_getTime"                         </method>
    rule <k> #runRPCCall => #firefly_setTime                         ... </k> <method> "firefly_setTime"                         </method>
    rule <k> #runRPCCall => #firefly_genesisBlock                    ... </k> <method> "firefly_genesisBlock"                    </method>
    rule <k> #runRPCCall => #firefly_setGasLimit                     ... </k> <method> "firefly_setGasLimit"                     </method>
    rule <k> #runRPCCall => #firefly_setGasPrice                     ... </k> <method> "firefly_setGasPrice"                     </method>
    rule <k> #runRPCCall => #firefly_setNetworkId                    ... </k> <method> "firefly_setNetworkId"                    </method>
    rule <k> #runRPCCall => #firefly_blake2compress                  ... </k> <method> "firefly_blake2compress"                  </method>

    rule <k> #runRPCCall => #miner_start                             ... </k> <method> "miner_start"                             </method>
    rule <k> #runRPCCall => #miner_stop                              ... </k> <method> "miner_stop"                              </method>
    rule <k> #runRPCCall => #personal_importRawKey                   ... </k> <method> "personal_importRawKey"                   </method>
    rule <k> #runRPCCall => #personal_sendTransaction                ... </k> <method> "personal_sendTransaction"                </method>
    rule <k> #runRPCCall => #personal_unlockAccount                  ... </k> <method> "personal_unlockAccount"                  </method>
    rule <k> #runRPCCall => #personal_newAccount                     ... </k> <method> "personal_newAccount"                     </method>
    rule <k> #runRPCCall => #personal_lockAccount                    ... </k> <method> "personal_lockAccount"                    </method>
    rule <k> #runRPCCall => #personal_listAccounts                   ... </k> <method> "personal_listAccounts"                   </method>

    rule <k> #runRPCCall => #rpcResponseError(-32601, "Method not found") ... </k> [owise]

    syntax KItem ::= "#firefly_shutdown"
 // ------------------------------------
    rule <k> #firefly_shutdown ~> _ => #putResponse({ "jsonrpc": "2.0" , "id": CALLID , "result": "Firefly client shutting down!" }, FD) </k>
         <web3shutdownable> true </web3shutdownable>
         <callid> CALLID </callid>
         <web3output> FD </web3output>
         <exit-code> _ => 0 </exit-code>

    rule <k> #firefly_shutdown => #rpcResponseError(-32800, "Firefly client not started with `--shutdownable`!") ... </k>
         <web3shutdownable> false </web3shutdownable>

    syntax KItem ::= "#net_version"
 // -------------------------------
    rule <k> #net_version => #rpcResponseSuccess(Int2String( CID )) ... </k>
         <chainID> CID </chainID>

    syntax KItem ::= "#web3_clientVersion"
 // --------------------------------------
    rule <k> #web3_clientVersion => #rpcResponseSuccess("Firefly RPC/v0.0.1/kevm") ... </k>

    syntax KItem ::= "#eth_gasPrice"
 // --------------------------------
    rule <k> #eth_gasPrice => #rpcResponseSuccess(#unparseQuantity( PRICE )) ... </k>
         <gasPrice> PRICE </gasPrice>

    syntax KItem ::= "#eth_blockNumber"
 // -----------------------------------
    rule <k> #eth_blockNumber => #rpcResponseSuccess(#unparseQuantity( BLOCKNUM -Int 1 )) ... </k>
         <number> BLOCKNUM </number>

    syntax KItem ::= "#eth_accounts"
 // --------------------------------
    rule <k> #eth_accounts => #rpcResponseSuccess([ #acctsToJArray( qsort(Set2List(keys(ACCTS))) ) ]) ... </k>
         <accountKeys> ACCTS </accountKeys>

    syntax List ::= qsort ( List ) [function]
 // -----------------------------------------
    rule qsort ( .List )           => .List
    rule qsort (ListItem(I:Int) L) => qsort(getIntElementsSmallerThan(I, L, .List)) ListItem(I) qsort(getIntElementsGreaterThan(I, L, .List))

    syntax List ::= getIntElementsSmallerThan ( Int, List, List ) [function]
                  | getIntElementsGreaterThan ( Int, List, List ) [function]
 // ------------------------------------------------------------------------
    rule getIntElementsSmallerThan (_, .List,               RESULTS) => RESULTS
    rule getIntElementsSmallerThan (X, (ListItem(I:Int) L), RESULTS) => getIntElementsSmallerThan (X, L, ListItem(I) RESULTS) requires I  <Int X
    rule getIntElementsSmallerThan (X, (ListItem(I:Int) L), RESULTS) => getIntElementsSmallerThan (X, L, RESULTS)             requires I >=Int X

    rule getIntElementsGreaterThan (_, .List ,              RESULTS) => RESULTS
    rule getIntElementsGreaterThan (X, (ListItem(I:Int) L), RESULTS) => getIntElementsGreaterThan (X, L, ListItem(I) RESULTS) requires I  >Int X
    rule getIntElementsGreaterThan (X, (ListItem(I:Int) L), RESULTS) => getIntElementsGreaterThan (X, L, RESULTS)             requires I <=Int X

    syntax JSONs ::= #acctsToJArray ( List ) [function]
 // ---------------------------------------------------
    rule #acctsToJArray( .List                       ) => .JSONs
    rule #acctsToJArray( ListItem( ACCT ) ACCTS:List ) => #unparseData( ACCT, 20 ), #acctsToJArray( ACCTS )

    syntax KItem ::= "#eth_getBalance"
 // ----------------------------------
    rule <k> #eth_getBalance ... </k>
         <params> [ (DATA => #parseHexWord(DATA)), _, .JSONs ] </params>

    rule <k> #eth_getBalance => #getAccountAtBlock(#parseBlockIdentifier(TAG), DATA) ~> #eth_getBalance ... </k>
         <params> [ DATA, TAG, .JSONs ] </params>

    rule <k> <account> ... <balance> ACCTBALANCE </balance> ... </account> ~> #eth_getBalance => #rpcResponseSuccess(#unparseQuantity( ACCTBALANCE )) ... </k>

    rule <k> .AccountItem ~> #eth_getBalance => #rpcResponseSuccess(#unparseQuantity( 0 )) ... </k>

    rule <k> #eth_getBalance => #rpcResponseError(-32000, "Incorrect number of arguments. Method 'eth_getBalance' requires exactly 2 arguments.") ... </k> [owise]

    syntax KItem ::= "#eth_getStorageAt"
 // ------------------------------------
    rule <k> #eth_getStorageAt ... </k>
         <params> [ (DATA => #parseHexWord(DATA)), (QUANTITY => #parseHexWord(QUANTITY)), _, .JSONs ] </params>

    rule <k> #eth_getStorageAt => #getAccountAtBlock(#parseBlockIdentifier(TAG), DATA) ~> #eth_getStorageAt ... </k>
         <params> [ DATA, QUANTITY, TAG, .JSONs ] </params>

    rule <k> <account> ... <storage> STORAGE </storage> ... </account> ~> #eth_getStorageAt => #rpcResponseSuccess(#unparseQuantity( #lookup(STORAGE, QUANTITY) )) ... </k>
         <params> [ DATA, QUANTITY, TAG, .JSONs ] </params>

    rule <k> .AccountItem ~> #eth_getStorageAt => #rpcResponseSuccess(#unparseQuantity( 0 )) ... </k>

    rule <k> #eth_getStorageAt => #rpcResponseError(-32000, "Incorrect number of arguments. Method 'eth_getStorageAt' requires exactly 3 arguments.") ... </k> [owise]

    syntax KItem ::= "#eth_getCode"
 // -------------------------------
    rule <k> #eth_getCode ... </k>
         <params> [ (DATA => #parseHexWord(DATA)), _, .JSONs ] </params>

    rule <k> #eth_getCode => #getAccountAtBlock(#parseBlockIdentifier(TAG), DATA) ~> #eth_getCode ... </k>
         <params> [ DATA, TAG, .JSONs ] </params>

     rule <k> <account> ... <code> CODE </code> ... </account> ~> #eth_getCode =>  #rpcResponseSuccess(#unparseDataByteArray( CODE )) ... </k>

     rule <k> .AccountItem ~> #eth_getCode => #rpcResponseSuccess(#unparseDataByteArray( .ByteArray )) ... </k>

    rule <k> #eth_getCode => #rpcResponseError(-32000, "Incorrect number of arguments. Method 'eth_getCode' requires exactly 2 arguments.") ... </k> [owise]

    syntax KItem ::= "#eth_getTransactionCount"
 // -------------------------------------------
    rule <k> #eth_getTransactionCount ... </k>
         <params> [ (DATA => #parseHexWord(DATA)), _, .JSONs ] </params>

    rule <k> #eth_getTransactionCount => #getAccountAtBlock(#parseBlockIdentifier(TAG), DATA) ~> #eth_getTransactionCount ... </k>
         <params> [ DATA, TAG, .JSONs ] </params>

    rule <k> <account> ... <nonce> NONCE </nonce> ... </account> ~> #eth_getTransactionCount => #rpcResponseSuccess(#unparseQuantity( NONCE )) ... </k>

    rule <k> .AccountItem ~> #eth_getTransactionCount => #rpcResponseSuccess(#unparseQuantity( 0 )) ... </k>

    rule <k> #eth_getTransactionCount => #rpcResponseError(-32000, "Incorrect number of arguments. Method 'eth_getTransactionCount' requires exactly 2 arguments.") ... </k> [owise]

    syntax KItem ::= "#eth_sign"
 // ----------------------------
    rule <k> #eth_sign => #signMessage(#unparseByteStack(#asByteStack(KEY)), #hashMessage(Hex2Raw(MESSAGE))) ... </k>
         <params> [ ACCTADDR, MESSAGE, .JSONs ] </params>
         <accountKeys>... #parseHexWord(ACCTADDR) |-> KEY ...</accountKeys>

    rule <k> #eth_sign => #rpcResponseError(3, "Execution error", [{ "code": 100, "message": "Account key doesn't exist, account locked!" }]) ... </k>
         <params> [ ACCTADDR, _ ] </params>
         <accountKeys> KEYMAP </accountKeys>
      requires notBool #parseHexWord(ACCTADDR) in_keys(KEYMAP)

    syntax KItem ::= #signMessage ( String , String )
 // -------------------------------------------------
    rule <k> #signMessage(KEY, MHASH) => #rpcResponseSuccess("0x" +String ECDSASign( MHASH, KEY )) ... </k>

    syntax String ::= #hashMessage ( String ) [function]
 // ----------------------------------------------------
    rule #hashMessage( S ) => #unparseByteStack(#parseHexBytes(Keccak256("\x19Ethereum Signed Message:\n" +String Int2String(lengthString(S)) +String S)))

    syntax SnapshotItem ::= "{" BlockListCell "|" NetworkCell "|" BlockCell "|" TxReceiptsCell "|" Int "|" MerkleTree "}"
 // ---------------------------------------------------------------------------------------------------------------------

    syntax KItem ::= "#evm_snapshot"
 // --------------------------------
    rule <k> #evm_snapshot => #pushNetworkState ~> #rpcResponseSuccess(#unparseQuantity( size ( SNAPSHOTS ) +Int 1 )) ... </k>
         <snapshots> SNAPSHOTS </snapshots>

    syntax KItem ::= "#pushNetworkState"
 // ------------------------------------
    rule <k> #pushNetworkState => . ... </k>
         <snapshots> ... (.List => ListItem({ <blockList> BLOCKLIST </blockList> | <network> NETWORK </network> | <block> BLOCK </block> | <txReceipts> RECEIPTS </txReceipts> | TIMEDIFF | TREE })) </snapshots>
         <network>    NETWORK   </network>
         <block>      BLOCK     </block>
         <blockList>  BLOCKLIST </blockList>
         <timeDiff>   TIMEDIFF  </timeDiff>
         <txReceipts> RECEIPTS  </txReceipts>
         <stateTrie>  TREE      </stateTrie>

    syntax KItem ::= "#popNetworkState"
 // -----------------------------------
    rule <k> #popNetworkState => . ... </k>
         <snapshots> ... ( ListItem({ <blockList> BLOCKLIST </blockList> | <network> NETWORK </network> | <block> BLOCK </block> | <txReceipts> RECEIPTS </txReceipts> | TIMEDIFF | TREE }) => .List ) </snapshots>
         <network>     _ => NETWORK                        </network>
         <blockhashes> _ => #getBlockhashlist( BLOCKLIST ) </blockhashes>
         <block>       _ => BLOCK                          </block>
         <blockList>   _ => BLOCKLIST                      </blockList>
         <timeDiff>    _ => TIMEDIFF                       </timeDiff>
         <txReceipts>  _ => RECEIPTS                       </txReceipts>
         <stateTrie>   _ => TREE                           </stateTrie>

    syntax List ::= #getBlockhashlist( List )            [function]
                  | #getBlockhashlistFromParents( List ) [function]
 // ---------------------------------------------------------------
    rule #getBlockhashlist( .List ) => .List
    rule #getBlockhashlist( (ListItem( BLOCK ) REST) #as BLOCKLIST ) => ListItem(#blockchainItemHash(BLOCK)) #getBlockhashlistFromParents(BLOCKLIST)
    rule #getBlockhashlistFromParents( .List ) => .List
    rule #getBlockhashlistFromParents( ListItem( { _ | <block> <previousHash> HP </previousHash> ... </block> } ) REST ) => ListItem(HP) #getBlockhashlistFromParents(REST)

    syntax KItem ::= "#evm_revert"
 // ------------------------------
    rule <k> #evm_revert => #popNetworkState ~> #rpcResponseSuccess(true) ... </k>
         <params>       [ DATA:Int, .JSONs ] </params>
         <snapshots>    SNAPSHOTS            </snapshots>
      requires DATA ==Int size(SNAPSHOTS)

    rule <k> #evm_revert ... </k>
         <params> [ (DATA => #parseHexWord(DATA)), .JSONs ] </params>

    rule <k> #evm_revert ... </k>
         <params>    ( [ DATA:Int, .JSONs ] )                    </params>
         <snapshots> ( SNAPSHOTS => range(SNAPSHOTS, 0, DATA ) ) </snapshots>
      requires size(SNAPSHOTS) >Int DATA

    rule <k> #evm_revert => #rpcResponseError(-32000, "Incorrect number of arguments. Method 'evm_revert' requires exactly 1 arguments. Request specified 0 arguments: [null].")  ... </k>
         <params> [ .JSONs ] </params>

    rule <k> #evm_revert => #rpcResponseSuccess(false) ... </k> [owise]

    syntax KItem ::= "#evm_increaseTime"
 // ------------------------------------
    rule <k> #evm_increaseTime ... </k>
         <params> [ (null => 0), .JSONs ] </params>

    rule <k> #evm_increaseTime => #rpcResponseSuccess(Int2String(TIMEDIFF +Int DATA)) ... </k>
         <params>   [ DATA:Int, .JSONs ]           </params>
         <timeDiff> TIMEDIFF => TIMEDIFF +Int DATA </timeDiff>

    syntax KItem ::= "#eth_newBlockFilter"
 // --------------------------------------
    rule <k> #eth_newBlockFilter => #rpcResponseSuccess(#unparseQuantity( FILTID )) ... </k>
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
         <params> [ (DATA => #parseHexWord(DATA)), .JSONs ] </params>

    rule <k> #eth_uninstallFilter => #rpcResponseSuccess(true) ... </k>
         <params> [ FILTID, .JSONs ] </params>
         <filters>
           ( <filter>
               <filterID> FILTID </filterID>
               ...
             </filter>
          => .Bag
           )
           ...
         </filters>

    rule <k> #eth_uninstallFilter => #rpcResponseSuccess(false) ... </k> [owise]
```

eth_sendTransaction
-------------------

**TODO**: Only call `#executeTx TXID` when mining is turned on, or when the mining interval comes around.

```k
    syntax KItem ::= "#eth_sendTransaction"
                   | "#eth_sendTransaction_final"
 // ---------------------------------------------
    rule <k> #eth_sendTransaction => #loadTx #parseHexWord( #getString("from",J) ) J ~> #eth_sendTransaction_final ... </k>
         <params> [ ({ _ } #as J), .JSONs ] </params>
      requires isString( #getJSON("from",J) )

    rule <k> #eth_sendTransaction => #rpcResponseError(-32000, "\"from\" field not found; is required") ... </k>
         <params> [ ({ _ } #as J), .JSONs ] </params>
      requires notBool isString( #getJSON("from",J) )

    rule <k> #eth_sendTransaction => #rpcResponseError(-32000, "Incorrect number of arguments. Method 'eth_sendTransaction' requires exactly 1 argument.") ... </k> [owise]

    rule <k> (TXID:Int => "0x" +String #hashSignedTx(TN, TP, TG, TT, TV, TD, TW, TR, TS)) ~> #eth_sendTransaction_final ... </k>
         <message>
           <msgID> TXID </msgID>
           <txNonce>    TN </txNonce>
           <txGasPrice> TP </txGasPrice>
           <txGasLimit> TG </txGasLimit>
           <to>         TT </to>
           <value>      TV </value>
           <sigV>       TW </sigV>
           <sigR>       TR </sigR>
           <sigS>       TS </sigS>
           <data>       TD </data>
         </message>

    rule <k> TXHASH:String ~> #eth_sendTransaction_final => #rpcResponseSuccess(TXHASH) ... </k>
         <statusCode> EVMC_SUCCESS </statusCode>

    rule <k> TXHASH:String ~> #eth_sendTransaction_final => #rpcResponseSuccessException(TXHASH, #generateException(TXHASH, PCOUNT, RD, EVMC_REVERT))
          ...
         </k>
         <statusCode> EVMC_REVERT </statusCode>
         <output> RD </output>
         <endPC> PCOUNT </endPC>

    rule <k> _:String ~> #eth_sendTransaction_final => #rpcResponseError(-32000, "base fee exceeds gas limit") ... </k>
         <statusCode> EVMC_OUT_OF_GAS </statusCode>

    rule <k> _:String ~> #eth_sendTransaction_final => #rpcResponseError(-32000, "sender doesn't have enough funds to send tx.") ... </k>
         <statusCode> EVMC_BALANCE_UNDERFLOW </statusCode>

    rule <k> _:String ~> #eth_sendTransaction_final => #rpcResponseError(-32000, "VM exception: " +String StatusCode2String( SC )) ... </k>
         <statusCode> SC:ExceptionalStatusCode </statusCode> [owise]

    rule <k> loadTransaction _ { "gas"      : (TG:String => #parseHexWord(TG)), _                    } ... </k>
    rule <k> loadTransaction _ { "gasPrice" : (TP:String => #parseHexWord(TP)), _                    } ... </k>
    rule <k> loadTransaction _ { "nonce"    : (TN:String => #parseHexWord(TN)), _                    } ... </k>
    rule <k> loadTransaction _ { "v"        : (TW:String => #parseHexWord(TW)), _                    } ... </k>
    rule <k> loadTransaction _ { "value"    : (TV:String => #parseHexWord(TV)), _                    } ... </k>
    rule <k> loadTransaction _ { "to"       : (TT:String => #parseHexWord(TT)), _                    } ... </k> requires TT =/=String ""
    rule <k> loadTransaction _ { "to"       : ""                              , REST => REST         } ... </k>
    rule <k> loadTransaction _ { "data"     : (TI:String => #parseByteStack(TI)), _                  } ... </k>
    rule <k> loadTransaction _ { "r"        : (TR:String => #padToWidth(32, #parseByteStack(TR))), _ } ... </k>
    rule <k> loadTransaction _ { "s"        : (TS:String => #padToWidth(32, #parseByteStack(TS))), _ } ... </k>
    rule <k> loadTransaction _ { ("from"    : _, REST => REST)                                       } ... </k>
    rule <k> loadTransaction _ { (("amount" : TV) => "value": TV)             , REST                 } ... </k>
    rule <k> loadTransaction _ { _          : _                               , REST => REST         } ... </k> [owise]

    syntax EthereumCommand ::= "makeTX" Int
 // ---------------------------------------
    rule <k> makeTX TXID => . ... </k>
         <txOrder>   ... (.List => ListItem(TXID)) </txOrder>
         <txPending> ... (.List => ListItem(TXID)) </txPending>
         <defaultGasPrice> GPRICE </defaultGasPrice>
         <defaultGasLimit> GLIMIT </defaultGasLimit>
         <messages>
            ( .Bag
           => <message>
                <msgID>      TXID:Int </msgID>
                <txGasPrice> GPRICE   </txGasPrice>
                <txGasLimit> GLIMIT   </txGasLimit>
                ...
              </message>
            )
          ...
          </messages>

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

    rule <k> #loadNonce _ _ => . ... </k> [owise]

    syntax JSON ::= #generateException( String, Int, Bytes, EndStatusCode ) [function]
 // ----------------------------------------------------------------------------------
    rule #generateException(TXHASH, PCOUNT, RD, SC) => { "message": "VM Exception while processing transaction: " +String StatusCode2TruffleString(SC) +String " " +String #parseReason(RD),
                                                      "code": -32000,
                                                      "data": {
                                                          TXHASH: {
                                                          "error": StatusCode2TruffleString(SC),
                                                          "program_counter": PCOUNT +Int 1,
                                                          "return": #unparseDataByteArray( RD ),
                                                          "reason": #parseReason(RD)
                                                        }
                                                      }
                                                    }
      requires lengthBytes(RD) >Int 68
    rule #generateException(TXHASH, PCOUNT, RD, SC) => { "message": "VM Exception while processing transaction: " +String StatusCode2TruffleString(SC),
                                                      "code": -32000,
                                                      "data": {
                                                          TXHASH: {
                                                          "error": StatusCode2TruffleString(SC),
                                                          "program_counter": PCOUNT +Int 1,
                                                          "return": #unparseDataByteArray( RD )
                                                        }
                                                      }
                                                    }
      requires notBool lengthBytes(RD) >Int 68

    syntax String ::= #parseReason ( Bytes ) [function]
 // ---------------------------------------------------
    rule #parseReason(RD) => Bytes2String(substrBytes(RD,
                              36 +Int #asInteger(substrBytes(RD,5,36)),
                              36 +Int #asInteger(substrBytes(RD,5,36)) +Int #asInteger(substrBytes(RD,37,68))))
```

-   signTX TXID ACCTFROM: Signs the transaction with TXID using ACCTFROM's private key

```k
    syntax KItem ::= "signTX" Int Int
                   | "signTX" Int String [klabel(signTXAux)]
 // --------------------------------------------------------
    rule <k> signTX TXID ACCTFROM:Int => signTX TXID ECDSASign( Hex2Raw( #hashUnsignedTx(TN, TP, TG, TT, TV, TD) ), #unparseByteStack( #padToWidth( 32, #asByteStack( KEY ) ) ) ) ... </k>
         <accountKeys> ... ACCTFROM |-> KEY ... </accountKeys>
         <mode> NORMAL </mode>
         <message>
           <msgID> TXID </msgID>
           <txNonce>    TN </txNonce>
           <txGasPrice> TP </txGasPrice>
           <txGasLimit> TG </txGasLimit>
           <to>         TT </to>
           <value>      TV </value>
           <data>       TD </data>
           ...
         </message>

    rule <k> signTX TXID ACCTFROM:Int => signTX TXID ECDSASign( Hex2Raw( #hashUnsignedTx(TN, TP, TG, TT, TV, TD) ), #unparseByteStack( ( #padToWidth( 20, #asByteStack( ACCTFROM ) ) ++ #padToWidth( 20, #asByteStack( ACCTFROM ) ) )[0 .. 32] ) ) ... </k>
         <mode> NOGAS </mode>
         <message>
           <msgID> TXID </msgID>
           <txNonce>    TN </txNonce>
           <txGasPrice> TP </txGasPrice>
           <txGasLimit> TG </txGasLimit>
           <to>         TT </to>
           <value>      TV </value>
           <data>       TD </data>
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
         <params> [ RAWTX:String, .JSONs ] => #rlpDecode( Hex2Raw( RAWTX ) ) </params>

    rule <k> #eth_sendRawTransaction => #rpcResponseError(-32000, "\"value\" argument must not be a number") ... </k>
         <params> [ _:Int, .JSONs ] </params>

    rule <k> #eth_sendRawTransaction => #rpcResponseError(-32000, "Invalid Signature") ... </k> [owise]

    rule <k> #eth_sendRawTransactionLoad
          => makeTX !ID:Int
          ~> loadTransaction !ID { "data"  : Raw2Hex(TI)  , "gas"      : Raw2Hex(TG) , "gasPrice" : Raw2Hex(TP)
                                 , "nonce" : Raw2Hex(TN)  , "r"        : Raw2Hex(TR) , "s"        : Raw2Hex(TS)
                                 , "to"    : Raw2Hex'(TT) , "v"        : Raw2Hex(TW) , "value"    : Raw2Hex(TV)
                                 , .JSONs
                                 }
          ~> #eth_sendRawTransactionVerify !ID
         ...
         </k>
         <params> [ TN, TP, TG, TT, TV, TI, TW, TR, TS, .JSONs ] </params>

    rule <k> #eth_sendRawTransactionLoad => #rpcResponseError(-32000, "Invalid Signature") ... </k> [owise]

    rule <k> #eth_sendRawTransactionVerify TXID
          => #prepareTx TXID #sender(TN, TP, TG, TT, TV, #unparseByteStack(TD), TW, TR, TS, CID)
          ~> #eth_sendRawTransactionSend TXID
         ...
         </k>
         <chainID> CID </chainID>
         <message>
           <msgID> TXID </msgID>
           <txNonce>    TN </txNonce>
           <txGasPrice> TP </txGasPrice>
           <txGasLimit> TG </txGasLimit>
           <to>         TT </to>
           <value>      TV </value>
           <data>       TD </data>
           <sigV>       TW </sigV>
           <sigR>       TR </sigR>
           <sigS>       TS </sigS>
         </message>
      requires #sender(TN, TP, TG, TT, TV, #unparseByteStack(TD), TW, TR, TS, CID) =/=K .Account

    rule <k> #eth_sendRawTransactionVerify TXID => #rpcResponseError(-32000, "Invalid Signature") ... </k>
         <txOrder> ListItem(TXID) => .List ... </txOrder>
         <txPending> ListItem(TXID) => .List ... </txPending>
         <messages> ( <message> <msgID> TXID </msgID> ... </message> => .Bag ) ... </messages> [owise]

    rule <k> #eth_sendRawTransactionSend TXID => #rpcResponseSuccess("0x" +String #hashSignedTx(TN, TP, TG, TT, TV, TD, TW, TR, TS)) ... </k>
         <message>
           <msgID> TXID </msgID>
           <txNonce>    TN </txNonce>
           <txGasPrice> TP </txGasPrice>
           <txGasLimit> TG </txGasLimit>
           <to>         TT </to>
           <value>      TV </value>
           <data>       TD </data>
           <sigV>       TW </sigV>
           <sigR>       TR </sigR>
           <sigS>       TS </sigS>
         </message>

    syntax String ::= "Raw2Hex'" "(" String ")" [function]
 // ------------------------------------------------------
    rule Raw2Hex' ("" ) => ""
    rule Raw2Hex' (TT ) => Raw2Hex(TT) requires TT =/=String ""
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
    rule <k> #eth_getBlockByNumber ... </k>
         <params> [ (null => "0x0"), _:Bool, .JSONs ] </params>

    rule <k> #eth_getBlockByNumber => #eth_getBlockByNumber_finalize( #getBlockByNumber(#parseBlockIdentifier(TAG), BLOCKLIST, {<network> NETWORK </network> | <block> BLOCK </block>})) ... </k>
         <params> [ TAG:String, TXOUT:Bool, .JSONs ] </params>
         <blockList> BLOCKLIST </blockList>
         <network>   NETWORK   </network>
         <block>     BLOCK     </block>

    rule <k> #eth_getBlockByNumber => #rpcResponseError(-32000, "Incorrect number of arguments. Method 'eth_getBlockByNumber' requires exactly 2 arguments.") ... </k>
         <params> [ VALUE, .JSONs ] </params>
      requires notBool isJSONs( VALUE )

    rule <k> #eth_getBlockByNumber => #rpcResponseError(-32000, "Incorrect number of arguments. Method 'eth_getBlockByNumber' requires exactly 2 arguments.") ... </k>
         <params> [ VALUE, VALUE2, _, .JSONs ] </params>
      requires notBool isJSONs( VALUE ) andBool notBool isJSONs( VALUE2 )

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
          => #rpcResponseSuccess( { "number": #unparseQuantity( NUM )
                                  , "hash": #unparseData( #blockchainItemHash( BLOCKITEM ), 32 )
                                  , "parentHash": #unparseData( PARENTHASH, 32 )
                                  , "mixHash": #unparseData( MIXHASH, 32 )
                                  , "nonce": #unparseData( NONCE, 8 )
                                  , "sha3Uncles": #unparseData( OMMERSHASH, 32 )
                                  , "logsBloom": #unparseDataByteArray( LOGSBLOOM )
                                  , "transactionsRoot": #unparseData( TXROOT, 32)
                                  , "stateRoot": #unparseData( STATEROOT, 32)
                                  , "receiptsRoot": #unparseData( RCPTROOT, 32)
                                  , "miner": #unparseData( MINER, 20 )
                                  , "difficulty": #unparseQuantity( DFFCLTY )
                                  , "totalDifficulty": #unparseQuantity( DFFCLTY )
                                  , "extraData": #unparseDataByteArray( DATA )
                                  , "size": "0x3e8"                                  // Ganache always returns 1000
                                  , "gasLimit": #unparseQuantity( GLIMIT )
                                  , "gasUsed": #unparseQuantity( GUSED )
                                  , "timestamp": #unparseQuantity( TIME )
                                  , "transactions": [ #getTransactionList( BLOCKITEM, <txReceipts> TXRECEIPTS </txReceipts>, FULLTX ) ]
                                  , "uncles": [ .JSONs ]
                                  }
                                )
          ...
         </k>
         <params> [ _, FULLTX:Bool, .JSONs ] </params>
         <txReceipts> TXRECEIPTS </txReceipts>

    rule <k> #eth_getBlockByNumber_finalize ( .BlockchainItem )=> #rpcResponseSuccess(null) ... </k>

    syntax JSONs ::= #getTransactionList ( BlockchainItem , TxReceiptsCell , Bool ) [function]
                   | #getTransactionHashList ( List, TxReceiptsCell , JSONs )       [function]
 // ------------------------------------------------------------------------------------------
    rule #getTransactionList ( { <network> <txOrder> TXIDLIST </txOrder> ... </network> | _ } , <txReceipts> TXRECEIPTS </txReceipts>, false )
      => #getTransactionHashList (TXIDLIST, <txReceipts> TXRECEIPTS </txReceipts>, .JSONs)

    rule #getTransactionHashList ( .List, _, RESULT ) => RESULT
    rule #getTransactionHashList ( ( ListItem(TXID) => .List ) TXIDLIST
                                 , <txReceipts>
                                     <txReceipt>
                                       <txID>   TXID   </txID>
                                       <txHash> TXHASH </txHash>
                                       ...
                                     </txReceipt>
                                     ...
                                   </txReceipts>
                                 , ( RESULT => TXHASH, RESULT ) )
```

Transaction Receipts
--------------------

-   The transaction receipt is a tuple of four items comprising:

    -   the cumulative gas used in the block containing the transaction receipt as of immediately after the transaction has happened,
    -   the set of logs created through execution of the transaction,
    -   the Bloom filter composed from information in those logs, and
    -   the status code of the transaction.

```k
    syntax KItem ::= "#makeTxReceipts"
                   | "#makeTxReceiptsAux" List
 // ------------------------------------------
    rule <k> #makeTxReceipts => #makeTxReceiptsAux TXLIST ... </k>
         <txOrder> TXLIST </txOrder>
    rule <k> #makeTxReceiptsAux .List => . ... </k>
    rule <k> #makeTxReceiptsAux (ListItem(TXID) TXLIST) => #makeTxReceipt TXID ~> #makeTxReceiptsAux TXLIST ... </k>

    syntax KItem ::= "#makeTxReceipt" Int
 // -------------------------------------
    rule <k> #makeTxReceipt TXID => . ... </k>
         <chainID> CID </chainID>
         <txReceipts>
           ( .Bag
          => <txReceipt>
               <txHash> "0x" +String #hashSignedTx(TN, TP, TG, TT, TV, TD, TW, TR, TS) </txHash>
               <txCumulativeGas> CGAS </txCumulativeGas>
               <logSet> LOGS </logSet>
               <bloomFilter> #bloomFilter(LOGS) </bloomFilter>
               <txStatus> bool2Word(STATUSCODE ==K EVMC_SUCCESS) </txStatus>
               <txID> TXID </txID>
               <sender> #parseHexWord(#unparseDataByteArray(#ecrecAddr(#sender(TN, TP, TG, TT, TV, #unparseByteStack(TD), TW , TR, TS, CID)))) </sender>
               <txBlockNumber> BN </txBlockNumber>
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
           <data>       TD   </data>
         </message>
         <statusCode> STATUSCODE </statusCode>
         <gasUsed> CGAS </gasUsed>
         <log> LOGS </log>
         <number> BN </number>

    syntax KItem ::= "#eth_getTransactionReceipt"
                   | "#eth_getTransactionReceipt_final" "(" BlockchainItem ")"
 // --------------------------------------------------------------------------
    rule <k> #eth_getTransactionReceipt => #eth_getTransactionReceipt_final(#getBlockByNumber (BN, BLOCKLIST, {<network> NETWORK </network> | <block> BLOCK </block>})) ... </k>
         <params> [TXHASH:String, .JSONs] </params>
         <txReceipt>
           <txHash>          TXHASH </txHash>
           <txBlockNumber>   BN     </txBlockNumber>
           ...
         </txReceipt>
         <blockList> BLOCKLIST </blockList>
         <network>   NETWORK </network>
         <block>     BLOCK   </block>

    rule <k> #eth_getTransactionReceipt_final ({
             <network>
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
               ...
             </network> | _ } #as BLOCKITEM )
          => #rpcResponseSuccess( { "transactionHash": TXHASH
                                  , "transactionIndex": #unparseQuantity(getIndexOf(TXID, TXLIST))
                                  , "blockHash": #unparseData( #blockchainItemHash( BLOCKITEM ), 32 )
                                  , "blockNumber": #unparseQuantity(BN)
                                  , "from": #unparseAccount(TXFROM)
                                  , "to": #unparseAccount(TT)
                                  , "gasUsed": #unparseQuantity(CGAS)
                                  , "cumulativeGasUsed": #unparseQuantity(CGAS)
                                  , "contractAddress": #if TT ==K .Account #then #unparseData(#newAddr(TXFROM, NONCE -Int 1), 20) #else null #fi
                                  , "logs": [#serializeLogs(LOGS, 0, getIndexOf(TXID, TXLIST), TXHASH, #unparseData( #blockchainItemHash( BLOCKITEM ), 32 ), BN)]
                                  , "status": #unparseQuantity(TXSTATUS)
                                  , "logsBloom": #unparseDataByteArray(BLOOM)
                                  , "v": #unparseQuantity(TW)
                                  , "r": #unparseQuantity( #asWord(TR) )
                                  , "s": #unparseQuantity( #asWord(TS) )
                                  }
                                )
         ...
         </k>
         <params> [TXHASH:String, .JSONs] </params>
         <txReceipt>
           <txHash>          TXHASH </txHash>
           <txID>            TXID </txID>
           <txCumulativeGas> CGAS </txCumulativeGas>
           <logSet>          LOGS </logSet>
           <bloomFilter>     BLOOM </bloomFilter>
           <txStatus>        TXSTATUS </txStatus>
           <sender>          TXFROM </sender>
           <txBlockNumber>   BN     </txBlockNumber>
         </txReceipt>

    rule <k> #eth_getTransactionReceipt => #rpcResponseSuccess(null) ... </k> [owise]

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
    rule #unparseAccount (ACCT:Int) => #unparseData(ACCT, 20)

    syntax JSONs ::= #unparseIntList ( List ) [function]
 // ----------------------------------------------------
    rule #unparseIntList (L) => #unparseIntListAux( L, .JSONs)

    syntax JSONs ::= #unparseIntListAux ( List, JSONs ) [function]
 // --------------------------------------------------------------
    rule #unparseIntListAux(.List, RESULT) => RESULT
    rule #unparseIntListAux(L ListItem(I), RESULT) => #unparseIntListAux(L, (#unparseDataByteArray(#padToWidth(32,#asByteStack(I))), RESULT))

    syntax JSONs ::= #serializeLogs ( List, Int, Int, String, String, Int ) [function]
 // ----------------------------------------------------------------------------------
    rule #serializeLogs (.List, _, _, _, _, _)  => .JSONs
    rule #serializeLogs (ListItem({ ACCT | TOPICS:List | DATA }) L, LI, TI, TH, BH, BN) => {
                                                                         "logIndex": #unparseQuantity(LI),
                                                                         "transactionIndex": #unparseQuantity(TI),
                                                                         "transactionHash": TH,
                                                                         "blockHash": BH,
                                                                         "blockNumber": #unparseQuantity(BN),
                                                                         "address": #unparseData(ACCT, 20),
                                                                         "data": #unparseDataByteArray(DATA),
                                                                         "topics": [#unparseIntList(TOPICS)],
                                                                         "type" : "mined"
                                                                                           }, #serializeLogs(L, LI +Int 1, TI, TH, BH, BN)

    syntax KItem ::= "#eth_getTransactionByHash"
 // -------------------------------------------
    rule <k> #eth_getTransactionByHash => #eth_getTransactionByHash_final(#getBlockByNumber (BN, BLOCKLIST, {<network> NETWORK </network> | <block> BLOCK </block>})) ... </k>
         <params> [ TXHASH:String, .JSONs ] </params>
         <txReceipt>
           <txHash> TXHASH </txHash>
           <txBlockNumber> BN </txBlockNumber>
           ...
         </txReceipt>
         <blockList> BLOCKLIST </blockList>
         <network>   NETWORK   </network>
         <block>     BLOCK     </block>

    rule <k> #eth_getTransactionByHash => #rpcResponseSuccess( null ) ... </k> [owise]

    syntax KItem ::= "#eth_getTransactionByHash_final" "(" BlockchainItem ")"
 // -------------------------------------------------------------------------
    rule <k> #eth_getTransactionByHash_final ({
             <network>
               <txOrder> TXLIST </txOrder>
               <message>
                 <msgID>      TXID     </msgID>
                 <txNonce>    TN       </txNonce>
                 <txGasPrice> TP       </txGasPrice>
                 <txGasLimit> TG       </txGasLimit>
                 <to>         TT:Account </to>
                 <value>      TV       </value>
                 <sigV>       TW       </sigV>
                 <sigR>       TR       </sigR>
                 <sigS>       TS       </sigS>
                 <data>       TD       </data>
               </message>
               ...
             </network> | _ } #as BLOCKITEM )
          => #rpcResponseSuccess( { "hash": TXHASH
                                  , "nonce": #unparseQuantity(TN)
                                  , "blockHash": #unparseData(#blockchainItemHash(BLOCKITEM),32)
                                  , "blockNumber": #unparseQuantity(BN)
                                  , "transactionIndex": #unparseQuantity(getIndexOf(TXID,TXLIST))
                                  , "from": #unparseData(TXFROM,20)
                                  , "to": #unparseAccount(TT)
                                  , "value": #unparseQuantity(TV)
                                  , "gas": #unparseQuantity(TG)
                                  , "gasPrice": #unparseQuantity(TP)
                                  , "input": #unparseDataByteArray(TD)
                                  , "v": #unparseQuantity(TW)
                                  , "r": #unparseQuantity(#asWord(TR))
                                  , "s": #unparseQuantity(#asWord(TS))
                                  }
                                )
          ...
         </k>
         <params> [ TXHASH:String, .JSONs ] </params>
         <txReceipt>
           <txHash> TXHASH </txHash>
           <txID> TXID </txID>
           <sender> TXFROM </sender>
           <txBlockNumber> BN </txBlockNumber>
           ...
         </txReceipt>
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
               "from":     #unparseDataByteArray(#ecrecAddr(#sender(TN, TP, TG, TT, TV, #unparseByteStack(DATA), TW , TR, TS, CID))),
               "to":       TT,
               "gas":      TG,
               "gasPrice": TP,
               "value":    TV,
               "data":     DATA
             }
         ...
         </k>
         <chainID> CID </chainID>
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

Transaction Execution
---------------------

- `#executeTx` takes a transaction, loads it into the current state and executes it.
**TODO**: treat the account creation case
**TODO**: record the logs after `finalizeTX`
**TODO**: execute all pending transactions

```k
    syntax KItem ::= "#loadTx" Account JSON
 // ---------------------------------------
    rule <k> #loadTx ACCTFROM J
          => makeTX !ID:Int
          ~> #loadNonce ACCTFROM !ID
          ~> loadTransaction !ID J
          ~> signTX !ID ACCTFROM
          ~> #prepareTx !ID ACCTFROM
          ~> !ID
          ...
         </k>

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

    rule <k> #validateTx TXID => #updateTimestamp ~> #executeTx TXID ~> #mineAndUpdate ... </k>
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
          ~> #finishTx
          ~> #finalizeTx(false)
         ...
         </k>
         <gasPrice> _ => GPRICE </gasPrice>
         <origin> ACCTFROM </origin>
         <callDepth> _ => -1 </callDepth>
         <txPending> ListItem(TXID:Int) ... </txPending>
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

    rule <k> #executeTx TXID:Int
          => #call ACCTFROM ACCTTO ACCTTO VALUE VALUE DATA false
          ~> #finishTx
          ~> #finalizeTx(false)
         ...
         </k>
         <origin> ACCTFROM </origin>
         <gasPrice> _ => GPRICE </gasPrice>
         <txPending> ListItem(TXID) ... </txPending>
         <callDepth> _ => -1 </callDepth>
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
      requires ACCTTO =/=K .Account

    syntax EthereumCommand ::= "#finishTx"
 // --------------------------------------
    rule <statusCode> _:ExceptionalStatusCode </statusCode> <k> #halt ~> #finishTx => #popCallStack ~> #popWorldState                   ... </k>
    rule <statusCode> EVMC_REVERT             </statusCode> <k> #halt ~> #finishTx => #popCallStack ~> #popWorldState ~> #refund GAVAIL ... </k> <gas> GAVAIL </gas>

    rule <statusCode> EVMC_SUCCESS </statusCode>
         <k> #halt ~> #finishTx => #mkCodeDeposit ACCT ... </k>
         <id> ACCT </id>
         <txPending> ListItem(TXID:Int) ... </txPending>
         <message>
           <msgID> TXID     </msgID>
           <to>    .Account </to>
           ...
         </message>

    rule <statusCode> EVMC_SUCCESS </statusCode>
         <k> #halt ~> #finishTx => #popCallStack ~> #dropWorldState ~> #refund GAVAIL ... </k>
         <id> ACCT </id>
         <gas> GAVAIL </gas>
         <txPending> ListItem(TXID:Int) ... </txPending>
         <message>
           <msgID> TXID </msgID>
           <to>    TT   </to>
           ...
         </message>
      requires TT =/=K .Account

    syntax KItem ::= "#mineAndUpdate"
 // ---------------------------------
    rule <statusCode> STATUSCODE </statusCode>
         <k> #mineAndUpdate => #mineBlock ... </k>
         <mode> EXECMODE </mode>
      requires EXECMODE =/=K NOGAS
       andBool ( STATUSCODE ==K EVMC_SUCCESS orBool STATUSCODE ==K EVMC_REVERT )

    rule <k> #mineAndUpdate => #clearGas ... </k> [owise]

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
    rule <k> #personal_importRawKey => #acctFromPrivateKey PRIKEY ~> #rpcResponseSuccess(#unparseData( #addrFromPrivateKey( PRIKEY ), 20 )) ... </k>
         <params> [ PRIKEY:String, PASSPHRASE:String, .JSONs ] </params>
      requires lengthString( PRIKEY ) ==Int 66

    rule <k> #personal_importRawKey => #rpcResponseError(-32000, "Private key length is invalid. Must be 32 bytes.") ... </k>
         <params> [ PRIKEY:String, _:String, .JSONs ] </params>
      requires lengthString( PRIKEY ) =/=Int 66

    rule <k> #personal_importRawKey => #rpcResponseError(-32000, "Method 'personal_importRawKey' requires exactly 2 parameters") ... </k> [owise]

    syntax KItem ::= "#acctFromPrivateKey" String
 // ---------------------------------------------
    rule <k> #acctFromPrivateKey KEY => #newAccount #addrFromPrivateKey(KEY) ... </k>
         <accountKeys> M => M[#addrFromPrivateKey(KEY) <- #parseHexWord(KEY)] </accountKeys>

    syntax KItem ::= "#firefly_addAccount" | "#firefly_addAccountByAddress" Int | "#firefly_addAccountByKey" String
 // ---------------------------------------------------------------------------------------------------------------
    rule <k> #firefly_addAccount => #firefly_addAccountByAddress #parseHexWord(#getString("address", J)) ... </k>
         <params> [ ({ _ } #as J), .JSONs ] </params>
      requires isString(#getJSON("address", J))

    rule <k> #firefly_addAccount => #firefly_addAccountByKey #getString("key", J) ... </k>
         <params> [ ({ _ } #as J), .JSONs ] </params>
      requires isString(#getJSON("key", J))

    rule <k> #firefly_addAccountByAddress ACCT_ADDR => #newAccount ACCT_ADDR ~> loadAccount ACCT_ADDR J ~> #rpcResponseSuccess(true) ... </k>
         <params> [ ({ _ } #as J), .JSONs ] </params>
         <activeAccounts> ACCTS </activeAccounts>
      requires notBool ACCT_ADDR in ACCTS

    rule <k> #firefly_addAccountByAddress ACCT_ADDR => #rpcResponseSuccess(false) ... </k>
         <params> [ ({ _ } #as J), .JSONs ] </params>
         <activeAccounts> ACCTS </activeAccounts>
      requires ACCT_ADDR in ACCTS

    rule <k> #firefly_addAccountByKey ACCT_KEY => #acctFromPrivateKey ACCT_KEY ~> loadAccount #addrFromPrivateKey(ACCT_KEY) J ~> #rpcResponseSuccess(true) ... </k>
         <params> [ ({ _ } #as J), .JSONs ] </params>
         <activeAccounts> ACCTS </activeAccounts>
      requires notBool #addrFromPrivateKey(ACCT_KEY) in ACCTS

    rule <k> #firefly_addAccountByKey ACCT_KEY => #rpcResponseSuccess(false) ... </k>
         <params> [ ({ _ } #as J), .JSONs ] </params>
          <activeAccounts> ACCTS </activeAccounts>
      requires #addrFromPrivateKey(ACCT_KEY) in ACCTS

    rule <k> #firefly_addAccount => #rpcResponseError(-32025, "Method 'firefly_addAccount' has invalid arguments") ... </k> [owise]

    rule <k> loadAccount _ { "balance" : ((VAL:String)         => #parseHexWord(VAL)),     _ } ... </k>
    rule <k> loadAccount _ { "nonce"   : ((VAL:String)         => #parseHexWord(VAL)),     _ } ... </k>
    rule <k> loadAccount _ { "code"    : ((CODE:String)        => #parseByteStack(CODE)),  _ } ... </k>
    rule <k> loadAccount _ { "storage" : ({ STORAGE:JSONs } => #parseMap({ STORAGE })), _ } ... </k>
    rule <k> loadAccount _ { "key" : _, REST => REST } ... </k>
    rule <k> loadAccount _ { "address" : _, REST => REST } ... </k>
```

- `#eth_call`

```k
    syntax KItem ::= "#eth_call"
 // ----------------------------
    rule <k> #eth_call ... </k>
         <params> [ { _ }, (.JSONs => "pending", .JSONs) ] </params>

    rule <k> #eth_call ... </k>
         <params> [ ({ ARGS => "from": #unparseData({keys_list(ACCTS)[0]}:>Int, 20), ARGS }), TAG, .JSONs ] </params>
         <accountKeys> ACCTS </accountKeys>
      requires notBool isString( #getJSON("from" , { ARGS }) )

    rule <k> #eth_call
          => #pushNetworkState
          ~> #setMode NOGAS
          ~> #loadTx #parseHexWord( #getString("from", J) ) J
          ~> #eth_call_finalize EXECMODE
         ...
         </k>
         <params> [ ({ _ } #as J), TAG, .JSONs ] </params>
         <mode> EXECMODE </mode>
      requires isString( #getJSON("from" , J) )

    rule <k> #eth_call => #rpcResponseError(-32027, "Method 'eth_call' has invalid arguments") ...  </k> [owise]

    syntax KItem ::= "#eth_call_finalize" Mode
 // ------------------------------------------
    rule <statusCode> EVMC_SUCCESS </statusCode>
         <k> _:Int ~> #eth_call_finalize EXECMODE
          => #setMode EXECMODE
          ~> #popNetworkState
          ~> #clearGas
          ~> #rpcResponseSuccess(#unparseDataByteArray( OUTPUT ))
         ...
         </k>
         <output> OUTPUT </output>

    rule <statusCode> SC:EndStatusCode </statusCode>
         <k> TXID:Int ~> #eth_call_finalize EXECMODE
          => #setMode EXECMODE
          ~> #popNetworkState
          ~> #clearGas
          ~> #rpcResponseError(#generateException("0x" +String #hashSignedTx(TN, TP, TG, TT, TV, TD, TW, TR, TS),
                               PCOUNT, RD, SC))
          ...
         </k>
         <endPC>   PCOUNT </endPC>
         <output>  RD     </output>
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
           <data>       TD   </data>
         </message>
      requires SC =/=K EVMC_SUCCESS
```

- `#eth_estimateGas`
**TODO**: add test for EVMC_OUT_OF_GAS
**TODO**: implement funcionality for block number argument

```k
    syntax KItem ::= "#eth_estimateGas"
 // -----------------------------------
    rule <k> #eth_estimateGas ... </k>
         <params> [ { _ }, (.JSONs => "pending", .JSONs) ] </params>

    rule <k> #eth_estimateGas ... </k>
         <params> [ ({ ARGS => "from": #unparseData({keys_list(ACCTS)[0]}:>Int, 20), ARGS }), TAG, .JSONs ] </params>
         <gasUsed>  GUSED  </gasUsed>
         <accountKeys> ACCTS </accountKeys>
      requires notBool isString( #getJSON("from" , { ARGS }) )

    rule <k> #eth_estimateGas
          => #pushNetworkState
          ~> #loadTx #parseHexWord( #getString("from", J) ) J
          ~> #eth_estimateGas_finalize GUSED
         ...
         </k>
         <params> [ ({ _ } #as J), TAG, .JSONs ] </params>
         <gasUsed>  GUSED  </gasUsed>
      requires isString(#getJSON("from", J) )

    rule <k> #eth_estimateGas => #rpcResponseError(-32028, "Method 'eth_estimateGas' has invalid arguments") ...  </k> [owise]

    syntax KItem ::= "#eth_estimateGas_finalize" Int
 // ------------------------------------------------
    rule <k> _:Int ~> #eth_estimateGas_finalize INITGUSED:Int => #popNetworkState ~> #rpcResponseSuccess(#unparseQuantity( #getGasUsed( #getBlockByNumber(LATEST, BLOCKLIST, {<network> NETWORK </network> | <block> BLOCK </block>}) ) -Int INITGUSED )) ... </k>
         <statusCode> STATUSCODE </statusCode>
         <blockList> BLOCKLIST </blockList>
         <network>   NETWORK   </network>
         <block>     BLOCK     </block>
      requires STATUSCODE =/=K EVMC_OUT_OF_GAS

    rule <k> _:Int ~> #eth_estimateGas_finalize _ => #popNetworkState ~> #rpcResponseError(-32000 , "base fee exceeds gas limit") ... </k>
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
    rule <k> #gas [ OP ] => . ... </k>
         <mode> NOGAS </mode>
     [priority(25)]

    rule <k> #memory [ OP ] => . ... </k>
         <mode> NOGAS </mode>
     [priority(25)]

    rule <k> #validateTx TXID => #updateTimestamp ~> #executeTx TXID ~> #mineAndUpdate ... </k>
         <mode> NOGAS </mode>
     [priority(25)]

    rule <k> #transferFunds _ _ _ => . ... </k>
         <mode> NOGAS </mode>
     [priority(25)]
```

Helper Funcs
------------

```k
    syntax Int ::= #blockchainItemHash( BlockchainItem ) [function]
 // ---------------------------------------------------------------
    rule #blockchainItemHash( { _ |
         <block>
           <previousHash>      HP </previousHash>
           <ommersHash>        HO </ommersHash>
           <coinbase>          HC </coinbase>
           <stateRoot>         HR </stateRoot>
           <transactionsRoot>  HT </transactionsRoot>
           <receiptsRoot>      HE </receiptsRoot>
           <logsBloom>         HB </logsBloom>
           <difficulty>        HD </difficulty>
           <number>            HI </number>
           <gasLimit>          HL </gasLimit>
           <gasUsed>           HG </gasUsed>
           <timestamp>         HS </timestamp>
           <extraData>         HX </extraData>
           <mixHash>           HM </mixHash>
           <blockNonce>        HN </blockNonce>
           ...
         </block> } )
      => #blockHeaderHash(HP, HO, HC, HR, HT, HE, HB, HD, HI, HL, HG, HS, HX, HM, HN)
```

State Root
----------

```k
    syntax MerkleTree ::= #stateRoot ( NetworkCell, Schedule ) [function]
 // ---------------------------------------------------------------------
    rule #stateRoot( <network>
                       <activeAccounts> ACCTS </activeAccounts>
                       <accounts> ACCTSCELL </accounts>
                       ...
                     </network>
                   , SCHED
                   )
      => #putAccountsInTrie( MerkleUpdateMap( .MerkleTree, #precompiledAccountsMap(#precompiledAccounts(SCHED)) ), Set2List(ACCTS), <accounts> ACCTSCELL </accounts> )

    syntax MerkleTree ::= #putAccountsInTrie( MerkleTree, List, AccountsCell ) [function]
 // -------------------------------------------------------------------------------------
    rule #putAccountsInTrie( TREE, .List, _ ) => TREE

    rule #putAccountsInTrie( (TREE => MerkleUpdate( TREE, Hex2Raw( #unparseData(ACCT,20) ), #rlpEncodeFullAccount(NONCE, BAL, STORAGE, CODE) ))
                           , (ListItem(ACCT) => .List) ACCTS
                           , <accounts>
                               <account>
                                 <acctID>  ACCT    </acctID>
                                 <nonce>   NONCE   </nonce>
                                 <balance> BAL     </balance>
                                 <storage> STORAGE </storage>
                                 <code>    CODE    </code>
                                 ...
                               </account>
                               ...
                             </accounts>
                           )

    rule #putAccountsInTrie( TREE => MerkleUpdate( TREE, Hex2Raw( #unparseData(ACCT,20) ), "" )
                           , (ListItem(ACCT) => .List) ACCTS
                           , _
                           )
      [owise]

    syntax KItem ::= "#firefly_getStateRoot"
 // ----------------------------------------
    rule <k> #firefly_getStateRoot => #rpcResponseSuccess({ "stateRoot" : "0x" +String Keccak256( #rlpEncodeMerkleTree( TREE ) ) }) ... </k>
         <stateTrie> TREE </stateTrie>
```

Transactions Root
-----------------

```k
    syntax MerkleTree ::= #transactionsRoot( NetworkCell )                            [function]
                        | #transactionsRootAux( MerkleTree, Int, List, MessagesCell ) [function]
 // --------------------------------------------------------------------------------------------
    rule #transactionsRoot( <network> <txOrder> TXLIST </txOrder> <messages> MESSAGES </messages> ... </network> )
      => #transactionsRootAux( .MerkleTree, 0, TXLIST, <messages> MESSAGES </messages> )

    rule #transactionsRootAux( ( TREE => MerkleUpdate( TREE, #rlpEncodeWord(I), #rlpEncodeTransaction(TN, TP, TG, TT, TV, TD, TW, TR, TS) ) )
                             , ( I => I +Int 1 )
                             , ( ListItem( TXID ) => .List ) TXLIST
                             , <messages>
                                 <message>
                                   <msgID> TXID </msgID>
                                   <txNonce>    TN </txNonce>
                                   <txGasPrice> TP </txGasPrice>
                                   <txGasLimit> TG </txGasLimit>
                                   <to>         TT </to>
                                   <value>      TV </value>
                                   <sigV>       TW </sigV>
                                   <sigR>       TR </sigR>
                                   <sigS>       TS </sigS>
                                   <data>       TD </data>
                                 </message>
                                 ...
                               </messages>
                             )

    rule #transactionsRootAux( TREE, _, .List, _ ) => TREE

    syntax KItem ::= "#firefly_getTxRoot"
 // -------------------------------------
    rule <k> #firefly_getTxRoot => #rpcResponseSuccess({ "transactionsRoot" : #getTxRoot( #getBlockByNumber(LATEST, BLOCKLIST, {<network> NETWORK </network> | <block> BLOCK </block>}) ) }) ... </k>
         <blockList> BLOCKLIST </blockList>
         <network>   NETWORK </network>
         <block>     BLOCK   </block>

    syntax String ::= #getTxRoot( BlockchainItem ) [function]
 // ---------------------------------------------------------
    rule #getTxRoot( { _ | <block> <transactionsRoot> TXROOT </transactionsRoot> ... </block> } ) => #unparseData( TXROOT, 32 )
```

Receipts Root
-------------

```k
    syntax MerkleTree ::= #receiptsRoot( List, TxReceiptsCell )                     [function]
                        | #receiptsRootAux( MerkleTree, Int, List, TxReceiptsCell ) [function]
 // ------------------------------------------------------------------------------------------

    rule #receiptsRoot( TXLIST, <txReceipts> TXRECEIPTS </txReceipts> )
      => #receiptsRootAux( .MerkleTree, 0, TXLIST, <txReceipts> TXRECEIPTS </txReceipts> )

    rule #receiptsRootAux( ( TREE => MerkleUpdate( TREE, #rlpEncodeWord(I), #rlpEncodeReceipt(TS, TG, TB, TL) ) )
                         , ( I => I +Int 1 )
                         , ( ListItem(TXID) => .List ) _
                         , <txReceipts>
                             <txReceipt>
                               <txID> TXID </txID>
                               <txStatus>        TS </txStatus>
                               <txCumulativeGas> TG </txCumulativeGas>
                               <bloomFilter>     TB </bloomFilter>
                               <logSet>          TL </logSet>
                               ...
                             </txReceipt>
                             ...
                           </txReceipts>
                         )

    rule #receiptsRootAux( TREE, _, .List, _ ) => TREE

    syntax KItem ::= "#firefly_getReceiptsRoot"
 // -------------------------------------------
    rule <k> #firefly_getReceiptsRoot => #rpcResponseSuccess({ "receiptsRoot" : #getReceiptRoot( #getBlockByNumber(LATEST, BLOCKLIST, {<network> NETWORK </network> | <block> BLOCK </block>}) ) }) ... </k>
         <blockList> BLOCKLIST </blockList>
         <network>   NETWORK   </network>
         <block>     BLOCK     </block>

    syntax String ::= #getReceiptRoot( BlockchainItem ) [function]
 // --------------------------------------------------------------
    rule #getReceiptRoot( { _ | <block> <receiptsRoot> RCPTROOT </receiptsRoot> ... </block> } ) => #unparseData( RCPTROOT, 32 )
```

Timestamp Calls
---------------

```k
    syntax KItem ::= "#firefly_getTime"
 // -----------------------------------
    rule <k> #firefly_getTime => #rpcResponseSuccess(#unparseQuantity( TIME )) ... </k>
         <timestamp> TIME </timestamp>

    syntax KItem ::= "#firefly_setTime"
 // -----------------------------------
    rule <k> #firefly_setTime => #rpcResponseSuccess(true) ... </k>
         <params> [ TIME:String, .JSONs ] </params>
         <timeDiff> _ => #parseHexWord( TIME ) -Int #time() </timeDiff>

    rule <k> #firefly_setTime => #rpcResponseSuccess(false) ... </k> [owise]
```

Gas Limit Call
--------------

```k
    syntax KItem ::= "#firefly_setGasLimit"
 // ---------------------------------------
    rule <k> #firefly_setGasLimit ... </k>
         <params> [ GLIMIT:String => #parseWord( GLIMIT ), .JSONs ] </params>

    rule <k> #firefly_setGasLimit => #rpcResponseSuccess(true) ... </k>
         <params>          [ GLIMIT:Int, .JSONs ] </params>
         <gasLimit>        _ => GLIMIT            </gasLimit>
         <defaultGasLimit> _ => GLIMIT            </defaultGasLimit>

    rule <k> #firefly_setGasLimit => #rpcResponseError(-32000, "firefly_setGasLimit requires exactly 1 argument") ... </k> [owise]
```

Gas Price Call
--------------

```k
    syntax KItem ::= "#firefly_setGasPrice"
 // ---------------------------------------
    rule <k> #firefly_setGasPrice ... </k>
         <params> [ GPRICE:String => #parseWord( GPRICE ), .JSONs ] </params>

    rule <k> #firefly_setGasPrice => #rpcResponseSuccess(true) ... </k>
         <params>          [ GPRICE:Int, .JSONs ] </params>
         <gasPrice>        _ => GPRICE            </gasPrice>
         <defaultGasPrice> _ => GPRICE            </defaultGasPrice>

    rule <k> #firefly_setGasPrice => #rpcResponseError(-32000, "firefly_setGasPrice requires exactly 1 argument") ... </k> [owise]
```

Network Id
----------

```k
    syntax KItem ::= "#firefly_setNetworkId"
 // ----------------------------------------
    rule <k> #firefly_setNetworkId ... </k>
         <params> [ VALUE:String => #parseWord( VALUE ), .JSONs ] </params>

    rule <k> #firefly_setNetworkId => #rpcResponseSuccess(true) ... </k>
         <params>          [ VALUE:Int, .JSONs ] </params>
         <chainID>        _ => VALUE            </chainID>

    rule <k> #firefly_setNetworkId => #rpcResponseError(-32000, "firefly_setNetworkId requires exactly 1 argument") ... </k> [owise]
```

Mining
------

```k
    syntax KItem ::= "#evm_mine"
 // ----------------------------
    rule <k> #evm_mine => #updateTimestamp ~> #mineBlock ~> #rpcResponseSuccess("0x0") ... </k> [owise]

    rule <k> #evm_mine => #mineBlock ~> #rpcResponseSuccess("0x0") ... </k>
         <params>    [ TIME:String, .JSONs ]              </params>
         <timestamp> _ => #parseWord( TIME )              </timestamp>
         <timeDiff>  _ => #parseWord( TIME ) -Int #time() </timeDiff>

    rule <k> #evm_mine => #rpcResponseError(-32000, "Incorrect number of arguments. Method 'evm_mine' requires between 0 and 1 arguments.") ... </k>
         <params> [ _ , _ , _:JSONs ] </params>

    syntax KItem ::= "#firefly_genesisBlock"
 // ----------------------------------------
    rule <k> #firefly_genesisBlock ... </k>
         <params> [ .JSONs => #unparseQuantity(#time()), .JSONs ] </params>

    rule <k> #firefly_genesisBlock => #initStateTrie ~> #updateTrieRoots ~> #pushBlockchainState ~> #incrementBlockNumber ~> #rpcResponseSuccess(true) ... </k>
         <params>     [ TIME:String, .JSONs ]                                                            </params>
         <timestamp>  _ => #parseWord( TIME )                                                            </timestamp>
         <logsBloom>  _ => #padToWidth( 256, .ByteArray )                                                </logsBloom>
         <ommersHash> _ => 13478047122767188135818125966132228187941283477090363246179690878162135454535 </ommersHash>
         <timeDiff>   _ => #parseWord( TIME ) -Int #time()                                               </timeDiff>

    syntax KItem ::= "#mineBlock"
 // -----------------------------
    rule <k> #mineBlock
          => #finalizeBlock
          ~> #setParentHash #getBlockByNumber( LATEST, BLOCKLIST, {<network> NETWORK </network> | <block> BLOCK </block>} )
          ~> #makeTxReceipts
          ~> #updateStateTrie
          ~> #updateTrieRoots
          ~> #saveState
          ~> #startBlock
          ~> #cleanTxLists
          ~> #clearGas
          ...
         </k>
         <blockList> BLOCKLIST </blockList>
         <network>   NETWORK   </network>
         <block>     BLOCK     </block>

    syntax KItem ::= "#saveState"
                   | "#incrementBlockNumber"
                   | "#cleanTxLists"
                   | "#clearGas"
                   | "#setParentHash" BlockchainItem
                   | "#updateTrieRoots"
                   | "#updateStateRoot"
                   | "#updateTransactionsRoot"
                   | "#updateReceiptsRoot"
                   | "#initStateTrie"
                   | "#updateStateTrie"
                   | #updateStateTrie ( JSONs )
 // -------------------------------------------
    rule <k> #saveState => #pushBlockchainState ~> #incrementBlockNumber ... </k>

    rule <k> #incrementBlockNumber => . ... </k>
         <number> BN => BN +Int 1 </number>

    rule <k> #cleanTxLists => . ... </k>
         <txPending> _ => .List </txPending>
         <txOrder>   _ => .List </txOrder>

    rule <k> #clearGas => . ... </k>
         <gas> _ => 0 </gas>

    rule <k> #setParentHash BCI => . ... </k>
         <previousHash> _ => #blockchainItemHash( BCI ) </previousHash>

    rule <k> #updateTrieRoots => #updateStateRoot ~> #updateTransactionsRoot ~> #updateReceiptsRoot ... </k>

    rule <k> #updateStateRoot => . ... </k>
         <stateRoot> _ => #parseHexWord( Keccak256( #rlpEncodeMerkleTree( TREE ) ) ) </stateRoot>
         <stateTrie> TREE </stateTrie>

    rule <k> #updateTransactionsRoot => . ... </k>
         <transactionsRoot> _ => #parseHexWord( Keccak256( #rlpEncodeMerkleTree( #transactionsRoot(<network> NETWORK </network>) ) ) ) </transactionsRoot>
         <network> NETWORK </network>

    rule <k> #updateReceiptsRoot => . ... </k>
         <receiptsRoot> _ => #parseHexWord( Keccak256( #rlpEncodeMerkleTree( #receiptsRoot( TXLIST, <txReceipts> TXRECEIPTS </txReceipts> ) ) ) ) </receiptsRoot>
         <txOrder> TXLIST </txOrder>
         <txReceipts> TXRECEIPTS </txReceipts>

    rule <k> #initStateTrie => . ... </k>
         <stateTrie> _ => #stateRoot( <network> NETWORK </network>, SCHED ) </stateTrie>
         <schedule> SCHED </schedule>
         <network> NETWORK </network>

    rule <k> #updateStateTrie => #updateStateTrie(OMMERS) ... </k>
         <ommerBlockHeaders> [ OMMERS ] </ommerBlockHeaders>

    rule <k> #updateStateTrie( [ _ , _ , OMMER , _ , _ , _ , _ , _ , _ , _ ] , REST ) => #updateStateTrie( REST ) ... </k>
         <touchedAccounts> ... .Set => SetItem(OMMER) ... </touchedAccounts>

    rule <k> #updateStateTrie( .JSONs ) => . ... </k>
         <schedule> SCHED </schedule>
         <stateTrie> TREE => #putAccountsInTrie( TREE, Set2List(SetItem(MINER) (ACCTS -Set #precompiledAccounts(SCHED))), <accounts> ACCTSCELL </accounts> ) </stateTrie>
         <touchedAccounts> ACCTS => .Set </touchedAccounts>
         <accounts> ACCTSCELL </accounts>
         <coinbase> MINER </coinbase>

    syntax KItem ::= "#updateTimestamp"
 // -----------------------------------
    rule <k> #updateTimestamp => . ... </k>
         <timestamp> _ => #time() +Int TIMEDIFF </timestamp>
         <timeDiff> TIMEDIFF </timeDiff>
```

Retrieving logs
---------------

 - `LogData` contains:
    - a List of log elements like `{ ACCT | TOPICS:List | DATA }`
    - Transaction Index (Int) inside the block in which it has been mined
    - Transaction Hash (String)
    - Block Number (Int)
    - Block Hash (String)

```k
    syntax LogData ::= "{" List "|" Int "|" String "|" Int "|" String "}"
 // ---------------------------------------------------------------------

    syntax KItem ::= "#eth_getLogs"
                   | #getLogs ( BlockIdentifier , BlockIdentifier , List )
                   | #serializeEthGetLogs ( List , JSONs )
 // ------------------------------------------------------
    rule <k> #eth_getLogs ... </k>
         <params> [ { PARAMS => "fromBlock": "latest", PARAMS } , .JSONs ] </params>
      requires #getJSON("fromBlock", { PARAMS }) ==K undef

    rule <k> #eth_getLogs ... </k>
         <params> [ { PARAMS => "toBlock": "latest", PARAMS } , .JSONs ] </params>
      requires #getJSON("toBlock", { PARAMS }) ==K undef

    rule <k> #eth_getLogs => #getLogs(#parseBlockIdentifier(#getJSON("fromBlock", { PARAMS })), #parseBlockIdentifier(#getJSON("toBlock", { PARAMS })), .List) ... </k>
         <params> [ { PARAMS } , .JSONs ] </params>
      requires #getJSON("fromBlock", { PARAMS }) =/=K undef
       andBool #getJSON("toBlock"  , { PARAMS }) =/=K undef

    rule <k> #getLogs(BLOCKID => #getNumberAtBlock(BLOCKID, BLOCKLIST,{<network> NETWORK </network> | <block> BLOCK </block>}), _, _) ... </k>
         <block>     BLOCK     </block>
         <network>   NETWORK   </network>
         <blockList> BLOCKLIST </blockList>
      requires BLOCKID ==K LATEST
        orBool BLOCKID ==K EARLIEST
        orBool BLOCKID ==K PENDING

    rule <k> #getLogs(_ , BLOCKID => #getNumberAtBlock(BLOCKID, BLOCKLIST,{<network> NETWORK </network> | <block> BLOCK </block>}), _) ... </k>
         <block>     BLOCK     </block>
         <network>   NETWORK   </network>
         <blockList> BLOCKLIST </blockList>
      requires BLOCKID ==K LATEST
        orBool BLOCKID ==K EARLIEST
        orBool BLOCKID ==K PENDING

    rule <k> #getLogs( START => START +Int 1
                     , END
                     , RESULT => RESULT ListItem( { LOGS
                                                  | #getTxPositionInBlock(TXID,#getBlockByNumber(START,BLOCKLIST,{<network> NETWORK </network>|<block> BLOCK </block>}))
                                                  | TXHASH
                                                  | START
                                                  | #unparseData( #blockchainItemHash( #getBlockByNumber(START,BLOCKLIST,{<network> NETWORK </network>|<block> BLOCK </block>}) ), 32 )
                                                  }
                                                )
                     )
          ...
         </k>
         <txReceipt>
           <txBlockNumber> START  </txBlockNumber>
           <txHash>        TXHASH </txHash>
           <txID>          TXID   </txID>
           <logSet>        LOGS   </logSet>
           ...
         </txReceipt>
         <block>     BLOCK     </block>
         <network>   NETWORK   </network>
         <blockList> BLOCKLIST </blockList>
      requires START <=Int END

    rule <k> #getLogs(START => START +Int 1, END, RESULT) ... </k>                           [owise]
    rule <k> #getLogs(START, END, RESULT) => #serializeEthGetLogs(RESULT, [.JSONs]) ... </k> requires START  >Int END

    rule <k> #serializeEthGetLogs(.List, RESULTS:JSONs) => #rpcResponseSuccess([flattenJSONs(RESULTS)]) ... </k>
    rule <k> #serializeEthGetLogs((ListItem({LOGS|TXID|TXHASH|BN|BH}:LogData) LIST:List), RESULTS) => #serializeEthGetLogs(LIST, [flattenJSONs(RESULTS, [#serializeLogs(LOGS,0,TXID,TXHASH,BH,BN)])]) ... </k>

    syntax Int ::= #getTxPositionInBlock( Int, BlockchainItem ) [function]
 // ----------------------------------------------------------------------
    rule #getTxPositionInBlock(TXID, {<network> <txOrder> TXLIST </txOrder> ...</network>|_}) => getIndexOf(TXID, TXLIST)
```

Blake2 Compression Function
---------------------------

```k
    syntax KItem ::= "#firefly_blake2compress"
 // ------------------------------------------
    rule <k> #firefly_blake2compress => #rpcResponseSuccess( Blake2Compress( Hex2Raw( DATA ) ) ) ... </k>
         <params> [ DATA:String, .JSONs ] </params>
```

Unimplemented Methods
---------------------

```k
    syntax KItem ::= "#eth_coinbase"
                   | "#eth_getBlockByHash"
                   | "#eth_getBlockTransactionCountByHash"
                   | "#eth_getBlockTransactionCountByNumber"
                   | "#eth_getCompilers"
                   | "#eth_getFilterChanges"
                   | "#eth_getFilterLogs"
                   | "#eth_getTransactionByBlockHashAndIndex"
                   | "#eth_getTransactionByBlockNumberAndIndex"
                   | "#eth_hashrate"
                   | "#eth_newFilter"
                   | "#eth_protocolVersion"
                   | "#eth_signTypedData"
                   | "#eth_subscribe"
                   | "#eth_unsubscribe"
                   | "#net_peerCount"
                   | "#net_listening"
                   | "#eth_syncing"
                   | "#bzz_hive"
                   | "#bzz_info"
                   | "#miner_start"
                   | "#miner_stop"
                   | "#personal_sendTransaction"
                   | "#personal_unlockAccount"
                   | "#personal_newAccount"
                   | "#personal_lockAccount"
                   | "#personal_listAccounts"
                   | "#web3_sha3"
                   | "#shh_version"
 // -------------------------------
    rule <k> #eth_coinbase                            => #rpcResponseUnimplemented ... </k>
    rule <k> #eth_getBlockByHash                      => #rpcResponseUnimplemented ... </k>
    rule <k> #eth_getBlockTransactionCountByHash      => #rpcResponseUnimplemented ... </k>
    rule <k> #eth_getBlockTransactionCountByNumber    => #rpcResponseUnimplemented ... </k>
    rule <k> #eth_getCompilers                        => #rpcResponseUnimplemented ... </k>
    rule <k> #eth_getFilterChanges                    => #rpcResponseUnimplemented ... </k>
    rule <k> #eth_getFilterLogs                       => #rpcResponseUnimplemented ... </k>
    rule <k> #eth_getTransactionByBlockHashAndIndex   => #rpcResponseUnimplemented ... </k>
    rule <k> #eth_getTransactionByBlockNumberAndIndex => #rpcResponseUnimplemented ... </k>
    rule <k> #eth_hashrate                            => #rpcResponseUnimplemented ... </k>
    rule <k> #eth_newFilter                           => #rpcResponseUnimplemented ... </k>
    rule <k> #eth_protocolVersion                     => #rpcResponseUnimplemented ... </k>
    rule <k> #eth_signTypedData                       => #rpcResponseUnimplemented ... </k>
    rule <k> #eth_subscribe                           => #rpcResponseUnimplemented ... </k>
    rule <k> #eth_unsubscribe                         => #rpcResponseUnimplemented ... </k>
    rule <k> #net_peerCount                           => #rpcResponseUnimplemented ... </k>
    rule <k> #net_listening                           => #rpcResponseUnimplemented ... </k>
    rule <k> #eth_syncing                             => #rpcResponseUnimplemented ... </k>
    rule <k> #bzz_hive                                => #rpcResponseUnimplemented ... </k>
    rule <k> #bzz_info                                => #rpcResponseUnimplemented ... </k>
    rule <k> #miner_start                             => #rpcResponseUnimplemented ... </k>
    rule <k> #miner_stop                              => #rpcResponseUnimplemented ... </k>
    rule <k> #personal_sendTransaction                => #rpcResponseUnimplemented ... </k>
    rule <k> #personal_unlockAccount                  => #rpcResponseUnimplemented ... </k>
    rule <k> #personal_newAccount                     => #rpcResponseUnimplemented ... </k>
    rule <k> #personal_lockAccount                    => #rpcResponseUnimplemented ... </k>
    rule <k> #personal_listAccounts                   => #rpcResponseUnimplemented ... </k>
    rule <k> #web3_sha3                               => #rpcResponseUnimplemented ... </k>
    rule <k> #shh_version                             => #rpcResponseUnimplemented ... </k>
```

Status Codes to Strings for Truffle
-----------------------------------

```k
    syntax String ::= StatusCode2TruffleString ( StatusCode ) [function]
 // --------------------------------------------------------------------
    rule StatusCode2TruffleString( EVMC_REVERT              ) => "revert"
    rule StatusCode2TruffleString( EVMC_INVALID_INSTRUCTION ) => "invalid opcode"
    rule StatusCode2TruffleString( SC                       ) => StatusCode2String(SC) [owise]
```

```k
endmodule
```
