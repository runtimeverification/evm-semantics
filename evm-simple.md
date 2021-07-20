```k
requires "evm-types.md"
requires "json-rpc.md"
requires "serialization.md"
requires "asm.md"
```

// FILE: evm.md

EVM Execution
=============

### Overview

The EVM is a stack machine over some simple opcodes.
Most of the opcodes are "local" to the execution state of the machine, but some of them must interact with the world state.
This file only defines the local execution operations, the file `driver.md` will define the interactions with the world state.

```k
//requires "data.md"
//requires "network.md"

module EVM
    imports STRING
    imports EVM-DATA
    imports NETWORK
```

Configuration
-------------

The configuration has cells for the current account id, the current opcode, the program counter, the current gas, the gas price, the current program, the word stack, and the local memory.
In addition, there are cells for the callstack and execution substate.

We've broken up the configuration into two components; those parts of the state that mutate during execution of a single transaction and those that are static throughout.
In the comments next to each cell, we've marked which component of the YellowPaper state corresponds to each cell.

```k
    configuration
      <kevm>
        <k> $PGM:EthereumSimulation </k>
        //<exit-code exit=""> 1 </exit-code>
        //<mode> $MODE:Mode </mode>
        //<schedule> $SCHEDULE:Schedule </schedule>

        <ethereum>

          // EVM Specific
          // ============

          <evm>

            // Mutable during a single transaction
            // -----------------------------------

            //<output>          .ByteArray  </output>           // H_RETURN
            //<statusCode>      .StatusCode </statusCode>
            //<endPC>           0           </endPC>
            //<callStack>       .List       </callStack>
            //<interimStates>   .List       </interimStates>
            //<touchedAccounts> .Set        </touchedAccounts>

            <callState> // KEEP 
              <program> .ByteArray </program> // KEEP
              <jumpDests> .Set </jumpDests> // KEEP

              // I_*
              //<id>        .Account   </id>                    // I_a
              //<caller>    .Account   </caller>                // I_s
              //<callData>  .ByteArray </callData>              // I_d
              //<callValue> 0          </callValue>             // I_v

              // \mu_*
              //<wordStack>   .WordStack </wordStack>           // \mu_s
              //<localMem>    .Memory    </localMem>            // \mu_m
              <pc>          0          </pc>                  // \mu_pc
              //<gas>         0          </gas>                 // \mu_g
              //<memoryUsed>  0          </memoryUsed>          // \mu_i
              //<callGas>     0          </callGas>

              //<static>    false </static>
              //<callDepth> 0     </callDepth>
            </callState>

            // A_* (execution substate)
            //<substate>
            //  <selfDestruct> .Set  </selfDestruct>            // A_s
            //  <log>          .List </log>                     // A_l
            //  <refund>       0     </refund>                  // A_r
            //</substate>

            // Immutable during a single transaction
            // -------------------------------------

            //<gasPrice> 0        </gasPrice>                   // I_p
            //<origin>   .Account </origin>                     // I_o

            // I_H* (block information)
            //<blockhashes> .List </blockhashes>
            //<block>
            //  <previousHash>     0          </previousHash>     // I_Hp
            //  <ommersHash>       0          </ommersHash>       // I_Ho
            //  <coinbase>         0          </coinbase>         // I_Hc
            //  <stateRoot>        0          </stateRoot>        // I_Hr
            //  <transactionsRoot> 0          </transactionsRoot> // I_Ht
            //  <receiptsRoot>     0          </receiptsRoot>     // I_He
            //  <logsBloom>        .ByteArray </logsBloom>        // I_Hb
            //  <difficulty>       0          </difficulty>       // I_Hd
            //  <number>           0          </number>           // I_Hi
            //  <gasLimit>         0          </gasLimit>         // I_Hl
            //  <gasUsed>          0          </gasUsed>          // I_Hg
            //  <timestamp>        0          </timestamp>        // I_Hs
            //  <extraData>        .ByteArray </extraData>        // I_Hx
            //  <mixHash>          0          </mixHash>          // I_Hm
            //  <blockNonce>       0          </blockNonce>       // I_Hn
            //
            //  <ommerBlockHeaders> [ .JSONs ] </ommerBlockHeaders>
            //</block>

          </evm>

          // Ethereum Network
          // ================

          <network>

            // Chain identifier
            // ----------------
            //<chainID> $CHAINID:Int </chainID>

            // Accounts Record
            // ---------------

            //<activeAccounts> .Set </activeAccounts>
            <accounts> // KEEP
              <account multiplicity="*" type="Map">
                //<acctID>      0                      </acctID>
                //<balance>     0                      </balance>
                //<code>        .ByteArray:AccountCode </code>
                <storage>     .Map                   </storage> // KEEP
                //<origStorage> .Map                   </origStorage>
                //<nonce>       0                      </nonce>
              </account>
            </accounts>

            // Transactions Record
            // -------------------

            //<txOrder>   .List </txOrder>
            //<txPending> .List </txPending>

            //<messages>
            //  <message multiplicity="*" type="Map">
            //    <msgID>      0          </msgID>
            //    <txNonce>    0          </txNonce>            // T_n
            //    <txGasPrice> 0          </txGasPrice>         // T_p
            //    <txGasLimit> 0          </txGasLimit>         // T_g
            //    <to>         .Account   </to>                 // T_t
            //    <value>      0          </value>              // T_v
            //    <sigV>       0          </sigV>               // T_w
            //    <sigR>       .ByteArray </sigR>               // T_r
            //    <sigS>       .ByteArray </sigS>               // T_s
            //    <data>       .ByteArray </data>               // T_i/T_e
            //  </message>
            //</messages>

          </network>

        </ethereum>
      </kevm>
```

```k
syntax EthereumSimulation

syntax AccountCode ::= ByteArray

syntax Mode ::= "NORMAL"  [klabel(NORMAL), symbol]
              | "VMTESTS" [klabel(VMTESTS), symbol]

syntax InternalOp ::= "#pushCallStack"
syntax InternalOp ::= "#popCallStack"
syntax InternalOp ::= "#dropCallStack"
//syntax Accounts ::= "{" AccountsCellFragment "|" Set "|" SubstateCellFragment "}"
syntax InternalOp ::= "#pushWorldState"
syntax InternalOp ::= "#popWorldState"
syntax InternalOp ::= "#dropWorldState"
syntax KItem ::= "#halt" | "#end" StatusCode
syntax KItem ::= "#execute"
syntax InternalOp ::= "#next" "[" OpCode "]"
syntax Bool ::= #stackUnderflow ( WordStack , OpCode ) [function]
                  | #stackUnderflow ( WordStack , Int    ) [function, functional]
                  | #stackOverflow  ( WordStack , OpCode ) [function]
syntax Int ::= #stackNeeded ( OpCode ) [function]
syntax Int ::= #stackAdded ( OpCode ) [function]
syntax Int ::= #stackDelta ( OpCode ) [function]
syntax Bool ::= #changesState ( OpCode , WordStack ) [function]
syntax InternalOp ::= "#exec" "[" OpCode "]"
syntax KItem  ::= OpCode
    syntax OpCode ::= NullStackOp | UnStackOp | BinStackOp | TernStackOp | QuadStackOp
                    | InvalidOp | StackOp | InternalOp | CallOp | CallSixOp | PushOp
syntax InternalOp ::= UnStackOp   Int
                        | BinStackOp  Int Int
                        | TernStackOp Int Int Int
                        | QuadStackOp Int Int Int Int
syntax InternalOp ::= StackOp WordStack
syntax InternalOp ::= CallSixOp Int Int     Int Int Int Int
                        | CallOp    Int Int Int Int Int Int Int
syntax InternalOp ::= "#addr" "[" OpCode "]"
syntax Bool ::= isAddr1Op ( OpCode ) [function, functional]
                  | isAddr2Op ( OpCode ) [function, functional]
syntax InternalOp ::= "#pc" "[" OpCode "]"
syntax Int ::= #widthOp ( OpCode ) [function]
syntax InternalOp ::= #finalizeStorage ( List )
syntax InternalOp ::= #finalizeTx ( Bool )
                        | #deleteAccounts ( List )
syntax EthereumCommand ::= "#startBlock"
syntax EthereumCommand ::= "#finalizeBlock" | #rewardOmmers ( JSONs )
syntax ByteArray ::= #bloomFilter(List)      [function]
                       | #bloomFilter(List, Int) [function, klabel(#bloomFilterAux)]
syntax List ::= listAsByteArrays(List) [function]
syntax Int ::= "M3:2048" "(" ByteArray ")" [function]
syntax Int ::= setBloomFilterBits(ByteArray) [function]
syntax Int ::= getBloomFilterBit(ByteArray, Int) [function]
syntax InternalOp ::= "#push" | "#setStack" WordStack
syntax InternalOp ::= "#newAccount" Int
                        | "#newExistingAccount" Int
                        | "#newFreshAccount" Int
syntax InternalOp ::= "#transferFunds" Int Int Int
syntax InvalidOp ::= "INVALID" | "UNDEFINED" "(" Int ")"
syntax UnStackOp ::= "POP"
syntax StackOp ::= DUP ( Int ) | SWAP ( Int )
syntax PushOp ::= PUSH ( Int )
syntax UnStackOp ::= "MLOAD"
syntax BinStackOp ::= "MSTORE" | "MSTORE8"
syntax UnStackOp ::= "ISZERO" | "NOT"
syntax BinStackOp ::= "ADD" | "MUL" | "SUB" | "DIV" | "EXP" | "MOD"
syntax BinStackOp ::= "SDIV" | "SMOD"
syntax TernStackOp ::= "ADDMOD" | "MULMOD"
syntax BinStackOp ::= "BYTE" | "SIGNEXTEND"
syntax BinStackOp ::= "SHL" | "SHR" | "SAR"
syntax BinStackOp ::= "AND" | "EVMOR" | "XOR"
syntax BinStackOp ::= "LT" | "GT" | "EQ"
syntax BinStackOp ::= "SLT" | "SGT"
syntax BinStackOp ::= "SHA3"
syntax NullStackOp ::= "PC" | "GAS" | "GASPRICE" | "GASLIMIT"
syntax NullStackOp ::= "COINBASE" | "TIMESTAMP" | "NUMBER" | "DIFFICULTY"
syntax NullStackOp ::= "ADDRESS" | "ORIGIN" | "CALLER" | "CALLVALUE" | "CHAINID" | "SELFBALANCE"
syntax NullStackOp ::= "MSIZE" | "CODESIZE"
syntax TernStackOp ::= "CODECOPY"
syntax UnStackOp ::= "BLOCKHASH"
syntax Int ::= #blockhash ( List , Int , Int , Int ) [function]
syntax NullStackOp ::= "JUMPDEST"
syntax UnStackOp ::= "JUMP"
syntax BinStackOp ::= "JUMPI"
syntax InternalOp ::= "#endBasicBlock"
syntax NullStackOp ::= "STOP"
syntax BinStackOp ::= "RETURN"
syntax BinStackOp ::= "REVERT"
syntax NullStackOp ::= "CALLDATASIZE"
syntax UnStackOp ::= "CALLDATALOAD"
syntax TernStackOp ::= "CALLDATACOPY"
syntax NullStackOp ::= "RETURNDATASIZE"
syntax TernStackOp ::= "RETURNDATACOPY"
syntax BinStackOp ::= LogOp
syntax LogOp ::= LOG ( Int )
syntax UnStackOp ::= "BALANCE"
syntax UnStackOp ::= "EXTCODESIZE"
syntax UnStackOp ::= "EXTCODEHASH"
syntax QuadStackOp ::= "EXTCODECOPY"
syntax UnStackOp ::= "SLOAD"
syntax BinStackOp ::= "SSTORE"
syntax InternalOp ::= "#checkCall" Int Int
                        | "#call"         Int Int Int Int Int ByteArray Bool
                        | "#callWithCode" Int Int Int ByteArray Int Int ByteArray Bool
                        | "#mkCall"       Int Int Int ByteArray     Int ByteArray Bool
syntax InternalOp ::= "#precompiled?" "(" Int "," Schedule ")"
syntax Bool ::= #isPrecompiledAccount ( Int , Schedule ) [function, functional, smtlib(isPrecompiledAccount)]
syntax KItem ::= "#initVM"
syntax KItem ::= "#loadProgram" ByteArray
syntax KItem ::= "#touchAccounts" Account | "#touchAccounts" Account Account

syntax Int ::= #widthOpCode(Int) [function]
syntax KItem ::= "#return" Int Int
syntax InternalOp ::= "#refund" Exp [strict]
                        | "#setLocalMem" Int Int ByteArray
syntax CallOp ::= "CALL"
syntax CallOp ::= "CALLCODE"
syntax CallSixOp ::= "DELEGATECALL"
syntax CallSixOp ::= "STATICCALL"
syntax InternalOp ::= "#create"   Int Int Int ByteArray
                        | "#mkCreate" Int Int Int ByteArray
                        | "#incrementNonce" Int
syntax KItem ::= "#codeDeposit" Int
                   | "#mkCodeDeposit" Int
                   | "#finishCodeDeposit" Int ByteArray
syntax TernStackOp ::= "CREATE"
syntax QuadStackOp ::= "CREATE2"
syntax UnStackOp ::= "SELFDESTRUCT"
syntax NullStackOp   ::= PrecompiledOp
syntax PrecompiledOp ::= #precompiled ( Int ) [function]
syntax Set ::= #precompiledAccounts ( Schedule ) [function, functional]
syntax PrecompiledOp ::= "ECREC"
syntax ByteArray ::= #ecrec ( Account ) [function]
syntax PrecompiledOp ::= "SHA256"
syntax PrecompiledOp ::= "RIP160"
syntax PrecompiledOp ::= "ID"
syntax PrecompiledOp ::= "MODEXP"
syntax ByteArray ::= #modexp1 ( Int , Int , Int , ByteArray ) [function]
                       | #modexp2 ( Int , Int , Int , ByteArray ) [function]
                       | #modexp3 ( Int , Int , Int , ByteArray ) [function]
                       | #modexp4 ( Int , Int , Int )             [function]
syntax PrecompiledOp ::= "ECADD"
syntax InternalOp ::= #ecadd(G1Point, G1Point)
syntax PrecompiledOp ::= "ECMUL"
syntax InternalOp ::= #ecmul(G1Point, Int)
syntax ByteArray ::= #point ( G1Point ) [function]
syntax PrecompiledOp ::= "ECPAIRING"
syntax InternalOp ::= #ecpairing(List, List, Int, ByteArray, Int)
syntax InternalOp ::= "#checkPoint"
syntax PrecompiledOp ::= "BLAKE2F"
syntax InternalOp ::= "#gas" "[" OpCode "," OpCode "]"
syntax InternalOp ::= "#gas"    "[" OpCode "]" | "#deductGas" | "#deductMemoryGas"
                        | "#memory" "[" OpCode "]" | "#deductMemory"
syntax Int ::= #memory ( OpCode , Int ) [function]
syntax Bool ::= #usesMemory ( OpCode ) [function]
syntax Int ::= #memoryUsageUpdate ( Int , Int , Int ) [function, functional]
syntax InternalOp ::= #gasExec ( Schedule , OpCode )
syntax InternalOp ::= "#allocateCallGas"
syntax InternalOp ::= "#allocateCreateGas"
syntax Exp     ::= Int
syntax KResult ::= Int
syntax Exp ::= Ccall         ( Schedule , BExp , Int , Int , Int ) [strict(2)]
              | Ccallgas      ( Schedule , BExp , Int , Int , Int ) [strict(2)]
              | Cselfdestruct ( Schedule , BExp , Int )             [strict(2)]
syntax Int ::= Cgascap ( Schedule , Int , Int , Int ) [function, functional, smtlib(gas_Cgascap)   ]
                 | Csstore ( Schedule , Int , Int , Int ) [function, functional, smtlib(gas_Csstore)   ]
                 | Rsstore ( Schedule , Int , Int , Int ) [function, functional, smtlib(gas_Rsstore)   ]
                 | Cextra  ( Schedule , Bool , Int )      [function, functional, smtlib(gas_Cextra)    ]
                 | Cnew    ( Schedule , Bool , Int )      [function, functional, smtlib(gas_Cnew)      ]
                 | Cxfer   ( Schedule , Int )             [function, functional, smtlib(gas_Cxfer)     ]
                 | Cmem    ( Schedule , Int )             [function, functional, smtlib(gas_Cmem), memo]
syntax BExp    ::= Bool
    syntax KResult ::= Bool
    syntax BExp ::= #accountNonexistent ( Int )
syntax Bool ::= #accountEmpty ( AccountCode , Int , Int ) [function, klabel(accountEmpty), symbol]
syntax Int ::= #allBut64th ( Int ) [function, functional, smtlib(gas_allBut64th)]
syntax Int ::= G0 ( Schedule , ByteArray , Bool ) [function]
syntax Int ::= "G*" "(" Int "," Int "," Int ")" [function]
syntax Int ::= #multComplexity(Int) [function]
syntax Int ::= #adjustedExpLength(Int, Int, ByteArray) [function]
                 | #adjustedExpLength(Int)                 [function, klabel(#adjustedExpLengthAux)]
syntax Bool ::= ScheduleFlag "<<" Schedule ">>" [function, functional]
syntax ScheduleFlag ::= "Gselfdestructnewaccount" | "Gstaticcalldepth" | "Gemptyisnonexistent" | "Gzerovaluenewaccountgas"
                          | "Ghasrevert"              | "Ghasreturndata"   | "Ghasstaticcall"      | "Ghasshift"
                          | "Ghasdirtysstore"         | "Ghascreate2"      | "Ghasextcodehash"     | "Ghasselfbalance"
                          | "Ghassstorestipend"       | "Ghaschainid"
syntax Int ::= ScheduleConst "<" Schedule ">" [function, functional]
syntax ScheduleConst ::= "Gzero"        | "Gbase"          | "Gverylow"      | "Glow"          | "Gmid"        | "Ghigh"
                           | "Gextcodesize" | "Gextcodecopy"   | "Gbalance"      | "Gsload"        | "Gjumpdest"   | "Gsstoreset"
                           | "Gsstorereset" | "Rsstoreclear"   | "Rselfdestruct" | "Gselfdestruct" | "Gcreate"     | "Gcodedeposit"  | "Gcall"
                           | "Gcallvalue"   | "Gcallstipend"   | "Gnewaccount"   | "Gexp"          | "Gexpbyte"    | "Gmemory"       | "Gtxcreate"
                           | "Gtxdatazero"  | "Gtxdatanonzero" | "Gtransaction"  | "Glog"          | "Glogdata"    | "Glogtopic"     | "Gsha3"
                           | "Gsha3word"    | "Gcopy"          | "Gblockhash"    | "Gquadcoeff"    | "maxCodeSize" | "Rb"            | "Gquaddivisor"
                           | "Gecadd"       | "Gecmul"         | "Gecpairconst"  | "Gecpaircoeff"  | "Gfround"
syntax Schedule ::= "DEFAULT" [klabel(DEFAULT_EVM), symbol, smtlib(schedule_DEFAULT)]
syntax Schedule ::= "FRONTIER" [klabel(FRONTIER_EVM), symbol, smtlib(schedule_FRONTIER)]
syntax Schedule ::= "HOMESTEAD" [klabel(HOMESTEAD_EVM), symbol, smtlib(schedule_HOMESTEAD)]
syntax Schedule ::= "TANGERINE_WHISTLE" [klabel(TANGERINE_WHISTLE_EVM), symbol, smtlib(schedule_TANGERINE_WHISTLE)]
syntax Schedule ::= "SPURIOUS_DRAGON" [klabel(SPURIOUS_DRAGON_EVM), symbol, smtlib(schedule_SPURIOUS_DRAGON)]
syntax Schedule ::= "BYZANTIUM" [klabel(BYZANTIUM_EVM), symbol, smtlib(schedule_BYZANTIUM)]
syntax Schedule ::= "CONSTANTINOPLE" [klabel(CONSTANTINOPLE_EVM), symbol, smtlib(schedule_CONSTANTINOPLE)]
syntax Schedule ::= "PETERSBURG" [klabel(PETERSBURG_EVM), symbol, smtlib(schedule_PETERSBURG)]
syntax Schedule ::= "ISTANBUL" [klabel(ISTANBUL_EVM), symbol, smtlib(schedule_ISTANBUL)]
syntax OpCode ::= #dasmOpCode ( Int , Schedule ) [function, memo]

// kept simplifications for these:

// [#] #computeValidJumpDests
  syntax Set ::= #computeValidJumpDests( ByteArray )            [function, memo]
               | #computeValidJumpDests( ByteArray , Int , List ) [function, klabel(#computeValidJumpDestsAux)]
// ---------------------------------------------------------------------------------------------------------
  rule #computeValidJumpDests(PGM) => #computeValidJumpDests(PGM, 0, .List)

  syntax Set ::= #computeValidJumpDestsWithinBound(ByteArray, Int, List) [function]
// ---------------------------------------------------------------------------------
  rule #computeValidJumpDests(PGM, I, RESULT) => List2Set(RESULT) requires I >=Int #sizeByteArray(PGM)
  rule #computeValidJumpDests(PGM, I, RESULT) => #computeValidJumpDestsWithinBound(PGM, I, RESULT) requires I <Int #sizeByteArray(PGM)

  rule #computeValidJumpDestsWithinBound(PGM, I, RESULT) => #computeValidJumpDests(PGM, I +Int 1, RESULT ListItem(I)) requires PGM [ I ] ==Int 91
  rule #computeValidJumpDestsWithinBound(PGM, I, RESULT) => #computeValidJumpDests(PGM, I +Int #widthOpCode(PGM [ I ]), RESULT) requires notBool PGM [ I ] ==Int 91


// [#] #widthOpCode
  syntax Int ::= #widthOpCode(Int) [function]
 // -------------------------------------------
    rule #widthOpCode(W) => W -Int 94 requires W >=Int 96 andBool W <=Int 127
    rule #widthOpCode(_) => 1 [owise]

```

```k
endmodule
```

FILE: data.md

EVM Words
=========

```k
//requires "evm-types.md"
//requires "json-rpc.md"
//requires "serialization.md"
```

```k
module EVM-DATA
    imports EVM-TYPES
    imports SERIALIZATION
    imports STRING-BUFFER
    imports MAP-SYMBOLIC
    imports COLLECTIONS
    imports JSON-EXT
```

```k
endmodule
```

FILE: driver.md

Ethereum Simulations
====================

Ethereum is using the EVM to drive updates over the world state.
Actual execution of the EVM is defined in [the EVM file](../evm).

```k
//requires "evm.md"
//requires "optimizations.md"
//requires "asm.md"
//requires "state-loader.md"

module ETHEREUM-SIMULATION
    imports EVM
    imports EVM-OPTIMIZATIONS
    imports EVM-ASSEMBLY
    imports STATE-LOADER
```

An Ethereum simulation is a list of Ethereum commands.
Some Ethereum commands take an Ethereum specification (eg. for an account or transaction).

```k
    syntax EthereumSimulation ::= ".EthereumSimulation"
                                | EthereumCommand EthereumSimulation
 // ----------------------------------------------------------------
    rule <k> .EthereumSimulation                        => .          ... </k>
    rule <k> ETC                 .EthereumSimulation    => ETC        ... </k>
    rule <k> ETC                 ETS:EthereumSimulation => ETC ~> ETS ... </k> requires ETS =/=K .EthereumSimulation

    rule <k> #halt ~> ETC ETS:EthereumSimulation => #halt ~> ETC ~> ETS ... </k>

    syntax EthereumSimulation ::= JSON
 // ----------------------------------
    rule <k> JSONINPUT:JSON => run JSONINPUT success .EthereumSimulation </k>
```

For verification purposes, it's much easier to specify a program in terms of its op-codes and not the hex-encoding that the tests use.
To do so, we'll extend sort `JSON` with some EVM specific syntax, and provide a "pretti-fication" to the nicer input form.

```k
    syntax JSON ::= ByteArray | OpCodes | Map | SubstateLogEntry | Account
 // ----------------------------------------------------------------------
```

### Driving Execution

-   `start` places `#next` on the `<k>` cell so that execution of the loaded state begin.
-   `flush` places `#finalize` on the `<k>` cell.

```k
    syntax EthereumCommand ::= "start"
 // ----------------------------------
    //rule <mode> NORMAL  </mode> <k> start => #execute ... </k>
    //rule <mode> VMTESTS </mode> <k> start => #execute ... </k>

    syntax EthereumCommand ::= "flush"
 // ----------------------------------
    //rule <mode> EXECMODE </mode> <statusCode> EVMC_SUCCESS            </statusCode> <k> #halt ~> flush => #finalizeTx(EXECMODE ==K VMTESTS)          ... </k>
    //rule <mode> EXECMODE </mode> <statusCode> _:ExceptionalStatusCode </statusCode> <k> #halt ~> flush => #finalizeTx(EXECMODE ==K VMTESTS) ~> #halt ... </k>
```

-   `startTx` computes the sender of the transaction, and places loadTx on the `k` cell.
-   `loadTx(_)` loads the next transaction to be executed into the current state.
-   `finishTx` is a place-holder for performing necessary cleanup after a transaction.

**TODO**: `loadTx(_) => loadTx_`

```k
    syntax EthereumCommand ::= "startTx"
 // ------------------------------------
    //rule <k> startTx => #finalizeBlock ... </k>
    //     <txPending> .List </txPending>

    //rule <k> startTx => loadTx(#sender(TN, TP, TG, TT, TV, #unparseByteStack(DATA), TW, TR, TS, CID)) ... </k>
    //     <chainID> CID </chainID>
    //     <txPending> ListItem(TXID:Int) ... </txPending>
    //     <message>
    //       <msgID>      TXID </msgID>
    //       <txNonce>    TN   </txNonce>
    //       <txGasPrice> TP   </txGasPrice>
    //       <txGasLimit> TG   </txGasLimit>
    //       <to>         TT   </to>
    //       <value>      TV   </value>
    //       <sigV>       TW   </sigV>
    //       <sigR>       TR   </sigR>
    //       <sigS>       TS   </sigS>
    //       <data>       DATA </data>
    //     </message>

    syntax EthereumCommand ::= loadTx ( Account )
 // ---------------------------------------------
    //rule <k> loadTx(ACCTFROM)
    //      => #create ACCTFROM #newAddr(ACCTFROM, NONCE) VALUE CODE
    //      ~> #finishTx ~> #finalizeTx(false) ~> startTx
    //     ...
    //     </k>
    //     <schedule> SCHED </schedule>
    //     <gasPrice> _ => GPRICE </gasPrice>
    //     <callGas> _ => GLIMIT -Int G0(SCHED, CODE, true) </callGas>
    //     <origin> _ => ACCTFROM </origin>
    //     <callDepth> _ => -1 </callDepth>
    //     <txPending> ListItem(TXID:Int) ... </txPending>
    //     <coinbase> MINER </coinbase>
    //     <message>
    //       <msgID>      TXID     </msgID>
    //       <txGasPrice> GPRICE   </txGasPrice>
    //       <txGasLimit> GLIMIT   </txGasLimit>
    //       <to>         .Account </to>
    //       <value>      VALUE    </value>
    //       <data>       CODE     </data>
    //       ...
    //     </message>
    //     <account>
    //       <acctID> ACCTFROM </acctID>
    //       <balance> BAL => BAL -Int (GLIMIT *Int GPRICE) </balance>
    //       <nonce> NONCE </nonce>
    //       ...
    //     </account>
    //     <touchedAccounts> _ => SetItem(MINER) </touchedAccounts>

    //rule <k> loadTx(ACCTFROM)
    //      => #call ACCTFROM ACCTTO ACCTTO VALUE VALUE DATA false
    //      ~> #finishTx ~> #finalizeTx(false) ~> startTx
    //     ...
    //     </k>
    //     <schedule> SCHED </schedule>
    //     <gasPrice> _ => GPRICE </gasPrice>
    //     <callGas> _ => GLIMIT -Int G0(SCHED, DATA, false) </callGas>
    //     <origin> _ => ACCTFROM </origin>
    //     <callDepth> _ => -1 </callDepth>
    //     <txPending> ListItem(TXID:Int) ... </txPending>
    //     <coinbase> MINER </coinbase>
    //     <message>
    //       <msgID>      TXID   </msgID>
    //       <txGasPrice> GPRICE </txGasPrice>
    //       <txGasLimit> GLIMIT </txGasLimit>
    //       <to>         ACCTTO </to>
    //       <value>      VALUE  </value>
    //       <data>       DATA   </data>
    //       ...
    //     </message>
    //     <account>
    //       <acctID> ACCTFROM </acctID>
    //       <balance> BAL => BAL -Int (GLIMIT *Int GPRICE) </balance>
    //       <nonce> NONCE => NONCE +Int 1 </nonce>
    //       ...
    //     </account>
    //     <touchedAccounts> _ => SetItem(MINER) </touchedAccounts>
    //  requires ACCTTO =/=K .Account

    syntax EthereumCommand ::= "#finishTx"
 // --------------------------------------
    //rule <statusCode> _:ExceptionalStatusCode </statusCode> <k> #halt ~> #finishTx => #popCallStack ~> #popWorldState                   ... </k>
    //rule <statusCode> EVMC_REVERT             </statusCode> <k> #halt ~> #finishTx => #popCallStack ~> #popWorldState ~> #refund GAVAIL ... </k> <gas> GAVAIL </gas>

    //rule <statusCode> EVMC_SUCCESS </statusCode>
    //     <k> #halt ~> #finishTx => #mkCodeDeposit ACCT ... </k>
    //     <id> ACCT </id>
    //     <txPending> ListItem(TXID:Int) ... </txPending>
    //     <message>
    //       <msgID> TXID     </msgID>
    //       <to>    .Account </to>
    //       ...
    //     </message>

    //rule <statusCode> EVMC_SUCCESS </statusCode>
    //     <k> #halt ~> #finishTx => #popCallStack ~> #dropWorldState ~> #refund GAVAIL ... </k>
    //     <gas> GAVAIL </gas>
    //     <txPending> ListItem(TXID:Int) ... </txPending>
    //     <message>
    //       <msgID> TXID </msgID>
    //       <to>    TT   </to>
    //       ...
    //     </message>
    //  requires TT =/=K .Account
```

-   `exception` only clears from the `<k>` cell if there is an exception preceding it.
-   `failure_` holds the name of a test that failed if a test does fail.
-   `success` sets the `<exit-code>` to `0` and the `<mode>` to `SUCCESS`.

```k
    syntax Mode ::= "SUCCESS"
 // -------------------------

    syntax EthereumCommand ::= "exception" | "status" StatusCode
 // ------------------------------------------------------------
    //rule <statusCode> _:ExceptionalStatusCode </statusCode>
    //     <k> #halt ~> exception => . ... </k>

    //rule <k> status SC => . ... </k> <statusCode> SC </statusCode>

    syntax EthereumCommand ::= "failure" String | "success"
 // -------------------------------------------------------
    //rule <k> success => . ... </k>
    //     <exit-code> _ => 0 </exit-code>
    //     <mode> _ => SUCCESS </mode>
    //     <endPC> _ => 0 </endPC>

    rule <k>          failure _ => . ... </k>
    rule <k> #halt ~> failure _ => . ... </k>
```

### Running Tests

-   `run` runs a given set of Ethereum tests (from the test-set).

Note that `TEST` is sorted here so that key `"network"` comes before key `"pre"`.

```k
    syntax EthereumCommand ::= "run" JSON
 // -------------------------------------
    rule <k> run { .JSONs } => . ... </k>
    rule <k> run { TESTID : { TEST:JSONs } , TESTS }
          => run ( TESTID : { qsortJSONs(TEST) } )
          ~> #if #hasPost?( { TEST } ) #then .K #else exception #fi
          ~> clear
          ~> run { TESTS }
         ...
         </k>

    syntax Bool ::= "#hasPost?" "(" JSON ")" [function]
 // ---------------------------------------------------
    rule #hasPost? ({ .JSONs }) => false
    rule #hasPost? ({ (KEY:String) : _ , REST }) => (KEY in #postKeys) orBool #hasPost? ({ REST })
```

-   `#loadKeys` are all the JSON nodes which should be considered as loads before execution.

```k
    syntax Set ::= "#loadKeys" [function]
 // -------------------------------------
    rule #loadKeys => ( SetItem("env") SetItem("pre") SetItem("rlp") SetItem("network") SetItem("genesisRLP") )

    rule <k> run  TESTID : { KEY : (VAL:JSON) , REST } => load KEY : VAL ~> run TESTID : { REST } ... </k>
      requires KEY in #loadKeys

    rule <k> run _TESTID : { "blocks" : [ { KEY : VAL , REST1 => REST1 }, .JSONs ] , ( REST2 => KEY : VAL , REST2 ) } ... </k>
    rule <k> run  TESTID : { "blocks" : [ { .JSONs }, .JSONs ] , REST } => run TESTID : { REST }                      ... </k>
```

-   `#execKeys` are all the JSON nodes which should be considered for execution (between loading and checking).

```k
    syntax Set ::= "#execKeys" [function]
 // -------------------------------------
    rule #execKeys => ( SetItem("exec") SetItem("lastblockhash") )

    rule <k> run  TESTID : { KEY : (VAL:JSON) , NEXT , REST } => run TESTID : { NEXT , KEY : VAL , REST } ... </k>
      requires KEY in #execKeys

    rule <k> run _TESTID : { "exec" : (EXEC:JSON) } => loadCallState EXEC ~> start ~> flush ... </k>
    rule <k> run _TESTID : { "lastblockhash" : (_:String) } => #startBlock ~> startTx    ... </k>

    rule <k> load "exec" : J => loadCallState J ... </k>

    //rule <k> loadCallState { "caller" : (ACCTFROM:Int), REST => REST } ... </k> <caller> _ => ACCTFROM </caller>
    //rule <k> loadCallState { "origin" : (ORIG:Int), REST => REST }     ... </k> <origin> _ => ORIG     </origin>
    //rule <k> loadCallState { "address" : (ACCTTO:Int), REST => REST }  ... </k> <id>     _ => ACCTTO   </id>

    rule <k> loadCallState { "code" : (CODE:OpCodes), REST } => #loadProgram #asmOpCodes(CODE) ~> loadCallState { REST } ... </k>

    rule <k> loadCallState { KEY : ((VAL:String) => #parseWord(VAL)), _ } ... </k>
      requires KEY in (SetItem("gas") SetItem("gasPrice") SetItem("value"))

    rule <k> loadCallState { KEY : ((VAL:String) => #parseHexWord(VAL)), _ } ... </k>
      requires KEY in (SetItem("address") SetItem("caller") SetItem("origin"))

    rule <k> loadCallState { "code" : ((CODE:String) => #parseByteStack(CODE)), _ } ... </k>
```

-   `#postKeys` are a subset of `#checkKeys` which correspond to post-state account checks.
-   `#checkKeys` are all the JSON nodes which should be considered as checks after execution.

```k
    syntax Set ::= "#postKeys" [function] | "#allPostKeys" [function] | "#checkKeys" [function]
 // -------------------------------------------------------------------------------------------
    rule #postKeys    => ( SetItem("post") SetItem("postState") SetItem("postStateHash") )
    rule #allPostKeys => ( #postKeys SetItem("expect") SetItem("export") SetItem("expet") )
    rule #checkKeys   => ( #allPostKeys SetItem("logs") SetItem("out") SetItem("gas")
                           SetItem("blockHeader") SetItem("transactions") SetItem("uncleHeaders") SetItem("genesisBlockHeader")
                         )

    rule <k> run TESTID : { KEY : (VAL:JSON) , REST } => run TESTID : { REST } ~> check TESTID : { "post" : VAL } ... </k> requires KEY in #allPostKeys
    rule <k> run TESTID : { KEY : (VAL:JSON) , REST } => run TESTID : { REST } ~> check TESTID : { KEY    : VAL } ... </k> requires KEY in #checkKeys andBool notBool KEY in #allPostKeys
```

-   `#discardKeys` are all the JSON nodes in the tests which should just be ignored.

```k
    syntax Set ::= "#discardKeys" [function]
 // ----------------------------------------
    rule #discardKeys => ( SetItem("//") SetItem("_info") SetItem("callcreates") SetItem("sealEngine") )

    rule <k> run TESTID : { KEY : _ , REST } => run TESTID : { REST } ... </k> requires KEY in #discardKeys
```

-   `driver.md` specific handling of state-loader commands

```k
    rule <k> load "account" : { ACCTID : ACCT } => loadAccount ACCTID ACCT ... </k>

    rule <k> loadAccount _ { "balance" : ((VAL:String)      => #parseWord(VAL)),        _ } ... </k>
    rule <k> loadAccount _ { "nonce"   : ((VAL:String)      => #parseWord(VAL)),        _ } ... </k>
    rule <k> loadAccount _ { "code"    : ((CODE:String)     => #parseByteStack(CODE)),  _ } ... </k>
    rule <k> loadAccount _ { "storage" : ({ STORAGE:JSONs } => #parseMap({ STORAGE })), _ } ... </k>

    rule <k> loadTransaction _ { "gasLimit" : (TG:String => #asWord(#parseByteStackRaw(TG))), _      } ... </k>
    rule <k> loadTransaction _ { "gasPrice" : (TP:String => #asWord(#parseByteStackRaw(TP))), _      } ... </k>
    rule <k> loadTransaction _ { "nonce"    : (TN:String => #asWord(#parseByteStackRaw(TN))), _      } ... </k>
    rule <k> loadTransaction _ { "v"        : (TW:String => #asWord(#parseByteStackRaw(TW))), _      } ... </k>
    rule <k> loadTransaction _ { "value"    : (TV:String => #asWord(#parseByteStackRaw(TV))), _      } ... </k>
    rule <k> loadTransaction _ { "to"       : (TT:String => #asAccount(#parseByteStackRaw(TT))), _   } ... </k>
    rule <k> loadTransaction _ { "data"     : (TI:String => #parseByteStackRaw(TI)), _               } ... </k>
    rule <k> loadTransaction _ { "r"        : (TR:String => #padToWidth(32, #parseByteStackRaw(TR))), _ } ... </k>
    rule <k> loadTransaction _ { "s"        : (TS:String => #padToWidth(32, #parseByteStackRaw(TS))), _ } ... </k>
```

### Checking State

-   `check_` checks if an account/transaction appears in the world-state as stated.

```k
    syntax EthereumCommand ::= "check" JSON
 // ---------------------------------------
    //rule <k> #halt ~> check J:JSON => check J ~> #halt ... </k>

    //rule <k> check DATA : { .JSONs } => . ... </k> requires DATA =/=String "transactions"
    //rule <k> check DATA : [ .JSONs ] => . ... </k> requires DATA =/=String "ommerHeaders"

    //rule <k> check DATA : { (KEY:String) : VALUE , REST } => check DATA : { KEY : VALUE } ~> check DATA : { REST } ... </k>
    //  requires REST =/=K .JSONs andBool notBool DATA in (SetItem("callcreates") SetItem("transactions"))

    //rule <k> check DATA : [ { TEST } , REST ] => check DATA : { TEST } ~> check DATA : [ REST ] ... </k>
    //  requires DATA =/=String "transactions"

    //rule <k> check (KEY:String) : { JS:JSONs => qsortJSONs(JS) } ... </k>
    //  requires KEY in (SetItem("callcreates")) andBool notBool sortedJSONs(JS)

    //rule <k> check TESTID : { "post" : (POST:String) } => check "blockHeader" : {  "stateRoot" : #parseWord(POST) } ~> failure TESTID ... </k>
    //rule <k> check TESTID : { "post" : { POST } } => check "account" : { POST } ~> failure TESTID ... </k>

    //rule <k> check "account" : { ACCTID:Int : { KEY : VALUE , REST } } => check "account" : { ACCTID : { KEY : VALUE } } ~> check "account" : { ACCTID : { REST } } ... </k>
    //  requires REST =/=K .JSONs

    //rule <k> check "account" : { ((ACCTID:String) => #parseAddr(ACCTID)) : _ACCT }                             ... </k>
    //rule <k> check "account" : { (_ACCT:Int) : { "balance" : ((VAL:String)      => #parseWord(VAL)) } }        ... </k>
    //rule <k> check "account" : { (_ACCT:Int) : { "nonce"   : ((VAL:String)      => #parseWord(VAL)) } }        ... </k>
    //rule <k> check "account" : { (_ACCT:Int) : { "code"    : ((CODE:String)     => #parseByteStack(CODE)) } }  ... </k>
    //rule <k> check "account" : { (_ACCT:Int) : { "storage" : ({ STORAGE:JSONs } => #parseMap({ STORAGE })) } } ... </k>

    //rule <mode> EXECMODE </mode>
    //     <k> check "account" : { ACCT : { "balance" : (BAL:Int) } } => . ... </k>
    //     <account>
    //       <acctID> ACCT </acctID>
    //       <balance> BAL </balance>
    //       ...
    //     </account>
    //  requires EXECMODE =/=K VMTESTS

    //rule <mode> VMTESTS </mode>
    //     <k> check "account" : { _ACCT : { "balance" : (_:Int) } } => . ... </k>

    //rule <k> check "account" : {  ACCT : { "nonce" : (NONCE:Int) } } => . ... </k>
    //     <account>
    //       <acctID> ACCT </acctID>
    //       <nonce> NONCE </nonce>
    //       ...
    //     </account>

    //rule <k> check "account" : { ACCT : { "storage" : (STORAGE:Map) } } => . ... </k>
    //     <account>
    //       <acctID> ACCT </acctID>
    //       <storage> ACCTSTORAGE </storage>
    //       ...
    //     </account>
    //  requires #removeZeros(ACCTSTORAGE) ==K STORAGE

    //rule <k> check "account" : { ACCT : { "code" : (CODE:ByteArray) } } => . ... </k>
    //     <account>
    //       <acctID> ACCT </acctID>
    //       <code> CODE </code>
    //       ...
    //     </account>
```

-   `#removeZeros` removes any entries in a map with zero values.

```k
    syntax Map ::= #removeZeros ( Map ) [function]
                 | #removeZeros ( List , Map ) [function, klabel(#removeZerosAux)]
 // ------------------------------------------------------------------------------
    rule #removeZeros( M )                                   => #removeZeros(Set2List(keys(M)), M)
    rule #removeZeros( .List, .Map )                         => .Map
    rule #removeZeros( ListItem(KEY) L, KEY |-> 0 REST )     => #removeZeros(L, REST)
    rule #removeZeros( ListItem(KEY) L, KEY |-> VALUE REST ) => KEY |-> VALUE #removeZeros(L, REST) requires VALUE =/=K 0
```

Here we check the other post-conditions associated with an EVM test.

```k
    //rule <k> check TESTID : { "out" : OUT } => check "out" : OUT ~> failure TESTID ... </k>
 // ---------------------------------------------------------------------------------------
    //rule <k> check "out" : ((OUT:String) => #parseByteStack(OUT)) ... </k>
    //rule <k> check "out" : OUT => . ... </k> <output> OUT </output>

    //rule <k> check TESTID : { "logs" : LOGS } => check "logs" : LOGS ~> failure TESTID ... </k>
 // -------------------------------------------------------------------------------------------
    //rule <k> check "logs" : HASH:String => . ... </k> <log> SL </log> requires #parseHexBytes(Keccak256(#rlpEncodeLogs(SL))) ==K #parseByteStack(HASH)

    //rule <k> check TESTID : { "gas" : GLEFT } => check "gas" : GLEFT ~> failure TESTID ... </k>
 // -------------------------------------------------------------------------------------------
    //rule <k> check "gas" : ((GLEFT:String) => #parseWord(GLEFT)) ... </k>
    //rule <k> check "gas" : GLEFT => . ... </k> <gas> GLEFT </gas>

    rule check TESTID : { "blockHeader" : BLOCKHEADER } => check "blockHeader" : BLOCKHEADER ~> failure TESTID
 // ----------------------------------------------------------------------------------------------------------
    rule <k> check "blockHeader" : { KEY : VALUE , REST } => check "blockHeader" : { KEY : VALUE } ~> check "blockHeader" : { REST } ... </k>
      requires REST =/=K .JSONs

    rule <k> check "blockHeader" : { _KEY : (VALUE:String => #parseByteStack(VALUE)) } ... </k>

    rule <k> check "blockHeader" : {  KEY : (VALUE:ByteArray => #asWord(VALUE)) } ... </k>
      requires KEY in ( SetItem("coinbase") SetItem("difficulty") SetItem("gasLimit") SetItem("gasUsed")
                        SetItem("mixHash") SetItem("nonce") SetItem("number") SetItem("parentHash")
                        SetItem("receiptTrie") SetItem("stateRoot") SetItem("timestamp")
                        SetItem("transactionsTrie") SetItem("uncleHash")
                      )

    //rule <k> check "blockHeader" : { "bloom"            : VALUE } => . ... </k> <logsBloom>        VALUE </logsBloom>
    //rule <k> check "blockHeader" : { "coinbase"         : VALUE } => . ... </k> <coinbase>         VALUE </coinbase>
    //rule <k> check "blockHeader" : { "difficulty"       : VALUE } => . ... </k> <difficulty>       VALUE </difficulty>
    //rule <k> check "blockHeader" : { "extraData"        : VALUE } => . ... </k> <extraData>        VALUE </extraData>
    //rule <k> check "blockHeader" : { "gasLimit"         : VALUE } => . ... </k> <gasLimit>         VALUE </gasLimit>
    //rule <k> check "blockHeader" : { "gasUsed"          : VALUE } => . ... </k> <gasUsed>          VALUE </gasUsed>
    //rule <k> check "blockHeader" : { "mixHash"          : VALUE } => . ... </k> <mixHash>          VALUE </mixHash>
    //rule <k> check "blockHeader" : { "nonce"            : VALUE } => . ... </k> <blockNonce>       VALUE </blockNonce>
    //rule <k> check "blockHeader" : { "number"           : VALUE } => . ... </k> <number>           VALUE </number>
    //rule <k> check "blockHeader" : { "parentHash"       : VALUE } => . ... </k> <previousHash>     VALUE </previousHash>
    //rule <k> check "blockHeader" : { "receiptTrie"      : VALUE } => . ... </k> <receiptsRoot>     VALUE </receiptsRoot>
    //rule <k> check "blockHeader" : { "stateRoot"        : VALUE } => . ... </k> <stateRoot>        VALUE </stateRoot>
    //rule <k> check "blockHeader" : { "timestamp"        : VALUE } => . ... </k> <timestamp>        VALUE </timestamp>
    //rule <k> check "blockHeader" : { "transactionsTrie" : VALUE } => . ... </k> <transactionsRoot> VALUE </transactionsRoot>
    //rule <k> check "blockHeader" : { "uncleHash"        : VALUE } => . ... </k> <ommersHash>       VALUE </ommersHash>

    //rule <k> check "blockHeader" : { "hash": HASH:ByteArray } => . ...</k>
    //     <previousHash>     HP </previousHash>
    //     <ommersHash>       HO </ommersHash>
    //     <coinbase>         HC </coinbase>
    //     <stateRoot>        HR </stateRoot>
    //     <transactionsRoot> HT </transactionsRoot>
    //     <receiptsRoot>     HE </receiptsRoot>
    //     <logsBloom>        HB </logsBloom>
    //     <difficulty>       HD </difficulty>
    //     <number>           HI </number>
    //     <gasLimit>         HL </gasLimit>
    //     <gasUsed>          HG </gasUsed>
    //     <timestamp>        HS </timestamp>
    //     <extraData>        HX </extraData>
    //     <mixHash>          HM </mixHash>
    //     <blockNonce>       HN </blockNonce>
    //  requires #blockHeaderHash(HP, HO, HC, HR, HT, HE, HB, HD, HI, HL, HG, HS, HX, HM, HN) ==Int #asWord(HASH)

    rule check TESTID : { "genesisBlockHeader" : BLOCKHEADER } => check "genesisBlockHeader" : BLOCKHEADER ~> failure TESTID
 // ------------------------------------------------------------------------------------------------------------------------
    rule <k> check "genesisBlockHeader" : { KEY : VALUE , REST } => check "genesisBlockHeader" : { KEY : VALUE } ~> check "genesisBlockHeader" : { REST } ... </k>
      requires REST =/=K .JSONs

    rule <k> check "genesisBlockHeader" : { KEY : _ } => .K ... </k> requires KEY =/=String "hash"

    rule <k> check "genesisBlockHeader" : { "hash": (HASH:String => #asWord(#parseByteStack(HASH))) } ... </k>
    //rule <k> check "genesisBlockHeader" : { "hash": HASH } => . ... </k>
    //     <blockhashes> ... ListItem(HASH) ListItem(_) </blockhashes>

    rule <k> check TESTID : { "transactions" : TRANSACTIONS } => check "transactions" : TRANSACTIONS ~> failure TESTID ... </k>
 // ---------------------------------------------------------------------------------------------------------------------------
    //rule <k> check "transactions" : [ .JSONs ] => . ... </k> <txOrder> .List                    </txOrder>
    //rule <k> check "transactions" : { .JSONs } => . ... </k> <txOrder> ListItem(_) => .List ... </txOrder>

    //rule <k> check "transactions" : [ TRANSACTION , REST ] => check "transactions" : TRANSACTION   ~> check "transactions" : [ REST ] ... </k>
    //rule <k> check "transactions" : { KEY : VALUE , REST } => check "transactions" : (KEY : VALUE) ~> check "transactions" : { REST } ... </k>

    //rule <k> check "transactions" : (_KEY : (VALUE:String    => #parseByteStack(VALUE))) ... </k>
    //rule <k> check "transactions" : ("to" : (VALUE:ByteArray => #asAccount(VALUE)))      ... </k>
    //rule <k> check "transactions" : ( KEY : (VALUE:ByteArray => #padToWidth(32, VALUE))) ... </k> requires KEY in (SetItem("r") SetItem("s")) andBool #sizeByteArray(VALUE) <Int 32
    //rule <k> check "transactions" : ( KEY : (VALUE:ByteArray => #asWord(VALUE)))         ... </k> requires KEY in (SetItem("gasLimit") SetItem("gasPrice") SetItem("nonce") SetItem("v") SetItem("value"))

    //rule <k> check "transactions" : ("data"     : VALUE) => . ... </k> <txOrder> ListItem(TXID) ... </txOrder> <message> <msgID> TXID </msgID> <data>       VALUE </data>       ... </message>
    //rule <k> check "transactions" : ("gasLimit" : VALUE) => . ... </k> <txOrder> ListItem(TXID) ... </txOrder> <message> <msgID> TXID </msgID> <txGasLimit> VALUE </txGasLimit> ... </message>
    //rule <k> check "transactions" : ("gasPrice" : VALUE) => . ... </k> <txOrder> ListItem(TXID) ... </txOrder> <message> <msgID> TXID </msgID> <txGasPrice> VALUE </txGasPrice> ... </message>
    //rule <k> check "transactions" : ("nonce"    : VALUE) => . ... </k> <txOrder> ListItem(TXID) ... </txOrder> <message> <msgID> TXID </msgID> <txNonce>    VALUE </txNonce>    ... </message>
    //rule <k> check "transactions" : ("r"        : VALUE) => . ... </k> <txOrder> ListItem(TXID) ... </txOrder> <message> <msgID> TXID </msgID> <sigR>       VALUE </sigR>       ... </message>
    //rule <k> check "transactions" : ("s"        : VALUE) => . ... </k> <txOrder> ListItem(TXID) ... </txOrder> <message> <msgID> TXID </msgID> <sigS>       VALUE </sigS>       ... </message>
    //rule <k> check "transactions" : ("to"       : VALUE) => . ... </k> <txOrder> ListItem(TXID) ... </txOrder> <message> <msgID> TXID </msgID> <to>         VALUE </to>         ... </message>
    //rule <k> check "transactions" : ("v"        : VALUE) => . ... </k> <txOrder> ListItem(TXID) ... </txOrder> <message> <msgID> TXID </msgID> <sigV>       VALUE </sigV>       ... </message>
    //rule <k> check "transactions" : ("value"    : VALUE) => . ... </k> <txOrder> ListItem(TXID) ... </txOrder> <message> <msgID> TXID </msgID> <value>      VALUE </value>      ... </message>
```

TODO: case with nonzero ommers.

```k
    //rule <k> check TESTID : { "uncleHeaders" : OMMERS } => check "ommerHeaders" : OMMERS ~> failure TESTID ... </k>
 // ---------------------------------------------------------------------------------------------------------------
    //rule <k> check "ommerHeaders" : [ .JSONs ] => . ... </k> <ommerBlockHeaders> [ .JSONs ] </ommerBlockHeaders>
```

```k
endmodule
```

FILE: optimizations.md

KEVM Optimizations
==================

These optimizations work on the LLVM and Haskell backend and are generated by the script `./optimizer/optimizations.sh`.

```k
// requires "evm.md"

module EVM-OPTIMIZATIONS-LEMMAS [kore, symbolic]
    imports EVM

    rule #sizeWordStack(WS           , N) => #sizeWordStack(WS, 0) +Int N requires N =/=Int 0                [simplification]
    rule #sizeWordStack(WS [ I := _ ], N) => #sizeWordStack(WS, N)        requires I <Int #sizeWordStack(WS) [simplification]

    rule #stackUnderflow(WS, N) => false requires N <=Int #sizeWordStack(WS) [simplification]

endmodule

module EVM-OPTIMIZATIONS [kore]
    imports EVM
    imports EVM-OPTIMIZATIONS-LEMMAS

// rule <kevm>
//        <k>
//          ( #next[ PUSH(N) ] => . ) ...
//        </k>
//        <schedule>
//          SCHED
//        </schedule>
//        <ethereum>
//          <evm>
//            <callState>
//              <program>
//                PGM
//              </program>
//              <wordStack>
//                ( WS => #asWord( PGM [ ( PCOUNT +Int 1 ) .. N ] ) : WS )
//              </wordStack>
//              <pc>
//                ( PCOUNT => ( ( PCOUNT +Int N ) +Int 1 ) )
//              </pc>
//              <gas>
//                ( GAVAIL => ( GAVAIL -Int Gverylow < SCHED > ) )
//              </gas>
//              ...
//            </callState>
//            ...
//          </evm>
//          ...
//        </ethereum>
//        ...
//      </kevm>
//   requires ( Gverylow < SCHED > <=Int GAVAIL )
//    andBool ( #sizeWordStack( #asWord( PGM [ ( PCOUNT +Int 1 ) .. N ] ) : WS ) <=Int 1024 )
//     [priority(40)]


// rule <kevm>
//        <k>
//          ( #next[ DUP(N) ] => . ) ...
//        </k>
//        <schedule>
//          SCHED
//        </schedule>
//        <ethereum>
//          <evm>
//            <callState>
//              <wordStack>
//                ( WS => WS [ ( N +Int -1 ) ] : WS )
//              </wordStack>
//              <pc>
//                ( PCOUNT => ( PCOUNT +Int 1 ) )
//              </pc>
//              <gas>
//                ( GAVAIL => ( GAVAIL -Int Gverylow < SCHED > ) )
//              </gas>
//              ...
//            </callState>
//            ...
//          </evm>
//          ...
//        </ethereum>
//        ...
//      </kevm>
//   requires #stackNeeded(DUP(N)) <=Int #sizeWordStack(WS)
//    andBool ( Gverylow < SCHED > <=Int GAVAIL )
//    andBool ( #sizeWordStack( WS [ ( N +Int -1 ) ] : WS ) <=Int 1024 )
//     [priority(40)]


// rule <kevm>
//        <k>
//          ( #next[ SWAP(N) ] => . ) ...
//        </k>
//        <schedule>
//          SCHED
//        </schedule>
//        <ethereum>
//          <evm>
//            <callState>
//              <wordStack>
//                ( W0 : WS => WS [ ( N +Int -1 ) ] : ( WS [ ( N +Int -1 ) := W0 ] ) )
//              </wordStack>
//              <pc>
//                ( PCOUNT => ( PCOUNT +Int 1 ) )
//              </pc>
//              <gas>
//                ( GAVAIL => ( GAVAIL -Int Gverylow < SCHED > ) )
//              </gas>
//              ...
//            </callState>
//            ...
//          </evm>
//          ...
//        </ethereum>
//        ...
//      </kevm>
//   requires #stackNeeded(SWAP(N)) <=Int #sizeWordStack(W0 : WS)
//    andBool ( Gverylow < SCHED > <=Int GAVAIL )
//    andBool ( #sizeWordStack( WS [ ( N +Int -1 ) ] : ( WS [ ( N +Int -1 ) := W0 ] ) ) <=Int 1024 )
//     [priority(40)]


// rule <kevm>
//        <k>
//          ( #next[ ADD ] => . ) ...
//        </k>
//        <schedule>
//          SCHED
//        </schedule>
//        <ethereum>
//          <evm>
//            <callState>
//              <wordStack>
//                ( W0 : W1 : WS => chop( ( W0 +Int W1 ) ) : WS )
//              </wordStack>
//              <pc>
//                ( PCOUNT => ( PCOUNT +Int 1 ) )
//              </pc>
//              <gas>
//                ( GAVAIL => ( GAVAIL -Int Gverylow < SCHED > ) )
//              </gas>
//              ...
//            </callState>
//            ...
//          </evm>
//          ...
//        </ethereum>
//        ...
//      </kevm>
//   requires ( Gverylow < SCHED > <=Int GAVAIL )
//    andBool ( #sizeWordStack( chop( ( W0 +Int W1 ) ) : WS ) <=Int 1024 )
//     [priority(40)]


// rule <kevm>
//        <k>
//          ( #next[ SUB ] => . ) ...
//        </k>
//        <schedule>
//          SCHED
//        </schedule>
//        <ethereum>
//          <evm>
//            <callState>
//              <wordStack>
//                ( W0 : W1 : WS => chop( ( W0 -Int W1 ) ) : WS )
//              </wordStack>
//              <pc>
//                ( PCOUNT => ( PCOUNT +Int 1 ) )
//              </pc>
//              <gas>
//                ( GAVAIL => ( GAVAIL -Int Gverylow < SCHED > ) )
//              </gas>
//              ...
//            </callState>
//            ...
//          </evm>
//          ...
//        </ethereum>
//        ...
//      </kevm>
//   requires ( Gverylow < SCHED > <=Int GAVAIL )
//    andBool ( #sizeWordStack( chop( ( W0 -Int W1 ) ) : WS ) <=Int 1024 )
//     [priority(40)]


// rule <kevm>
//        <k>
//          ( #next[ AND ] => . ) ...
//        </k>
//        <schedule>
//          SCHED
//        </schedule>
//        <ethereum>
//          <evm>
//            <callState>
//              <wordStack>
//                ( W0 : W1 : WS => W0 &Int W1 : WS )
//              </wordStack>
//              <pc>
//                ( PCOUNT => ( PCOUNT +Int 1 ) )
//              </pc>
//              <gas>
//                ( GAVAIL => ( GAVAIL -Int Gverylow < SCHED > ) )
//              </gas>
//              ...
//            </callState>
//            ...
//          </evm>
//          ...
//        </ethereum>
//        ...
//      </kevm>
//   requires ( Gverylow < SCHED > <=Int GAVAIL )
//    andBool ( #sizeWordStack( W0 &Int W1 : WS ) <=Int 1024 )
//     [priority(40)]


// rule <kevm>
//        <k>
//          ( #next[ LT ] => . ) ...
//        </k>
//        <schedule>
//          SCHED
//        </schedule>
//        <ethereum>
//          <evm>
//            <callState>
//              <wordStack>
//                ( W0 : W1 : WS => bool2Word( W0 <Int W1 ) : WS )
//              </wordStack>
//              <pc>
//                ( PCOUNT => ( PCOUNT +Int 1 ) )
//              </pc>
//              <gas>
//                ( GAVAIL => ( GAVAIL -Int Gverylow < SCHED > ) )
//              </gas>
//              ...
//            </callState>
//            ...
//          </evm>
//          ...
//        </ethereum>
//        ...
//      </kevm>
//   requires ( Gverylow < SCHED > <=Int GAVAIL )
//    andBool ( #sizeWordStack( bool2Word( W0 <Int W1 ) : WS ) <=Int 1024 )
//     [priority(40)]


// rule <kevm>
//        <k>
//          ( #next[ GT ] => . ) ...
//        </k>
//        <schedule>
//          SCHED
//        </schedule>
//        <ethereum>
//          <evm>
//            <callState>
//              <wordStack>
//                ( W0 : W1 : WS => bool2Word( W1 <Int W0 ) : WS )
//              </wordStack>
//              <pc>
//                ( PCOUNT => ( PCOUNT +Int 1 ) )
//              </pc>
//              <gas>
//                ( GAVAIL => ( GAVAIL -Int Gverylow < SCHED > ) )
//              </gas>
//              ...
//            </callState>
//            ...
//          </evm>
//          ...
//        </ethereum>
//        ...
//      </kevm>
//   requires ( Gverylow < SCHED > <=Int GAVAIL )
//    andBool ( #sizeWordStack( bool2Word( W1 <Int W0 ) : WS ) <=Int 1024 )
//     [priority(40)]


// {OPTIMIZATIONS}


endmodule
```

FILE: state-loader.md

State Manager
-------------

```k
//requires "evm.md"
//requires "asm.md"

module STATE-LOADER
    imports EVM
    imports EVM-ASSEMBLY

    syntax JSON ::= ByteArray | OpCodes | Map | SubstateLogEntry | Account
 // ----------------------------------------------------------------------

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
    //rule <k> clearTX => . ... </k>
    //     <output>          _ => .ByteArray </output>
    //     <memoryUsed>      _ => 0          </memoryUsed>
    //     <callDepth>       _ => 0          </callDepth>
    //     <callStack>       _ => .List      </callStack>
    //     <program>         _ => .ByteArray </program>
    //     <jumpDests>       _ => .Set       </jumpDests>
    //     <id>              _ => .Account   </id>
    //     <caller>          _ => .Account   </caller>
    //     <callData>        _ => .ByteArray </callData>
    //     <callValue>       _ => 0          </callValue>
    //     <wordStack>       _ => .WordStack </wordStack>
    //     <localMem>        _ => .Memory    </localMem>
    //     <pc>              _ => 0          </pc>
    //     <gas>             _ => 0          </gas>
    //     <callGas>         _ => 0          </callGas>
    //     <selfDestruct>    _ => .Set       </selfDestruct>
    //     <log>             _ => .List      </log>
    //     <refund>          _ => 0          </refund>
    //     <gasPrice>        _ => 0          </gasPrice>
    //     <origin>          _ => .Account   </origin>
    //     <touchedAccounts> _ => .Set       </touchedAccounts>

    syntax EthereumCommand ::= "clearBLOCK"
 // ---------------------------------------
    //rule <k> clearBLOCK => . ... </k>
    //     <previousHash>      _ => 0          </previousHash>
    //     <ommersHash>        _ => 0          </ommersHash>
    //     <coinbase>          _ => 0          </coinbase>
    //     <stateRoot>         _ => 0          </stateRoot>
    //     <transactionsRoot>  _ => 0          </transactionsRoot>
    //     <receiptsRoot>      _ => 0          </receiptsRoot>
    //     <logsBloom>         _ => .ByteArray </logsBloom>
    //     <difficulty>        _ => 0          </difficulty>
    //     <number>            _ => 0          </number>
    //     <gasLimit>          _ => 0          </gasLimit>
    //     <gasUsed>           _ => 0          </gasUsed>
    //     <timestamp>         _ => 0          </timestamp>
    //     <extraData>         _ => .ByteArray </extraData>
    //     <mixHash>           _ => 0          </mixHash>
    //     <blockNonce>        _ => 0          </blockNonce>
    //     <ommerBlockHeaders> _ => [ .JSONs ] </ommerBlockHeaders>
    //     <blockhashes>       _ => .List      </blockhashes>

    syntax EthereumCommand ::= "clearNETWORK"
 // -----------------------------------------
    //rule <k> clearNETWORK => . ... </k>
    //     <statusCode>     _ => .StatusCode </statusCode>
    //     <activeAccounts> _ => .Set        </activeAccounts>
    //     <accounts>       _ => .Bag        </accounts>
    //     <messages>       _ => .Bag        </messages>
    //     <schedule>       _ => DEFAULT     </schedule>
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
    rule <k> load _DATA : { .JSONs }             => .                                                   ... </k>
    rule <k> load  DATA : { KEY : VALUE , REST } => load DATA : { KEY : VALUE } ~> load DATA : { REST } ... </k>
      requires REST =/=K .JSONs andBool DATA =/=String "transaction"

    rule <k> load _DATA : [ .JSONs ]          => .                                            ... </k>
    rule <k> load  DATA : [ { TEST } , REST ] => load DATA : { TEST } ~> load DATA : [ REST ] ... </k>
```

Here we perform pre-proccesing on account data which allows "pretty" specification of input.

```k
    rule <k> load "pre" : { (ACCTID:String) : ACCT } => mkAcct #parseAddr(ACCTID) ~> loadAccount #parseAddr(ACCTID) ACCT ... </k>

    syntax EthereumCommand ::= "loadAccount" Int JSON
 // -------------------------------------------------
    //rule <k> loadAccount _ { .JSONs } => . ... </k>

    //rule <k> loadAccount ACCT { "balance" : (BAL:Int), REST => REST } ... </k>
    //     <account> <acctID> ACCT </acctID> <balance> _ => BAL </balance> ... </account>

    //rule <k> loadAccount ACCT { "code" : (CODE:ByteArray), REST => REST } ... </k>
    //     <account> <acctID> ACCT </acctID> <code> _ => CODE </code> ... </account>

    //rule <k> loadAccount ACCT { "nonce" : (NONCE:Int), REST => REST } ... </k>
    //     <account> <acctID> ACCT </acctID> <nonce> _ => NONCE </nonce> ... </account>

    //rule <k> loadAccount ACCT { "storage" : (STORAGE:Map), REST => REST } ... </k>
    //     <account> <acctID> ACCT </acctID> <origStorage> _ => STORAGE </origStorage> <storage> _ => STORAGE </storage> ... </account>
```

Here we load the environmental information.

```k
    rule <k> load "env" : { KEY : ((VAL:String) => #parseWord(VAL)) } ... </k>
      requires KEY in (SetItem("currentTimestamp") SetItem("currentGasLimit") SetItem("currentNumber") SetItem("currentDifficulty"))
    rule <k> load "env" : { KEY : ((VAL:String) => #parseHexWord(VAL)) } ... </k>
      requires KEY in (SetItem("currentCoinbase") SetItem("previousHash"))
 // ----------------------------------------------------------------------
    //rule <k> load "env" : { "currentCoinbase"   : (CB:Int)     } => . ... </k> <coinbase>     _ => CB     </coinbase>
    //rule <k> load "env" : { "currentDifficulty" : (DIFF:Int)   } => . ... </k> <difficulty>   _ => DIFF   </difficulty>
    //rule <k> load "env" : { "currentGasLimit"   : (GLIMIT:Int) } => . ... </k> <gasLimit>     _ => GLIMIT </gasLimit>
    //rule <k> load "env" : { "currentNumber"     : (NUM:Int)    } => . ... </k> <number>       _ => NUM    </number>
    //rule <k> load "env" : { "previousHash"      : (HASH:Int)   } => . ... </k> <previousHash> _ => HASH   </previousHash>
    //rule <k> load "env" : { "currentTimestamp"  : (TS:Int)     } => . ... </k> <timestamp>    _ => TS     </timestamp>

    syntax KItem ::= "loadCallState" JSON
 // -------------------------------------
    //rule <k> loadCallState { "data" : ( DATA:String => #parseByteStack( DATA ) ), _REST } ... </k>

    //rule <k> loadCallState { "code" : CODE:ByteArray, REST } => #loadProgram CODE ~> loadCallState { REST } ... </k>

    //rule <k> loadCallState { "gas" : GLIMIT:Int, REST => REST }      ... </k> <gas>       _ => GLIMIT </gas>
    //rule <k> loadCallState { "gasPrice" : GPRICE:Int, REST => REST } ... </k> <gasPrice>  _ => GPRICE </gasPrice>
    //rule <k> loadCallState { "value" : VALUE:Int, REST => REST }     ... </k> <callValue> _ => VALUE  </callValue>
    //rule <k> loadCallState { "data" : DATA:ByteArray, REST => REST } ... </k> <callData>  _ => DATA   </callData>

    //rule <k> loadCallState { .JSONs } => . ... </k>
```

The `"network"` key allows setting the fee schedule inside the test.

```k
    //rule <k> load "network" : SCHEDSTRING => . ... </k>
    //     <schedule> _ => #asScheduleString(SCHEDSTRING) </schedule>

    syntax Schedule ::= #asScheduleString ( String ) [function]
 // -----------------------------------------------------------
    //rule #asScheduleString("Frontier")          => FRONTIER
    //rule #asScheduleString("Homestead")         => HOMESTEAD
    //rule #asScheduleString("EIP150")            => TANGERINE_WHISTLE
    //rule #asScheduleString("EIP158")            => SPURIOUS_DRAGON
    //rule #asScheduleString("Byzantium")         => BYZANTIUM
    //rule #asScheduleString("Constantinople")    => CONSTANTINOPLE
    //rule #asScheduleString("ConstantinopleFix") => PETERSBURG
    //rule #asScheduleString("Istanbul")          => ISTANBUL
```

The `"rlp"` key loads the block information.

```k
    rule <k> load "rlp"        : (VAL:String => #rlpDecode(#unparseByteStack(#parseByteStack(VAL)))) ... </k>
    rule <k> load "genesisRLP" : (VAL:String => #rlpDecode(#unparseByteStack(#parseByteStack(VAL)))) ... </k>
 // ---------------------------------------------------------------------------------------------------------
    //rule <k> load "rlp" : [ [ HP , HO , HC , HR , HT , HE , HB , HD , HI , HL , HG , HS , HX , HM , HN , .JSONs ] , BT , BU , .JSONs ]
    //      => load "transaction" : BT
    //     ...
    //     </k>
    //     <previousHash>      _ => #asWord(#parseByteStackRaw(HP)) </previousHash>
    //     <ommersHash>        _ => #asWord(#parseByteStackRaw(HO)) </ommersHash>
    //     <coinbase>          _ => #asWord(#parseByteStackRaw(HC)) </coinbase>
    //     <stateRoot>         _ => #asWord(#parseByteStackRaw(HR)) </stateRoot>
    //     <transactionsRoot>  _ => #asWord(#parseByteStackRaw(HT)) </transactionsRoot>
    //     <receiptsRoot>      _ => #asWord(#parseByteStackRaw(HE)) </receiptsRoot>
    //     <logsBloom>         _ => #parseByteStackRaw(HB)          </logsBloom>
    //     <difficulty>        _ => #asWord(#parseByteStackRaw(HD)) </difficulty>
    //     <number>            _ => #asWord(#parseByteStackRaw(HI)) </number>
    //     <gasLimit>          _ => #asWord(#parseByteStackRaw(HL)) </gasLimit>
    //     <gasUsed>           _ => #asWord(#parseByteStackRaw(HG)) </gasUsed>
    //     <timestamp>         _ => #asWord(#parseByteStackRaw(HS)) </timestamp>
    //     <extraData>         _ => #parseByteStackRaw(HX)          </extraData>
    //     <mixHash>           _ => #asWord(#parseByteStackRaw(HM)) </mixHash>
    //     <blockNonce>        _ => #asWord(#parseByteStackRaw(HN)) </blockNonce>
    //     <ommerBlockHeaders> _ => BU                              </ommerBlockHeaders>

    //rule <k> load "genesisRLP": [ [ HP, HO, HC, HR, HT, HE:String, HB, HD, HI, HL, HG, HS, HX, HM, HN, .JSONs ], _, _, .JSONs ] => .K ... </k>
    //     <blockhashes> .List => ListItem(#blockHeaderHash(HP, HO, HC, HR, HT, HE, HB, HD, HI, HL, HG, HS, HX, HM, HN)) ListItem(#asWord(#parseByteStackRaw(HP))) ... </blockhashes>

    syntax EthereumCommand ::= "mkTX" Int
 // -------------------------------------
    //rule <k> mkTX TXID => . ... </k>
    //     <txOrder>   ... (.List => ListItem(TXID)) </txOrder>
    //     <txPending> ... (.List => ListItem(TXID)) </txPending>
    //     <messages>
    //        ( .Bag
    //       => <message>
    //            <msgID>      TXID:Int </msgID>
    //            <txGasPrice> 20000000000   </txGasPrice>
    //            <txGasLimit> 90000         </txGasLimit>
    //            ...
    //          </message>
    //        )
    //      ...
    //      </messages>

    rule <k> load "transaction" : [ [ TN , TP , TG , TT , TV , TI , TW , TR , TS ] , REST ]
          => mkTX !ID:Int
          ~> loadTransaction !ID { "data"  : TI   ,   "gasLimit" : TG   ,   "gasPrice" : TP
                                 , "nonce" : TN   ,   "r"        : TR   ,   "s"        : TS
                                 , "to"    : TT   ,   "v"        : TW   ,   "value"    : TV
                                 , .JSONs
                                 }
          ~> load "transaction" : [ REST ]
          ...
          </k>

    syntax EthereumCommand ::= "loadTransaction" Int JSON
 // -----------------------------------------------------
    // rule <k> loadTransaction _ { .JSONs } => . ... </k>

    // rule <k> loadTransaction TXID { GLIMIT : TG:Int, REST => REST } ... </k>
    //       <message> <msgID> TXID </msgID> <txGasLimit> _ => TG </txGasLimit> ... </message>
    //   requires GLIMIT in (SetItem("gas") SetItem("gasLimit"))

    // rule <k> loadTransaction TXID { "gasPrice" : TP:Int, REST => REST } ... </k>
    //       <message> <msgID> TXID </msgID> <txGasPrice> _ => TP </txGasPrice> ... </message>

    // rule <k> loadTransaction TXID { "nonce" : TN:Int, REST => REST } ... </k>
    //       <message> <msgID> TXID </msgID> <txNonce> _ => TN </txNonce> ... </message>

    // rule <k> loadTransaction TXID { "value" : TV:Int, REST => REST } ... </k>
    //       <message> <msgID> TXID </msgID> <value> _ => TV </value> ... </message>

    // rule <k> loadTransaction TXID { "to" : TT:Account, REST => REST } ... </k>
    //       <message> <msgID> TXID </msgID> <to> _ => TT </to> ... </message>

    // rule <k> loadTransaction TXID { "data" : TI:ByteArray, REST => REST } ... </k>
    //       <message> <msgID> TXID </msgID> <data> _ => TI </data> ... </message>

    // rule <k> loadTransaction TXID { "v" : TW:Int, REST => REST } ... </k>
    //       <message> <msgID> TXID </msgID> <sigV> _ => TW </sigV> ... </message>

    // rule <k> loadTransaction TXID { "r" : TR:ByteArray, REST => REST } ... </k>
    //       <message> <msgID> TXID </msgID> <sigR> _ => TR </sigR> ... </message>

    // rule <k> loadTransaction TXID { "s" : TS:ByteArray, REST => REST } ... </k>
    //       <message> <msgID> TXID </msgID> <sigS> _ => TS </sigS> ... </message>
```

### Block Identifiers

```k
    syntax BlockIdentifier ::= Int
                             | "LATEST"
                             | "PENDING"
                             | "EARLIEST"
 // -------------------------------------

    syntax BlockIdentifier ::= #parseBlockIdentifier ( JSON ) [function]
 // --------------------------------------------------------------------
    rule #parseBlockIdentifier(BLOCKNUM:Int) => BLOCKNUM
    rule #parseBlockIdentifier("pending")    => PENDING
    rule #parseBlockIdentifier("latest")     => LATEST
    rule #parseBlockIdentifier("earliest")   => EARLIEST
    rule #parseBlockIdentifier(BLOCKNUM)     => #parseWord(BLOCKNUM) [owise]
```
```k
endmodule
```

FILE: network.md

Network State
=============

This file represents all the network state present in the EVM.
It will incrementally build up to supporting the entire [EVM-C API].

```k
module NETWORK
    imports STRING-SYNTAX

    syntax String ::= StatusCode2String(StatusCode) [function]
 // ----------------------------------------------------------
```

EVM Status Codes
----------------

### Exceptional Codes

The following codes all indicate that the VM ended execution with an exception, but give details about how.

-   `EVMC_FAILURE` is a catch-all for generic execution failure.
-   `EVMC_INVALID_INSTRUCTION` indicates reaching the designated `INVALID` opcode.
-   `EVMC_UNDEFINED_INSTRUCTION` indicates that an undefined opcode has been reached.
-   `EVMC_OUT_OF_GAS` indicates that execution exhausted the gas supply.
-   `EVMC_BAD_JUMP_DESTINATION` indicates a `JUMP*` to a non-`JUMPDEST` location.
-   `EVMC_STACK_OVERFLOW` indicates pushing more than 1024 elements onto the wordstack.
-   `EVMC_STACK_UNDERFLOW` indicates popping elements off an empty wordstack.
-   `EVMC_CALL_DEPTH_EXCEEDED` indicates that we have executed too deeply a nested sequence of `CALL*` or `CREATE` opcodes.
-   `EVMC_INVALID_MEMORY_ACCESS` indicates that a bad memory access occured.
    This can happen when accessing local memory with `CODECOPY*` or `CALLDATACOPY`, or when accessing return data with `RETURNDATACOPY`.
-   `EVMC_STATIC_MODE_VIOLATION` indicates that a `STATICCALL` tried to change state.
    **TODO:** Avoid `_ERROR` suffix that suggests fatal error.
-   `EVMC_PRECOMPILE_FAILURE` indicates an errors in the precompiled contracts (eg. invalid points handed to elliptic curve functions).

```k
    syntax ExceptionalStatusCode ::= "EVMC_FAILURE"
                                   | "EVMC_INVALID_INSTRUCTION"
                                   | "EVMC_UNDEFINED_INSTRUCTION"
                                   | "EVMC_OUT_OF_GAS"
                                   | "EVMC_BAD_JUMP_DESTINATION"
                                   | "EVMC_STACK_OVERFLOW"
                                   | "EVMC_STACK_UNDERFLOW"
                                   | "EVMC_CALL_DEPTH_EXCEEDED"
                                   | "EVMC_INVALID_MEMORY_ACCESS"
                                   | "EVMC_STATIC_MODE_VIOLATION"
                                   | "EVMC_PRECOMPILE_FAILURE"
 // ----------------------------------------------------------
    rule StatusCode2String(EVMC_FAILURE)               => "EVMC_FAILURE"
    rule StatusCode2String(EVMC_INVALID_INSTRUCTION)   => "EVMC_INVALID_INSTRUCTION"
    rule StatusCode2String(EVMC_UNDEFINED_INSTRUCTION) => "EVMC_UNDEFINED_INSTRUCTION"
    rule StatusCode2String(EVMC_OUT_OF_GAS)            => "EVMC_OUT_OF_GAS"
    rule StatusCode2String(EVMC_BAD_JUMP_DESTINATION)  => "EVMC_BAD_JUMP_DESTINATION"
    rule StatusCode2String(EVMC_STACK_OVERFLOW)        => "EVMC_STACK_OVERFLOW"
    rule StatusCode2String(EVMC_STACK_UNDERFLOW)       => "EVMC_STACK_UNDERFLOW"
    rule StatusCode2String(EVMC_CALL_DEPTH_EXCEEDED)   => "EVMC_CALL_DEPTH_EXCEEDED"
    rule StatusCode2String(EVMC_INVALID_MEMORY_ACCESS) => "EVMC_INVALID_MEMORY_ACCESS"
    rule StatusCode2String(EVMC_STATIC_MODE_VIOLATION) => "EVMC_STATIC_MODE_VIOLATION"
    rule StatusCode2String(EVMC_PRECOMPILE_FAILURE)    => "EVMC_PRECOMPILE_FAILURE"
```

### Ending Codes

These additional status codes indicate that execution has ended in some non-exceptional way.

-   `EVMC_SUCCESS` indicates successful end of execution.
-   `EVMC_REVERT` indicates that the contract called `REVERT`.

```k
    syntax EndStatusCode ::= ExceptionalStatusCode
                           | "EVMC_SUCCESS"
                           | "EVMC_REVERT"
 // --------------------------------------
    rule StatusCode2String(EVMC_SUCCESS) => "EVMC_SUCCESS"
    rule StatusCode2String(EVMC_REVERT)  => "EVMC_REVERT"
```

### Other Codes

The following codes indicate other non-execution errors with the VM.

-   `EVMC_REJECTED` indicates malformed or wrong-version EVM bytecode.
-   `EVMC_INTERNAL_ERROR` indicates some other error that is unrecoverable but not due to the bytecode.
-   `.StatusCode` is an extra code added for "unset or unknown".

```k
    syntax StatusCode ::= EndStatusCode
                        | "EVMC_REJECTED"
                        | "EVMC_INTERNAL_ERROR"
                        | ".StatusCode"
 // -----------------------------------
    rule StatusCode2String(EVMC_REJECTED)       => "EVMC_REJECTED"
    rule StatusCode2String(EVMC_INTERNAL_ERROR) => "EVMC_INTERNAL_ERROR"
    rule StatusCode2String(.StatusCode)         => ""
```

Client/Network Codes
--------------------

The following are status codes used to report network state failures to the EVM from the client.
These are not present in the [EVM-C API].

-   `EVMC_ACCOUNT_ALREADY_EXISTS` indicates that a newly created account already exists.
-   `EVMC_BALANCE_UNDERFLOW` indicates an attempt to create an account which already exists.

```k
    syntax ExceptionalStatusCode ::= "EVMC_ACCOUNT_ALREADY_EXISTS"
                                   | "EVMC_BALANCE_UNDERFLOW"
 // ---------------------------------------------------------
    rule StatusCode2String(EVMC_ACCOUNT_ALREADY_EXISTS) => "EVMC_ACCOUNT_ALREADY_EXISTS"
    rule StatusCode2String(EVMC_BALANCE_UNDERFLOW)      => "EVMC_BALANCE_UNDERFLOW"
```

```k
endmodule
```

Resources
=========

[EVM-C API]: <https://github.com/ethereum/evmjit/blob/9abb8fd50d2a8164a417a153684701fcbdf54599/include/evm.h>
