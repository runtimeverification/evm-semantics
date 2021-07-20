EVM Execution
=============

### Overview

The EVM is a stack machine over some simple opcodes.
Most of the opcodes are "local" to the execution state of the machine, but some of them must interact with the world state.
This file only defines the local execution operations, the file `driver.md` will define the interactions with the world state.

```k
requires "data.md"
requires "network.md"

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
        <exit-code exit=""> 1 </exit-code>
        <mode> $MODE:Mode </mode>
        <schedule> $SCHEDULE:Schedule </schedule>

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
              <id>        .Account   </id>                    // I_a
              <caller>    .Account   </caller>                // I_s
              <callData>  .ByteArray </callData>              // I_d
              <callValue> 0          </callValue>             // I_v

              // \mu_*
              <wordStack>   .WordStack </wordStack>           // \mu_s
              <localMem>    .Memory    </localMem>            // \mu_m
              <pc>          0          </pc>                  // \mu_pc
              <gas>         0          </gas>                 // \mu_g
              <memoryUsed>  0          </memoryUsed>          // \mu_i
              <callGas>     0          </callGas>

              <static>    false </static>
              <callDepth> 0     </callDepth>
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
            <chainID> $CHAINID:Int </chainID>

            // Accounts Record
            // ---------------

            <activeAccounts> .Set </activeAccounts>
            <accounts> // KEEP
              <account multiplicity="*" type="Map">
                <acctID>      0                      </acctID>
                <balance>     0                      </balance>
                <code>        .ByteArray:AccountCode </code>
                <storage>     .Map                   </storage> // KEEP
                <origStorage> .Map                   </origStorage>
                <nonce>       0                      </nonce>
              </account>
            </accounts>

            // Transactions Record
            // -------------------

            <txOrder>   .List </txOrder>
            <txPending> .List </txPending>

            <messages>
              <message multiplicity="*" type="Map">
                <msgID>      0          </msgID>
                <txNonce>    0          </txNonce>            // T_n
                <txGasPrice> 0          </txGasPrice>         // T_p
                <txGasLimit> 0          </txGasLimit>         // T_g
                <to>         .Account   </to>                 // T_t
                <value>      0          </value>              // T_v
                <sigV>       0          </sigV>               // T_w
                <sigR>       .ByteArray </sigR>               // T_r
                <sigS>       .ByteArray </sigS>               // T_s
                <data>       .ByteArray </data>               // T_i/T_e
              </message>
            </messages>

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