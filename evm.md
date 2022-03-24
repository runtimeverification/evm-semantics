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

            <output>          .ByteArray  </output>           // H_RETURN
            <statusCode>      .StatusCode </statusCode>
            <endPC>           0           </endPC>
            <callStack>       .List       </callStack>
            <interimStates>   .List       </interimStates>
            <touchedAccounts> .Set        </touchedAccounts>

            <callState>
              <program> .ByteArray </program>
              <jumpDests> .Set </jumpDests>

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
            <substate>
              <selfDestruct>     .Set  </selfDestruct>            // A_s
              <log>              .List </log>                     // A_l
              <refund>           0     </refund>                  // A_r
              <accessedAccounts> .Set  </accessedAccounts>
              <accessedStorage>  .Map  </accessedStorage>
            </substate>

            // Immutable during a single transaction
            // -------------------------------------

//            <gasPrice> 0        </gasPrice>                   // I_p
//            <origin>   .Account </origin>                     // I_o

            // I_H* (block information)
//            <blockhashes> .List </blockhashes>
/*            <block>
              <previousHash>     0          </previousHash>     // I_Hp
              <ommersHash>       0          </ommersHash>       // I_Ho
              <coinbase>         0          </coinbase>         // I_Hc
              <stateRoot>        0          </stateRoot>        // I_Hr
              <transactionsRoot> 0          </transactionsRoot> // I_Ht
              <receiptsRoot>     0          </receiptsRoot>     // I_He
              <logsBloom>        .ByteArray </logsBloom>        // I_Hb
              <difficulty>       0          </difficulty>       // I_Hd
              <number>           0          </number>           // I_Hi
              <gasLimit>         0          </gasLimit>         // I_Hl
              <gasUsed>          0          </gasUsed>          // I_Hg
              <timestamp>        0          </timestamp>        // I_Hs
              <extraData>        .ByteArray </extraData>        // I_Hx
              <mixHash>          0          </mixHash>          // I_Hm
              <blockNonce>       0          </blockNonce>       // I_Hn
              <baseFee>          0          </baseFee>

              <ommerBlockHeaders> [ .JSONs ] </ommerBlockHeaders>
            </block>
*/
          </evm>

          // Ethereum Network
          // ================

          <network>

            // Chain identifier
            // ----------------
            <chainID> $CHAINID:Int </chainID>

            // Accounts Record
            // ---------------

            //<activeAccounts> .Set </activeAccounts>
            <accounts>
              <account multiplicity="*" type="Map">
                <acctID>      0                      </acctID>
                <balance>     0                      </balance>
                <code>        .ByteArray:AccountCode </code>
                <storage>     .Map                   </storage>
                <origStorage> .Map                   </origStorage>
                <nonce>       0                      </nonce>
              </account>
            </accounts>

            // Transactions Record
            // -------------------

//            <txOrder>   .List </txOrder>
//            <txPending> .List </txPending>

/*            <messages>
              <message multiplicity="*" type="Map">
                <msgID>         0          </msgID>
                <txNonce>       0          </txNonce>       // T_n
                <txGasPrice>    0          </txGasPrice>    // T_p
                <txGasLimit>    0          </txGasLimit>    // T_g
                <to>            .Account   </to>            // T_t
                <value>         0          </value>         // T_v
                <sigV>          0          </sigV>          // T_w
                <sigR>          .ByteArray </sigR>          // T_r
                <sigS>          .ByteArray </sigS>          // T_s
                <data>          .ByteArray </data>          // T_i/T_e
                <txAccess>      [ .JSONs ] </txAccess>      // T_a
                <txChainID>     0          </txChainID>     // T_c
                <txPriorityFee> 0          </txPriorityFee>
                <txMaxFee>      0          </txMaxFee>
                <txType>        .TxType    </txType>
              </message>
            </messages>
*/
          </network>

        </ethereum>
      </kevm>

    syntax EthereumSimulation
    syntax AccountCode ::= ByteArray
 // --------------------------------
```

Modal Semantics
---------------

Our semantics is modal, with the initial mode being set on the command line via `-cMODE=EXECMODE`.

-   `NORMAL` executes as a client on the network would.
-   `VMTESTS` skips `CALL*` and `CREATE` operations.

```k
    syntax Mode ::= "NORMAL"  [klabel(NORMAL), symbol]
                  | "VMTESTS" [klabel(VMTESTS), symbol]
 // ---------------------------------------------------
```

Control Flow
------------

### Exception Based

-   `#halt` indicates end of execution.
    It will consume anything related to the current computation behind it on the `<k>` cell.
-   `#end_` sets the `statusCode` and the program counter of the last executed opcode, then halts execution.

```k
    syntax KItem ::= "#halt" | "#end" StatusCode
 // --------------------------------------------
```

OpCode Execution
----------------

### Execution Macros

-   `#execute` loads the next opcode (or halts with `EVMC_SUCCESS` if there is no next opcode).

```k
    syntax KItem ::= "#execute"
```

### Execution Step

Here we load the correct number of arguments from the `wordStack` based on the sort of the opcode.

```k
    syntax KItem  ::= OpCode
    syntax OpCode ::= NullStackOp | UnStackOp | BinStackOp
                    | InternalOp
 // --------------------------------------------------------------------------------

    syntax InternalOp ::= UnStackOp   Int
                        | BinStackOp  Int Int
 // -------------------------------------------------
```

EVM Programs
============

EVM OpCodes
-----------

### EVM Control Flow

The `JUMP*` family of operations affect the current program counter.

```k
    syntax UnStackOp ::= "JUMP"
 // ---------------------------

    syntax BinStackOp ::= "JUMPI"
 // -----------------------------
    rule <k> JUMPI _DEST I => . ... </k>
      requires I ==Int 0

    rule <k> JUMPI  DEST I => JUMP DEST ... </k>
      requires I =/=Int 0
```

### `STOP`, `REVERT`, and `RETURN`

```k
    syntax NullStackOp ::= "STOP"
 // -----------------------------

    syntax BinStackOp ::= "RETURN"
 // ------------------------------

    syntax BinStackOp ::= "REVERT"
 // ------------------------------
```

Ethereum Network OpCodes
------------------------

Operators that require access to the rest of the Ethereum network world-state can be taken as a first draft of a "blockchain generic" language.

### Call Operations

The various `CALL*` (and other inter-contract control flow) operations will be desugared into these `InternalOp`s.

-   The `callLog` is used to store the `CALL*`/`CREATE` operations so that we can compare them against the test-set.

-   `#call_____` takes the calling account, the account to execute as, the account whose code should execute, the gas limit, the amount to transfer, the arguments, and the static flag.
-   `#callWithCode______` takes the calling account, the accout to execute as, the code to execute (as a bytearray), the gas limit, the amount to transfer, the arguments, and the static flag.
-   `#return__` is a placeholder for the calling program, specifying where to place the returned data in memory.

```k
    syntax Bool ::= #isPrecompiledAccount ( Int , Schedule ) [function, functional, smtlib(isPrecompiledAccount)]
 // -------------------------------------------------------------------------------------------------------------
    rule [isPrecompiledAccount.true]:  #isPrecompiledAccount(ACCTCODE, SCHED) => true  requires         ACCTCODE in #precompiledAccounts(SCHED)
    rule [isPrecompiledAccount.false]: #isPrecompiledAccount(ACCTCODE, SCHED) => false requires notBool ACCTCODE in #precompiledAccounts(SCHED)

    syntax Set ::= #computeValidJumpDests(ByteArray)            [function, memo]
                 | #computeValidJumpDests(ByteArray, Int, List) [function, klabel(#computeValidJumpDestsAux)]
 // ---------------------------------------------------------------------------------------------------------
    rule #computeValidJumpDests(PGM) => #computeValidJumpDests(PGM, 0, .List)
```

```{.k .bytes}
    syntax Set ::= #computeValidJumpDestsWithinBound(ByteArray, Int, List) [function]
 // ---------------------------------------------------------------------------------
    rule #computeValidJumpDests(PGM, I, RESULT) => List2Set(RESULT) requires I >=Int #sizeByteArray(PGM)
    rule #computeValidJumpDests(PGM, I, RESULT) => #computeValidJumpDestsWithinBound(PGM, I, RESULT) requires I <Int #sizeByteArray(PGM)

    rule #computeValidJumpDestsWithinBound(PGM, I, RESULT) => #computeValidJumpDests(PGM, I +Int 1, RESULT ListItem(I)) requires PGM [ I ] ==Int 91
    rule #computeValidJumpDestsWithinBound(PGM, I, RESULT) => #computeValidJumpDests(PGM, I +Int #widthOpCode(PGM [ I ]), RESULT) requires notBool PGM [ I ] ==Int 91
```

```k
    syntax Int ::= #widthOpCode(Int) [function]
 // -------------------------------------------
    rule #widthOpCode(W) => W -Int 94 requires W >=Int 96 andBool W <=Int 127
    rule #widthOpCode(_) => 1 [owise]

    syntax KItem ::= "#return" Int Int
 // ----------------------------------

    syntax InternalOp ::= "#refund" Exp [strict]
                        | "#setLocalMem" Int Int ByteArray
 // ------------------------------------------------------
    rule [refund]: <k> #refund G:Int => . ... </k> <gas> GAVAIL => GAVAIL +Int G </gas>

    rule <k> #setLocalMem START WIDTH WS => . ... </k>
         <localMem> LM => LM [ START := WS [ 0 .. minInt(WIDTH, #sizeByteArray(WS)) ] ] </localMem>
```

Precompiled Contracts
---------------------

-   `#precompiled` is a placeholder for the 9 pre-compiled contracts at addresses 1 through 9.

```k
    syntax NullStackOp   ::= PrecompiledOp
    syntax PrecompiledOp ::= #precompiled ( Int ) [function]
 // --------------------------------------------------------
    rule #precompiled(1) => ECREC

    syntax Set ::= #precompiledAccounts ( Schedule ) [function, functional]
 // -----------------------------------------------------------------------
```

-   `ECREC` performs ECDSA public key recovery.
-   `SHA256` performs the SHA2-257 hash function.
-   `RIP160` performs the RIPEMD-160 hash function.
-   `ID` is the identity function (copies input to output).

```k
    syntax PrecompiledOp ::= "ECREC"
 // --------------------------------
    rule <k> ECREC => #end EVMC_SUCCESS ... </k>
         <callData> DATA </callData>
         <output> _ => #ecrec(DATA [ 0 .. 32 ], DATA [ 32 .. 32 ], DATA [ 64 .. 32 ], DATA [ 96 .. 32 ]) </output>

    syntax ByteArray ::= #ecrec ( ByteArray , ByteArray , ByteArray , ByteArray ) [function]
                       | #ecrec ( Account )                                       [function]
 // ----------------------------------------------------------------------------------------
    rule [ecrec]: #ecrec(HASH, SIGV, SIGR, SIGS) => #ecrec(#sender(#unparseByteStack(HASH), #asWord(SIGV), #unparseByteStack(SIGR), #unparseByteStack(SIGS)))

    rule #ecrec(.Account) => .ByteArray
    rule #ecrec(N:Int)    => #padToWidth(32, #asByteStack(N))
```


Simplify next

```k
    syntax Exp     ::= Int
    syntax KResult ::= Int
    syntax Exp ::= Ccall         ( Schedule , BExp , Int , Int , Int , Bool ) [strict(2)]
                 | Ccallgas      ( Schedule , BExp , Int , Int , Int , Bool ) [strict(2)]
                 | Cselfdestruct ( Schedule , BExp , Int )                    [strict(2)]
 // -------------------------------------------------------------------------------------

    syntax BExp    ::= Bool
    syntax KResult ::= Bool

    syntax Bool ::= #accountEmpty ( AccountCode , Int , Int ) [function, klabel(accountEmpty), symbol]
 // --------------------------------------------------------------------------------------------------
    rule #accountEmpty(CODE, NONCE, BAL) => CODE ==K .ByteArray andBool NONCE ==Int 0 andBool BAL ==Int 0

    syntax Int ::= #allBut64th ( Int ) [function, functional, smtlib(gas_allBut64th)]
 // ---------------------------------------------------------------------------------
    rule [allBut64th.pos]: #allBut64th(N) => N -Int (N /Int 64) requires 0 <=Int N
    rule [allBut64th.neg]: #allBut64th(N) => 0                  requires N  <Int 0
```

### Default Schedule

### Istanbul Schedule

```k
    syntax Schedule ::= "ISTANBUL" [klabel(ISTANBUL_EVM), symbol, smtlib(schedule_ISTANBUL)]
 // ----------------------------------------------------------------------------------------
```

EVM Program Representations
===========================

EVM programs are represented algebraically in K, but programs can load and manipulate program data directly.
The opcodes `CODECOPY` and `EXTCODECOPY` rely on the assembled form of the programs being present.
The opcode `CREATE` relies on being able to interperet EVM data as a program.

This is a program representation dependence, which we might want to avoid.
Perhaps the only program representation dependence we should have is the hash of the program; doing so achieves:

-   Program representation independence (different analysis tools on the language don't have to ensure they have a common representation of programs, just a common interperetation of the data-files holding programs).
-   Programming language independence (we wouldn't even have to commit to a particular language or interperetation of the data-file).
-   Only depending on the hash allows us to know that we have *exactly* the correct data-file (program), and nothing more.

Disassembler
------------

After interpreting the strings representing programs as a `WordStack`, it should be changed into an `OpCodes` for use by the EVM semantics.

-   `#dasmOpCode` interperets a `Int` as an `OpCode`.

```k
    syntax OpCode ::= #dasmOpCode ( Int , Schedule ) [function, memo]
 // -----------------------------------------------------------------
endmodule
```
