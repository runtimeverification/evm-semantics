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

            <gasPrice> 0        </gasPrice>                   // I_p
            <origin>   .Account </origin>                     // I_o

            // I_H* (block information)
            <blockhashes> .List </blockhashes>
            <block>
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

            <txOrder>   .List </txOrder>
            <txPending> .List </txPending>

            <messages>
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

State Stacks
------------

### The CallStack

The `callStack` cell stores a list of previous VM execution states.

-   `#pushCallStack` saves a copy of VM execution state on the `callStack`.
-   `#popCallStack` restores the top element of the `callStack`.
-   `#dropCallStack` removes the top element of the `callStack`.

```k
    syntax InternalOp ::= "#pushCallStack"
 // --------------------------------------
    rule <k> #pushCallStack => . ... </k>
         <callStack> (.List => ListItem(CALLSTATE)) ... </callStack>
         <callState> CALLSTATE </callState>

    syntax InternalOp ::= "#popCallStack"
 // -------------------------------------
    rule <k> #popCallStack => . ... </k>
         <callStack>  (ListItem(CALLSTATE) => .List) ... </callStack>
         <callState> _ => CALLSTATE </callState>

    syntax InternalOp ::= "#dropCallStack"
 // --------------------------------------
    rule <k> #dropCallStack => . ... </k>
         <callStack> (ListItem(_) => .List) ... </callStack>
```

### The StateStack

The `interimStates` cell stores a list of previous world states.

-   `#pushWorldState` stores a copy of the current accounts and the substate at the top of the `interimStates` cell.
-   `#popWorldState` restores the top element of the `interimStates`.
-   `#dropWorldState` removes the top element of the `interimStates`.

```k
    syntax Accounts ::= "{" AccountsCellFragment "|" Set "|" SubstateCellFragment "}"
 // ---------------------------------------------------------------------------------

    syntax InternalOp ::= "#pushWorldState"
 // ---------------------------------------
    rule <k> #pushWorldState => .K ... </k>
         <interimStates> (.List => ListItem({ ACCTDATA | ACCTS | SUBSTATE })) ... </interimStates>
         <activeAccounts> ACCTS    </activeAccounts>
         <accounts>       ACCTDATA </accounts>
         <substate>       SUBSTATE </substate>

    syntax InternalOp ::= "#popWorldState"
 // --------------------------------------
    rule <k> #popWorldState => .K ... </k>
         <interimStates> (ListItem({ ACCTDATA | ACCTS | SUBSTATE }) => .List) ... </interimStates>
         <activeAccounts> _ => ACCTS    </activeAccounts>
         <accounts>       _ => ACCTDATA </accounts>
         <substate>       _ => SUBSTATE </substate>

    syntax InternalOp ::= "#dropWorldState"
 // ---------------------------------------
    rule <k> #dropWorldState => . ... </k> <interimStates> (ListItem(_) => .List) ... </interimStates>
    
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
    rule <k> #end SC => #halt ... </k>
         <statusCode> _ => SC     </statusCode>
         <endPC>      _ => PCOUNT </endPC>
         <pc>         PCOUNT      </pc>

    rule <k> #halt ~> (_:Int    => .) ... </k>
    rule <k> #halt ~> (_:OpCode => .) ... </k>
```

OpCode Execution
----------------

### Execution Macros

-   `#execute` loads the next opcode (or halts with `EVMC_SUCCESS` if there is no next opcode).

```k
    syntax KItem ::= "#execute"
 // ---------------------------
    rule [halt]: <k> #halt ~> (#execute => .) ... </k>
    rule [step]: <k> (. => #next [ #dasmOpCode(PGM [ PCOUNT ], SCHED) ]) ~> #execute ... </k>
                 <pc> PCOUNT </pc>
                 <program> PGM </program>
                 <schedule> SCHED </schedule>
      requires PCOUNT <Int #sizeByteArray(PGM)

    rule <k> (. => #end EVMC_SUCCESS) ~> #execute ... </k>
         <pc> PCOUNT </pc>
         <program> PGM </program>
         <output> _ => .ByteArray </output>
      requires PCOUNT >=Int #sizeByteArray(PGM)
```

### Single Step

If the program-counter points to an actual opcode, it's loaded into the `#next [_]` operator.
The `#next [_]` operator initiates execution by:

1.  checking if there will be a stack over/underflow, or a static mode violation,
2.  calculate any address conversions needed for items on the wordstack,
3.  executing the opcode (which includes any gas deduction needed), and
4.  adjusting the program counter.

```k
    syntax InternalOp ::= "#next" "[" OpCode "]"
 // --------------------------------------------
```

### Exceptional Checks

-   `#stackNeeded` is how many arguments that opcode will need off the top of the stack.
-   `#stackAdded` is how many arguments that opcode will push onto the top of the stack.
-   `#stackDelta` is the delta the stack will have after the opcode executes.

```k
    syntax Bool ::= #stackUnderflow ( WordStack , OpCode ) [function]
                  | #stackUnderflow ( WordStack , Int    ) [function, functional]
                  | #stackOverflow  ( WordStack , OpCode ) [function]
 // -----------------------------------------------------------------------------
    rule #stackUnderflow(_         , N:Int    ) => false                         requires notBool (N >Int 0)
    rule #stackUnderflow(_ : WS    , N:Int    ) => #stackUnderflow(WS, N -Int 1) requires          N >Int 0
    rule #stackUnderflow(.WordStack, N:Int    ) => true                          requires          N >Int 0
```

-   `#changesState` is true if the given opcode will change `<network>` state given the arguments.

```k
    syntax Bool ::= #changesState ( OpCode , WordStack ) [function]
 // ---------------------------------------------------------------
```

### Execution Step

Here we load the correct number of arguments from the `wordStack` based on the sort of the opcode.

```k
    syntax KItem  ::= OpCode
    syntax OpCode ::= NullStackOp | UnStackOp | BinStackOp | TernStackOp | QuadStackOp
                    | InvalidOp | InternalOp
 // --------------------------------------------------------------------------------

    syntax InternalOp ::= UnStackOp   Int
                        | BinStackOp  Int Int
                        | TernStackOp Int Int Int
                        | QuadStackOp Int Int Int Int
 // -------------------------------------------------
```

### Program Counter

All operators except for `PUSH` and `JUMP*` increment the program counter by 1.
The arguments to `PUSH` must be skipped over (as they are inline), and the opcode `JUMP` already affects the program counter in the correct way.

-   `#pc` calculates the next program counter of the given operator.

```k
    syntax InternalOp ::= "#pc" "[" OpCode "]"
 // ------------------------------------------
    rule <k> #pc [ OP ] => . ... </k>
         <pc> PCOUNT => PCOUNT +Int #widthOp(OP) </pc>

    syntax Int ::= #widthOp ( OpCode ) [function]
 // ---------------------------------------------
```

After executing a transaction, it's necessary to have the effect of the substate log recorded.

-   `#finalizeStorage` updates the origStorage cell with the new values of storage.
-   `#finalizeTx` makes the substate log actually have an effect on the state.
-   `#deleteAccounts` deletes the accounts specified by the self destruct list.

```k
    syntax InternalOp ::= #finalizeStorage ( List )
 // -----------------------------------------------
    rule <k> #finalizeStorage((ListItem(ACCT) => .List) _) ... </k>
         <account>
           <acctID> ACCT </acctID>
           <storage> STORAGE </storage>
           <origStorage> _ => STORAGE </origStorage>
           ...
         </account>

    rule <k> #finalizeStorage(.List) => . ... </k>

    syntax InternalOp ::= #finalizeTx ( Bool )
                        | #deleteAccounts ( List )
 // ----------------------------------------------
    rule <k> #finalizeTx(true) => #finalizeStorage(Set2List(ACCTS)) ... </k>
         <selfDestruct> .Set </selfDestruct>
         <activeAccounts> ACCTS </activeAccounts>
         <accessedAccounts> _ => .Set </accessedAccounts>
         <accessedStorage> _ => .Map </accessedStorage>

    rule <k> (.K => #newAccount MINER) ~> #finalizeTx(_)... </k>
         <coinbase> MINER </coinbase>
         <activeAccounts> ACCTS </activeAccounts>
      requires notBool MINER in ACCTS

    rule <k> #finalizeTx(false) ... </k>
         <schedule> SCHED </schedule>
         <gas> GAVAIL => G*(GAVAIL, GLIMIT, REFUND, SCHED) </gas>
         <refund> REFUND => 0 </refund>
         <txPending> ListItem(MSGID:Int) ... </txPending>
         <message>
            <msgID> MSGID </msgID>
            <txGasLimit> GLIMIT </txGasLimit>
            ...
         </message>
      requires REFUND =/=Int 0

    rule <k> #finalizeTx(false => true) ... </k>
         <baseFee> BFEE </baseFee>
         <origin> ORG </origin>
         <coinbase> MINER </coinbase>
         <gas> GAVAIL </gas>
         <gasUsed> GUSED => GUSED +Int GLIMIT -Int GAVAIL </gasUsed>
         <gasPrice> GPRICE </gasPrice>
         <refund> 0 </refund>
         <account>
           <acctID> ORG </acctID>
           <balance> ORGBAL => ORGBAL +Int GAVAIL *Int GPRICE </balance>
           ...
         </account>
         <account>
           <acctID> MINER </acctID>
           <balance> MINBAL => MINBAL +Int (GLIMIT -Int GAVAIL) *Int (GPRICE -Int BFEE) </balance>
           ...
         </account>
         <txPending> ListItem(TXID:Int) => .List ... </txPending>
         <message>
           <msgID> TXID </msgID>
           <txGasLimit> GLIMIT </txGasLimit>
           ...
         </message>
      requires ORG =/=Int MINER

    rule <k> #finalizeTx(false => true) ... </k>
         <baseFee> BFEE </baseFee>
         <origin> ACCT </origin>
         <coinbase> ACCT </coinbase>
         <gas> GAVAIL </gas>
         <gasUsed> GUSED => GUSED +Int GLIMIT -Int GAVAIL </gasUsed>
         <gasPrice> GPRICE </gasPrice>
         <refund> 0 </refund>
         <account>
           <acctID> ACCT </acctID>
           <balance> BAL => BAL +Int GLIMIT *Int (GPRICE -Int BFEE) </balance>
           ...
         </account>
         <txPending> ListItem(MsgId:Int) => .List ... </txPending>
         <message>
           <msgID> MsgId </msgID>
           <txGasLimit> GLIMIT </txGasLimit>
           ...
         </message>

    rule <k> (. => #deleteAccounts(Set2List(ACCTS))) ~> #finalizeTx(true) ... </k>
         <selfDestruct> ACCTS => .Set </selfDestruct>
      requires size(ACCTS) >Int 0

    rule <k> #deleteAccounts(ListItem(ACCT) ACCTS) => #deleteAccounts(ACCTS) ... </k>
         <activeAccounts> ... (SetItem(ACCT) => .Set) </activeAccounts>
         <accounts>
           ( <account>
               <acctID> ACCT </acctID>
               ...
             </account>
          => .Bag
           )
           ...
         </accounts>

    rule <k> #deleteAccounts(.List) => . ... </k>
```

### Block processing

-   `#startBlock` is used to signal that we are about to start mining a block and block initialization should take place (before transactions are executed).
-   `#finalizeBlock` is used to signal that block finalization procedures should take place (after transactions have executed).
-   `#rewardOmmers(_)` pays out the reward to uncle blocks so that blocks are orphaned less often in Ethereum.

```k
    syntax EthereumCommand ::= "#startBlock"
 // ----------------------------------------
    rule <k> #startBlock => . ... </k>
         <gasUsed> _ => 0 </gasUsed>
         <log> _ => .List </log>
         <logsBloom> _ => #padToWidth(256, .ByteArray) </logsBloom>

    syntax EthereumCommand ::= "#finalizeBlock" | #rewardOmmers ( JSONs )
 // ---------------------------------------------------------------------


    syntax ByteArray ::= #bloomFilter(List)      [function]
                       | #bloomFilter(List, Int) [function, klabel(#bloomFilterAux)]
 // --------------------------------------------------------------------------------
    rule #bloomFilter(L) => #bloomFilter(L, 0)

    rule #bloomFilter(.List, B) => #padToWidth(256, #asByteStack(B))
    rule #bloomFilter(ListItem({ ACCT | TOPICS | _ }) L, B) => #bloomFilter(ListItem(#padToWidth(20, #asByteStack(ACCT))) listAsByteArrays(TOPICS) L, B)

    syntax List ::= listAsByteArrays(List) [function]
 // -------------------------------------------------
    rule listAsByteArrays(.List) => .List
    rule listAsByteArrays(ListItem(TOPIC) L) => ListItem(#padToWidth(32, #asByteStack(TOPIC))) listAsByteArrays(L)

    rule #bloomFilter(ListItem(WS:ByteArray) L, B) => #bloomFilter(L, B |Int M3:2048(WS))
```

- `M3:2048` computes the 2048-bit hash of a log entry in which exactly 3 bits are set. This is used to compute the Bloom filter of a log entry.

```k
    syntax Int ::= "M3:2048" "(" ByteArray ")" [function]
 // -----------------------------------------------------
    rule M3:2048(WS) => setBloomFilterBits(#parseByteStack(Keccak256(#unparseByteStack(WS))))

    syntax Int ::= setBloomFilterBits(ByteArray) [function]
 // -------------------------------------------------------
    rule setBloomFilterBits(HASH) => (1 <<Int getBloomFilterBit(HASH, 0)) |Int (1 <<Int getBloomFilterBit(HASH, 2)) |Int (1 <<Int getBloomFilterBit(HASH, 4))

    syntax Int ::= getBloomFilterBit(ByteArray, Int) [function]
 // -----------------------------------------------------------
    rule getBloomFilterBit(X, I) => #asInteger(X [ I .. 2 ]) %Int 2048
```

EVM Programs
============

EVM OpCodes
-----------


### Internal Operations

These are just used by the other operators for shuffling local execution state around on the EVM.

-   `#push` will push an element to the `wordStack` without any checks.
-   `#setStack_` will set the current stack to the given one.

```k
    syntax InternalOp ::= "#push" | "#setStack" WordStack
 // -----------------------------------------------------
    rule <k> W0:Int ~> #push => . ... </k> <wordStack> WS => W0 : WS </wordStack>
    rule <k> #setStack WS    => . ... </k> <wordStack> _  => WS      </wordStack>
```

-   `#newAccount_` allows declaring a new empty account with the given address (and assumes the rounding to 160 bits has already occured).
    If the account already exists with non-zero nonce or non-empty code, an exception is thrown.
    Otherwise, if the account already exists, the storage is cleared.

```k
    syntax InternalOp ::= "#newAccount" Int
                        | "#newExistingAccount" Int
                        | "#newFreshAccount" Int
 // --------------------------------------------
    rule <k> #newAccount ACCT => #newExistingAccount ACCT ... </k>
         <activeAccounts> ACCTS:Set </activeAccounts>
      requires ACCT in ACCTS

    rule <k> #newAccount ACCT => #newFreshAccount ACCT ... </k>
         <activeAccounts> ACCTS:Set </activeAccounts>
      requires notBool ACCT in ACCTS

    rule <k> #newExistingAccount ACCT => #end EVMC_ACCOUNT_ALREADY_EXISTS ... </k>
         <account>
           <acctID> ACCT  </acctID>
           <code>   CODE  </code>
           <nonce>  NONCE </nonce>
           ...
         </account>
      requires CODE =/=K .ByteArray orBool NONCE =/=Int 0

    rule <k> #newExistingAccount ACCT => . ... </k>
         <account>
           <acctID>      ACCT      </acctID>
           <code>        WS        </code>
           <nonce>       0         </nonce>
           <storage>     _ => .Map </storage>
           <origStorage> _ => .Map </origStorage>
           ...
         </account>
      requires #sizeByteArray(WS) ==Int 0

    rule <k> #newFreshAccount ACCT => . ... </k>
         <activeAccounts> ... (.Set => SetItem(ACCT)) ... </activeAccounts>
         <accounts>
           ( .Bag
          => <account>
               <acctID> ACCT </acctID>
               ...
             </account>
           )
           ...
         </accounts>
```

-   `#transferFunds` moves money from one account into another, creating the destination account if it doesn't exist.

```k
    syntax InternalOp ::= "#transferFunds" Int Int Int
 // --------------------------------------------------
    rule <k> #transferFunds ACCT ACCT VALUE => . ... </k>
         <account>
           <acctID> ACCT </acctID>
           <balance> ORIGFROM </balance>
           ...
         </account>
      requires VALUE <=Int ORIGFROM

    rule <k> #transferFunds ACCTFROM ACCTTO VALUE => . ... </k>
         <account>
           <acctID> ACCTFROM </acctID>
           <balance> ORIGFROM => ORIGFROM -Word VALUE </balance>
           ...
         </account>
         <account>
           <acctID> ACCTTO </acctID>
           <balance> ORIGTO => ORIGTO +Word VALUE </balance>
           ...
         </account>
      requires ACCTFROM =/=K ACCTTO andBool VALUE <=Int ORIGFROM

    rule <k> #transferFunds ACCTFROM _ACCTTO VALUE => #end EVMC_BALANCE_UNDERFLOW ... </k>
         <account>
           <acctID> ACCTFROM </acctID>
           <balance> ORIGFROM </balance>
           ...
         </account>
      requires VALUE >Int ORIGFROM

```

### Invalid Operator

We use `INVALID` both for marking the designated invalid operator, and `UNDEFINED(_)` for garbage bytes in the input program.

```k
    syntax InvalidOp ::= "INVALID" | "UNDEFINED" "(" Int ")"
 // --------------------------------------------------------
    rule <k> INVALID      => #end EVMC_INVALID_INSTRUCTION   ... </k>
    rule <k> UNDEFINED(_) => #end EVMC_UNDEFINED_INSTRUCTION ... </k>
```

### Local Memory

These operations are getters/setters of the local execution memory.

```k
    syntax UnStackOp ::= "MLOAD"
 // ----------------------------
    rule <k> MLOAD INDEX => #asWord(#range(LM, INDEX, 32)) ~> #push ... </k>
         <localMem> LM </localMem>

    syntax BinStackOp ::= "MSTORE" | "MSTORE8"
 // ------------------------------------------
    rule <k> MSTORE INDEX VALUE => . ... </k>
         <localMem> LM => LM [ INDEX := #padToWidth(32, #asByteStack(VALUE)) ] </localMem>

    rule <k> MSTORE8 INDEX VALUE => . ... </k>
         <localMem> LM => LM [ INDEX := (VALUE modInt 256) ] </localMem>
```

### Expressions

Expression calculations are simple and don't require anything but the arguments from the `wordStack` to operate.

NOTE: We have to call the opcode `OR` by `EVMOR` instead, because K has trouble parsing it/compiling the definition otherwise.

```k
    syntax UnStackOp ::= "ISZERO" | "NOT"
 // -------------------------------------
    rule <k> ISZERO W => W ==Word 0 ~> #push ... </k>
    rule <k> NOT    W => ~Word W    ~> #push ... </k>

    syntax BinStackOp ::= "ADD" | "MUL" | "SUB" | "DIV" | "EXP" | "MOD"
 // -------------------------------------------------------------------
    rule <k> ADD W0 W1 => W0 +Word W1 ~> #push ... </k>
    rule <k> MUL W0 W1 => W0 *Word W1 ~> #push ... </k>
    rule <k> SUB W0 W1 => W0 -Word W1 ~> #push ... </k>
    rule <k> DIV W0 W1 => W0 /Word W1 ~> #push ... </k>
    rule <k> EXP W0 W1 => W0 ^Word W1 ~> #push ... </k>
    rule <k> MOD W0 W1 => W0 %Word W1 ~> #push ... </k>

    syntax BinStackOp ::= "SDIV" | "SMOD"
 // -------------------------------------
    rule <k> SDIV W0 W1 => W0 /sWord W1 ~> #push ... </k>
    rule <k> SMOD W0 W1 => W0 %sWord W1 ~> #push ... </k>

    syntax TernStackOp ::= "ADDMOD" | "MULMOD"
 // ------------------------------------------
    rule <k> ADDMOD W0 W1 W2 => (W0 +Int W1) %Word W2 ~> #push ... </k>
    rule <k> MULMOD W0 W1 W2 => (W0 *Int W1) %Word W2 ~> #push ... </k>

    syntax BinStackOp ::= "BYTE" | "SIGNEXTEND"
 // -------------------------------------------
    rule <k> BYTE INDEX W     => byte(INDEX, W)     ~> #push ... </k>
    rule <k> SIGNEXTEND W0 W1 => signextend(W0, W1) ~> #push ... </k>

    syntax BinStackOp ::= "SHL" | "SHR" | "SAR"
 // -------------------------------------------
    rule <k> SHL W0 W1 => W1 <<Word  W0 ~> #push ... </k>
    rule <k> SHR W0 W1 => W1 >>Word  W0 ~> #push ... </k>
    rule <k> SAR W0 W1 => W1 >>sWord W0 ~> #push ... </k>

    syntax BinStackOp ::= "AND" | "EVMOR" | "XOR"
 // ---------------------------------------------
    rule <k> AND   W0 W1 => W0 &Word W1   ~> #push ... </k>
    rule <k> EVMOR W0 W1 => W0 |Word W1   ~> #push ... </k>
    rule <k> XOR   W0 W1 => W0 xorWord W1 ~> #push ... </k>

    syntax BinStackOp ::= "LT" | "GT" | "EQ"
 // ----------------------------------------
    rule <k> LT W0 W1 => W0 <Word  W1 ~> #push ... </k>
    rule <k> GT W0 W1 => W0 >Word  W1 ~> #push ... </k>
    rule <k> EQ W0 W1 => W0 ==Word W1 ~> #push ... </k>

    syntax BinStackOp ::= "SLT" | "SGT"
 // -----------------------------------
    rule <k> SLT W0 W1 => W0 s<Word W1 ~> #push ... </k>
    rule <k> SGT W0 W1 => W1 s<Word W0 ~> #push ... </k>

    syntax BinStackOp ::= "SHA3"
 // ----------------------------
    rule <k> SHA3 MEMSTART MEMWIDTH => keccak(#range(LM, MEMSTART, MEMWIDTH)) ~> #push ... </k>
         <localMem> LM </localMem>
```

### Local State

These operators make queries about the current execution state.

```k
    syntax NullStackOp ::= "PC" | "GAS" | "GASPRICE" | "GASLIMIT" | "BASEFEE"
 // -------------------------------------------------------------------------
    rule <k> PC       => PCOUNT ~> #push ... </k> <pc> PCOUNT </pc>
    rule <k> GAS      => GAVAIL ~> #push ... </k> <gas> GAVAIL </gas>
    rule <k> GASPRICE => GPRICE ~> #push ... </k> <gasPrice> GPRICE </gasPrice>
    rule <k> GASLIMIT => GLIMIT ~> #push ... </k> <gasLimit> GLIMIT </gasLimit>
    rule <k> BASEFEE  => BFEE   ~> #push ... </k> <baseFee> BFEE </baseFee>

    syntax NullStackOp ::= "COINBASE" | "TIMESTAMP" | "NUMBER" | "DIFFICULTY"
 // -------------------------------------------------------------------------
    rule <k> COINBASE   => CB   ~> #push ... </k> <coinbase> CB </coinbase>
    rule <k> TIMESTAMP  => TS   ~> #push ... </k> <timestamp> TS </timestamp>
    rule <k> NUMBER     => NUMB ~> #push ... </k> <number> NUMB </number>
    rule <k> DIFFICULTY => DIFF ~> #push ... </k> <difficulty> DIFF </difficulty>

    syntax NullStackOp ::= "ADDRESS" | "ORIGIN" | "CALLER" | "CALLVALUE" | "CHAINID" | "SELFBALANCE"
 // ------------------------------------------------------------------------------------------------
    rule <k> ADDRESS     => ACCT ~> #push ... </k> <id> ACCT </id>
    rule <k> ORIGIN      => ORG  ~> #push ... </k> <origin> ORG </origin>
    rule <k> CALLER      => CL   ~> #push ... </k> <caller> CL </caller>
    rule <k> CALLVALUE   => CV   ~> #push ... </k> <callValue> CV </callValue>
    rule <k> CHAINID     => CID  ~> #push ... </k> <chainID> CID </chainID>
    rule <k> SELFBALANCE => BAL  ~> #push ... </k>
         <id> ACCT </id>
         <account>
            <acctID> ACCT </acctID>
            <balance> BAL </balance>
            ...
         </account>

    syntax NullStackOp ::= "MSIZE" | "CODESIZE"
 // -------------------------------------------
    rule <k> MSIZE    => 32 *Word MU         ~> #push ... </k> <memoryUsed> MU </memoryUsed>
    rule <k> CODESIZE => #sizeByteArray(PGM) ~> #push ... </k> <program> PGM </program>

    syntax TernStackOp ::= "CODECOPY"
 // ---------------------------------
    rule <k> CODECOPY MEMSTART PGMSTART WIDTH => . ... </k>
         <program> PGM </program>
         <localMem> LM => LM [ MEMSTART := PGM [ PGMSTART .. WIDTH ] ] </localMem>

    syntax UnStackOp ::= "BLOCKHASH"
 // --------------------------------
```

When running as a `node`, the blockhash will be retrieved from the running client.
Otherwise, it is calculated here using the "shortcut" formula used for running tests.

```{.k .standalone}
    rule <k> BLOCKHASH N => #blockhash(HASHES, N, HI -Int 1, 0) ~> #push ... </k>
         <number>      HI     </number>
         <blockhashes> HASHES </blockhashes>

    syntax Int ::= #blockhash ( List , Int , Int , Int ) [function]
 // ---------------------------------------------------------------
    rule #blockhash(_, N, HI, _) => 0 requires N >Int HI
    rule #blockhash(_, _, _, 256) => 0
    rule #blockhash(ListItem(0) _, _, _, _) => 0
    rule #blockhash(ListItem(H) _, N, N, _) => H
    rule #blockhash(ListItem(_) L, N, HI, A) => #blockhash(L, N, HI -Int 1, A +Int 1) [owise]
```

EVM OpCodes
-----------

### EVM Control Flow

The `JUMP*` family of operations affect the current program counter.

```k
    syntax NullStackOp ::= "JUMPDEST"
 // ---------------------------------
    rule <k> JUMPDEST => . ... </k>

    syntax UnStackOp ::= "JUMP"
 // ---------------------------
    rule <k> JUMP DEST => #endBasicBlock... </k>
         <pc> _ => DEST </pc>
         <jumpDests> DESTS </jumpDests>
      requires DEST in DESTS

    rule <k> JUMP DEST => #end EVMC_BAD_JUMP_DESTINATION ... </k>
         <jumpDests> DESTS </jumpDests>
      requires notBool DEST in DESTS

    syntax BinStackOp ::= "JUMPI"
 // -----------------------------
    rule <k> JUMPI _DEST I => . ... </k>
      requires I ==Int 0

    rule <k> JUMPI  DEST I => JUMP DEST ... </k>
      requires I =/=Int 0

    syntax InternalOp ::= "#endBasicBlock"
 // --------------------------------------
    rule <k> #endBasicBlock ~> (_:OpCode => .) ... </k>
    rule <k> (#endBasicBlock => .) ~> #execute ... </k>
```

### `STOP`, `REVERT`, and `RETURN`

```k
    syntax NullStackOp ::= "STOP"
 // -----------------------------
    rule <k> STOP => #end EVMC_SUCCESS ... </k>
         <output> _ => .ByteArray </output>

    syntax BinStackOp ::= "RETURN"
 // ------------------------------
    rule <k> RETURN RETSTART RETWIDTH => #end EVMC_SUCCESS ... </k>
         <output> _ => #range(LM, RETSTART, RETWIDTH) </output>
         <localMem> LM </localMem>

    syntax BinStackOp ::= "REVERT"
 // ------------------------------
    rule <k> REVERT RETSTART RETWIDTH => #end EVMC_REVERT ... </k>
         <output> _ => #range(LM, RETSTART, RETWIDTH) </output>
         <localMem> LM </localMem>
```

### Call Data

These operators query about the current `CALL*` state.

```k
    syntax NullStackOp ::= "CALLDATASIZE"
 // -------------------------------------
    rule <k> CALLDATASIZE => #sizeByteArray(CD) ~> #push ... </k>
         <callData> CD </callData>

    syntax UnStackOp ::= "CALLDATALOAD"
 // -----------------------------------
    rule <k> CALLDATALOAD DATASTART => #asWord(CD [ DATASTART .. 32 ]) ~> #push ... </k>
         <callData> CD </callData>

    syntax TernStackOp ::= "CALLDATACOPY"
 // -------------------------------------
    rule <k> CALLDATACOPY MEMSTART DATASTART DATAWIDTH => . ... </k>
         <localMem> LM => LM [ MEMSTART := CD [ DATASTART .. DATAWIDTH ] ] </localMem>
         <callData> CD </callData>
```

### Return Data

These operators query about the current return data buffer.

```k
    syntax NullStackOp ::= "RETURNDATASIZE"
 // ---------------------------------------
    rule <k> RETURNDATASIZE => #sizeByteArray(RD) ~> #push ... </k>
         <output> RD </output>

    syntax TernStackOp ::= "RETURNDATACOPY"
 // ----------------------------------------
    rule <k> RETURNDATACOPY MEMSTART DATASTART DATAWIDTH => . ... </k>
         <localMem> LM => LM [ MEMSTART := RD [ DATASTART .. DATAWIDTH ] ] </localMem>
         <output> RD </output>
      requires DATASTART +Int DATAWIDTH <=Int #sizeByteArray(RD)

    rule <k> RETURNDATACOPY _MEMSTART DATASTART DATAWIDTH => #end EVMC_INVALID_MEMORY_ACCESS ... </k>
         <output> RD </output>
      requires DATASTART +Int DATAWIDTH >Int #sizeByteArray(RD)
```

### Log Operations

```k
    syntax BinStackOp ::= LogOp
    syntax LogOp ::= LOG ( Int )
 // ----------------------------
    rule <k> LOG(N) MEMSTART MEMWIDTH => . ... </k>
         <id> ACCT </id>
         <wordStack> WS => #drop(N, WS) </wordStack>
         <localMem> LM </localMem>
         <log> ... (.List => ListItem({ ACCT | WordStack2List(#take(N, WS)) | #range(LM, MEMSTART, MEMWIDTH) })) </log>
      requires #sizeWordStack(WS) >=Int N
```

Ethereum Network OpCodes
------------------------

Operators that require access to the rest of the Ethereum network world-state can be taken as a first draft of a "blockchain generic" language.

### Account Queries

TODO: It's unclear what to do in the case of an account not existing for these operators.
`BALANCE` is specified to push 0 in this case, but the others are not specified.
For now, I assume that they instantiate an empty account and use the empty data.

```k
    syntax UnStackOp ::= "BALANCE"
 // ------------------------------
    rule <k> BALANCE ACCT => BAL ~> #push ... </k>
         <account>
           <acctID> ACCT </acctID>
           <balance> BAL </balance>
           ...
         </account>

    rule <k> BALANCE ACCT => 0 ~> #push ... </k>
         <activeAccounts> ACCTS </activeAccounts>
      requires notBool ACCT in ACCTS

    syntax UnStackOp ::= "EXTCODESIZE"
 // ----------------------------------
    rule <k> EXTCODESIZE ACCT => #sizeByteArray(CODE) ~> #push ... </k>
         <account>
           <acctID> ACCT </acctID>
           <code> CODE </code>
           ...
         </account>

    rule <k> EXTCODESIZE ACCT => 0 ~> #push ... </k>
         <activeAccounts> ACCTS </activeAccounts>
      requires notBool ACCT in ACCTS

    syntax UnStackOp ::= "EXTCODEHASH"
 // ----------------------------------
    rule <k> EXTCODEHASH ACCT => keccak(CODE) ~> #push ... </k>
         <account>
           <acctID> ACCT </acctID>
           <code> CODE:ByteArray </code>
           <nonce> NONCE </nonce>
           <balance> BAL </balance>
           ...
         </account>
      requires notBool #accountEmpty(CODE, NONCE, BAL)

     rule <k> EXTCODEHASH ACCT => 0 ~> #push ... </k>
         <account>
           <acctID> ACCT </acctID>
           <code> CODE </code>
           <nonce> NONCE </nonce>
           <balance> BAL </balance>
           ...
         </account>
       requires #accountEmpty(CODE, NONCE, BAL)

    rule <k> EXTCODEHASH ACCT => 0 ~> #push ... </k>
         <activeAccounts> ACCTS </activeAccounts>
      requires notBool ACCT in ACCTS
```

TODO: What should happen in the case that the account doesn't exist with `EXTCODECOPY`?
Should we pad zeros (for the copied "program")?

```k
    syntax QuadStackOp ::= "EXTCODECOPY"
 // ------------------------------------
    rule <k> EXTCODECOPY ACCT MEMSTART PGMSTART WIDTH => . ... </k>
         <localMem> LM => LM [ MEMSTART := PGM [ PGMSTART .. WIDTH ] ] </localMem>
         <account>
           <acctID> ACCT </acctID>
           <code> PGM </code>
           ...
         </account>

    rule <k> EXTCODECOPY ACCT _MEMSTART _PGMSTART _WIDTH => . ... </k>
         <activeAccounts> ACCTS </activeAccounts>
      requires notBool ACCT in ACCTS
```

### Account Storage Operations

These rules reach into the network state and load/store from account storage:

```k
    syntax UnStackOp ::= "SLOAD"
 // ----------------------------
    rule <k> SLOAD INDEX => #lookup(STORAGE, INDEX) ~> #push ... </k>
         <id> ACCT </id>
         <account>
           <acctID> ACCT </acctID>
           <storage> STORAGE </storage>
           ...
         </account>

    syntax BinStackOp ::= "SSTORE"
 // ------------------------------
    rule <k> SSTORE INDEX NEW => . ... </k>
         <id> ACCT </id>
         <account>
           <acctID> ACCT </acctID>
           <storage> STORAGE => STORAGE [ INDEX <- NEW ] </storage>
           ...
         </account>
```

### Call Operations

The various `CALL*` (and other inter-contract control flow) operations will be desugared into these `InternalOp`s.

-   The `callLog` is used to store the `CALL*`/`CREATE` operations so that we can compare them against the test-set.

-   `#call_____` takes the calling account, the account to execute as, the account whose code should execute, the gas limit, the amount to transfer, the arguments, and the static flag.
-   `#callWithCode______` takes the calling account, the accout to execute as, the code to execute (as a bytearray), the gas limit, the amount to transfer, the arguments, and the static flag.
-   `#return__` is a placeholder for the calling program, specifying where to place the returned data in memory.

```k
    syntax InternalOp ::= "#checkCall" Int Int
                        | "#call"         Int Int Int Int Int ByteArray Bool
                        | "#callWithCode" Int Int Int ByteArray Int Int ByteArray Bool
                        | "#mkCall"       Int Int Int ByteArray     Int ByteArray Bool
 // ----------------------------------------------------------------------------------
    rule <k> #checkCall ACCT VALUE
          => #refund GCALL ~> #pushCallStack ~> #pushWorldState
          ~> #end #if VALUE >Int BAL #then EVMC_BALANCE_UNDERFLOW #else EVMC_CALL_DEPTH_EXCEEDED #fi
         ...
         </k>
         <callDepth> CD </callDepth>
         <output> _ => .ByteArray </output>
         <account>
           <acctID> ACCT </acctID>
           <balance> BAL </balance>
           ...
         </account>
         <callGas> GCALL </callGas>
      requires VALUE >Int BAL orBool CD >=Int 1024

     rule <k> #checkCall ACCT VALUE => . ... </k>
         <callDepth> CD </callDepth>
         <account>
           <acctID> ACCT </acctID>
           <balance> BAL </balance>
           ...
         </account>
      requires notBool (VALUE >Int BAL orBool CD >=Int 1024)

    rule <k> #call ACCTFROM ACCTTO ACCTCODE VALUE APPVALUE ARGS STATIC
          => #callWithCode ACCTFROM ACCTTO ACCTCODE CODE VALUE APPVALUE ARGS STATIC
         ...
         </k>
         <account>
           <acctID> ACCTCODE </acctID>
           <code> CODE </code>
           ...
         </account>

    rule <k> #call ACCTFROM ACCTTO ACCTCODE VALUE APPVALUE ARGS STATIC
          => #callWithCode ACCTFROM ACCTTO ACCTCODE .ByteArray VALUE APPVALUE ARGS STATIC
         ...
         </k>
         <activeAccounts> ACCTS </activeAccounts>
      requires notBool ACCTCODE in ACCTS

    rule <k> #callWithCode ACCTFROM ACCTTO ACCTCODE BYTES VALUE APPVALUE ARGS STATIC
          => #pushCallStack ~> #pushWorldState
          ~> #transferFunds ACCTFROM ACCTTO VALUE
          ~> #mkCall ACCTFROM ACCTTO ACCTCODE BYTES APPVALUE ARGS STATIC
         ...
         </k>

    rule <k> #mkCall ACCTFROM ACCTTO ACCTCODE BYTES APPVALUE ARGS STATIC:Bool
          => #touchAccounts ACCTFROM ACCTTO ~> #accessAccounts ACCTFROM ACCTTO ~> #loadProgram BYTES ~> #initVM ~> #precompiled?(ACCTCODE, SCHED) ~> #execute
         ...
         </k>
         <callDepth> CD => CD +Int 1 </callDepth>
         <callData> _ => ARGS </callData>
         <callValue> _ => APPVALUE </callValue>
         <id> _ => ACCTTO </id>
         <gas> _ => GCALL </gas>
         <callGas> GCALL => 0 </callGas>
         <caller> _ => ACCTFROM </caller>
         <static> OLDSTATIC:Bool => OLDSTATIC orBool STATIC </static>
         <schedule> SCHED </schedule>

    syntax InternalOp ::= "#precompiled?" "(" Int "," Schedule ")"
 // --------------------------------------------------------------
    rule <k> #precompiled?(ACCTCODE, SCHED) => #next [ #precompiled(ACCTCODE) ] ... </k> requires         #isPrecompiledAccount(ACCTCODE, SCHED)
    rule <k> #precompiled?(ACCTCODE, SCHED) => .                                ... </k> requires notBool #isPrecompiledAccount(ACCTCODE, SCHED)

    syntax Bool ::= #isPrecompiledAccount ( Int , Schedule ) [function, functional, smtlib(isPrecompiledAccount)]
 // -------------------------------------------------------------------------------------------------------------
    rule [isPrecompiledAccount.true]:  #isPrecompiledAccount(ACCTCODE, SCHED) => true  requires         ACCTCODE in #precompiledAccounts(SCHED)
    rule [isPrecompiledAccount.false]: #isPrecompiledAccount(ACCTCODE, SCHED) => false requires notBool ACCTCODE in #precompiledAccounts(SCHED)

    syntax KItem ::= "#initVM"
 // --------------------------
    rule <k> #initVM      => . ...      </k>
         <pc>           _ => 0          </pc>
         <memoryUsed>   _ => 0          </memoryUsed>
         <output>       _ => .ByteArray </output>
         <wordStack>    _ => .WordStack </wordStack>
         <localMem>     _ => .Memory    </localMem>

    syntax KItem ::= "#loadProgram" ByteArray
 // -----------------------------------------
    rule <k> #loadProgram BYTES => . ... </k>
         <program> _ => BYTES </program>
         <jumpDests> _ => #computeValidJumpDests(BYTES) </jumpDests>

    syntax KItem ::= "#touchAccounts" Account | "#touchAccounts" Account Account
 // ----------------------------------------------------------------------------
    rule <k> #touchAccounts ADDR1 ADDR2 => #touchAccounts ADDR1 ~> #touchAccounts ADDR2 ... </k>

    rule <k> #touchAccounts ADDR => . ... </k>
         <touchedAccounts> TOUCHED_ACCOUNTS => TOUCHED_ACCOUNTS |Set SetItem(ADDR) </touchedAccounts>

    syntax KItem ::= "#accessStorage" Account Int
 // --------------------------------------------
    rule <k> #accessStorage ACCT INDEX => . ... </k>
         <accessedStorage> ... ACCT |-> (TS:Set => TS |Set SetItem(INDEX)) ... </accessedStorage>
    rule <k> #accessStorage ACCT INDEX => . ... </k>
         <accessedStorage> TS => TS[ACCT <- SetItem(INDEX)] </accessedStorage>
      requires notBool ACCT in_keys(TS)

    syntax KItem ::= "#accessAccounts" Account
                   | "#accessAccounts" Set
                   | "#accessAccounts" Account Account
                   | "#accessAccounts" Account Account Set
 // -----------------------------------------------------
    rule <k> #accessAccounts ADDR1:Account ADDR2:Account ADDRSET:Set => #accessAccounts ADDR1 ~> #accessAccounts ADDR2 ~> #accessAccounts ADDRSET ... </k>

    rule <k> #accessAccounts ADDR1:Account ADDR2:Account => #accessAccounts ADDR1 ~> #accessAccounts ADDR2 ... </k>

    rule <k> #accessAccounts ADDR:Account => . ... </k>
         <accessedAccounts> TOUCHED_ACCOUNTS => TOUCHED_ACCOUNTS |Set SetItem(ADDR) </accessedAccounts>

    rule <k> #accessAccounts ADDRSET:Set => . ... </k>
         <accessedAccounts> TOUCHED_ACCOUNTS => TOUCHED_ACCOUNTS |Set ADDRSET </accessedAccounts>

    syntax Set ::= #computeValidJumpDests(ByteArray)            [function, memo]
                 | #computeValidJumpDests(ByteArray, Int, List) [function, klabel(#computeValidJumpDestsAux)]
 // ---------------------------------------------------------------------------------------------------------
    rule #computeValidJumpDests(PGM) => #computeValidJumpDests(PGM, 0, .List)
```

```{.k .nobytes}
    rule #computeValidJumpDests(.WordStack, _, RESULT) => List2Set(RESULT)
    rule #computeValidJumpDests(91 : WS   , I, RESULT) => #computeValidJumpDests(WS                            , I +Int 1              , ListItem(I) RESULT)
    rule #computeValidJumpDests( W : WS   , I, RESULT) => #computeValidJumpDests(#drop(#widthOpCode(W), W : WS), I +Int #widthOpCode(W),             RESULT) requires W =/=Int 91
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
    rule <statusCode> _:ExceptionalStatusCode </statusCode>
         <k> #halt ~> #return _ _
          => #popCallStack ~> #popWorldState ~> 0 ~> #push
         ...
         </k>
         <output> _ => .ByteArray </output>

    rule <statusCode> EVMC_REVERT </statusCode>
         <k> #halt ~> #return RETSTART RETWIDTH
          => #popCallStack ~> #popWorldState
          ~> 0 ~> #push ~> #refund GAVAIL ~> #setLocalMem RETSTART RETWIDTH OUT
         ...
         </k>
         <output> OUT </output>
         <gas> GAVAIL </gas>

    rule <statusCode> EVMC_SUCCESS </statusCode>
         <k> #halt ~> #return RETSTART RETWIDTH
          => #popCallStack ~> #dropWorldState
          ~> 1 ~> #push ~> #refund GAVAIL ~> #setLocalMem RETSTART RETWIDTH OUT
         ...
         </k>
         <output> OUT </output>
         <gas> GAVAIL </gas>

    syntax InternalOp ::= "#refund" Exp [strict]
                        | "#setLocalMem" Int Int ByteArray
 // ------------------------------------------------------
    rule [refund]: <k> #refund G:Int => . ... </k> <gas> GAVAIL => GAVAIL +Int G </gas>

    rule <k> #setLocalMem START WIDTH WS => . ... </k>
         <localMem> LM => LM [ START := WS [ 0 .. minInt(WIDTH, #sizeByteArray(WS)) ] ] </localMem>
```

Ethereum Network OpCodes
------------------------

### Account Creation/Deletion

-   `#create____` transfers the endowment to the new account and triggers the execution of the initialization code.
-   `#codeDeposit_` checks the result of initialization code and whether the code deposit can be paid, indicating an error if not.
-   `#isValidCode_` checks if the code returned by the execution of the initialization code begins with a reserved byte. [EIP-3541]

```k
    syntax InternalOp ::= "#create"   Int Int Int ByteArray
                        | "#mkCreate" Int Int Int ByteArray
                        | "#incrementNonce" Int
 // -------------------------------------------
    rule <k> #create ACCTFROM ACCTTO VALUE INITCODE
          => #incrementNonce ACCTFROM
          ~> #pushCallStack ~> #pushWorldState
          ~> #newAccount ACCTTO
          ~> #transferFunds ACCTFROM ACCTTO VALUE
          ~> #mkCreate ACCTFROM ACCTTO VALUE INITCODE
         ...
         </k>

    rule <k> #incrementNonce ACCT => . ... </k>
         <account>
           <acctID> ACCT </acctID>
           <nonce> NONCE => NONCE +Int 1 </nonce>
           ...
         </account>

    syntax Bool ::= #isValidCode ( ByteArray , Schedule ) [function]
 // ----------------------------------------------------------------

    syntax KItem ::= "#codeDeposit" Int
                   | "#mkCodeDeposit" Int
                   | "#finishCodeDeposit" Int ByteArray
 // --------------------------------------------------
```

`CREATE` will attempt to `#create` the account using the initialization code and cleans up the result with `#codeDeposit`.

```k
    syntax TernStackOp ::= "CREATE"
 // -------------------------------
    rule <k> CREATE VALUE MEMSTART MEMWIDTH
          => #accessAccounts #newAddr(ACCT, NONCE)
          ~> #checkCall ACCT VALUE
          ~> #create ACCT #newAddr(ACCT, NONCE) VALUE #range(LM, MEMSTART, MEMWIDTH)
          ~> #codeDeposit #newAddr(ACCT, NONCE)
         ...
         </k>
         <id> ACCT </id>
         <localMem> LM </localMem>
         <account>
           <acctID> ACCT </acctID>
           <nonce> NONCE </nonce>
           ...
         </account>
```

`CREATE2` will attempt to `#create` the account, but with the new scheme for choosing the account address.

```k
    syntax QuadStackOp ::= "CREATE2"
 // --------------------------------
    rule <k> CREATE2 VALUE MEMSTART MEMWIDTH SALT
          => #accessAccounts #newAddr(ACCT, SALT, #range(LM, MEMSTART, MEMWIDTH))
          ~> #checkCall ACCT VALUE
          ~> #create ACCT #newAddr(ACCT, SALT, #range(LM, MEMSTART, MEMWIDTH)) VALUE #range(LM, MEMSTART, MEMWIDTH)
          ~> #codeDeposit #newAddr(ACCT, SALT, #range(LM, MEMSTART, MEMWIDTH))
         ...
         </k>
         <id> ACCT </id>
         <localMem> LM </localMem>
```

`SELFDESTRUCT` marks the current account for deletion and transfers funds out of the current account.
Self destructing to yourself, unlike a regular transfer, destroys the balance in the account, irreparably losing it.

```k
    syntax UnStackOp ::= "SELFDESTRUCT"
 // -----------------------------------
    rule <k> SELFDESTRUCT ACCTTO => #touchAccounts ACCT ACCTTO ~> #transferFunds ACCT ACCTTO BALFROM ~> #end EVMC_SUCCESS ... </k>
         <id> ACCT </id>
         <selfDestruct> SDS => SDS |Set SetItem(ACCT) </selfDestruct>
         <account>
           <acctID> ACCT </acctID>
           <balance> BALFROM </balance>
           ...
         </account>
         <output> _ => .ByteArray </output>
      requires ACCT =/=Int ACCTTO

    rule <k> SELFDESTRUCT ACCT => #touchAccounts ACCT ~> #end EVMC_SUCCESS ... </k>
         <id> ACCT </id>
         <selfDestruct> SDS => SDS |Set SetItem(ACCT) </selfDestruct>
         <account>
           <acctID> ACCT </acctID>
           <balance> _ => 0 </balance>
           ...
         </account>
         <output> _ => .ByteArray </output>
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
    syntax BExp ::= #accountNonexistent ( Int )
 // -------------------------------------------
    rule <k> #accountNonexistent(ACCT) => true ... </k>
         <activeAccounts> ACCTS </activeAccounts>
      requires notBool ACCT in ACCTS

    syntax Bool ::= #accountEmpty ( AccountCode , Int , Int ) [function, klabel(accountEmpty), symbol]
 // --------------------------------------------------------------------------------------------------
    rule #accountEmpty(CODE, NONCE, BAL) => CODE ==K .ByteArray andBool NONCE ==Int 0 andBool BAL ==Int 0

    syntax Int ::= #allBut64th ( Int ) [function, functional, smtlib(gas_allBut64th)]
 // ---------------------------------------------------------------------------------
    rule [allBut64th.pos]: #allBut64th(N) => N -Int (N /Int 64) requires 0 <=Int N
    rule [allBut64th.neg]: #allBut64th(N) => 0                  requires N  <Int 0
```

```k
    syntax Int ::= "G*" "(" Int "," Int "," Int "," Schedule ")" [function]
 // -----------------------------------------------------------------------

    syntax Int ::= #multComplexity(Int)    [function]
                 | #newMultComplexity(Int) [function]
 // -------------------------------------------------
    rule #multComplexity(X) => X *Int X                                     requires X <=Int 64
    rule #multComplexity(X) => X *Int X /Int 4 +Int 96 *Int X -Int 3072     requires X >Int 64 andBool X <=Int 1024
    rule #multComplexity(X) => X *Int X /Int 16 +Int 480 *Int X -Int 199680 requires X >Int 1024

    rule #newMultComplexity(X) => (X up/Int 8) ^Int 2

    syntax Int ::= #adjustedExpLength(Int, Int, ByteArray) [function]
                 | #adjustedExpLength(Int)                 [function, klabel(#adjustedExpLengthAux)]
 // ------------------------------------------------------------------------------------------------
    rule #adjustedExpLength(BASELEN, EXPLEN, DATA) => #if EXPLEN <=Int 32 #then 0 #else 8 *Int (EXPLEN -Int 32) #fi +Int #adjustedExpLength(#asInteger(DATA [ 96 +Int BASELEN .. minInt(EXPLEN, 32) ]))

    rule #adjustedExpLength(0) => 0
    rule #adjustedExpLength(1) => 0
    rule #adjustedExpLength(N) => 1 +Int #adjustedExpLength(N /Int 2) requires N >Int 1
```

### Default Schedule

```k
    syntax Schedule ::= "DEFAULT" [klabel(DEFAULT_EVM), symbol, smtlib(schedule_DEFAULT)]
 // -------------------------------------------------------------------------------------
```

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
