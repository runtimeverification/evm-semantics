EVM Execution
=============

The EVM is a stack machine over some simple opcodes.
Most of the opcodes are "local" to the execution state of the machine, but some of them must interact with the world state.
This file only defines the local execution operations, the file `ethereum.md` will define the interactions with the world state.

Configuration
-------------

The configuration has cells for the current account id, the current opcode, the program counter, the current gas, the gas price, the current program, the word stack, and the local memory.
In addition, there are cells for the callstack and execution substate.

We've broken up the configuration into two components; those parts of the state that mutate during execution of a single transaction and those that are static throughout.
In the comments next to each cell, we've marked which component of the yellowpaper state corresponds to each cell.

TODO: The value \mu_i is not being accounted for (memory consumption gas tracker?).

```k
requires "data.k"

module ETHEREUM
    imports EVM-DATA
    imports KCELLS

    configuration <ethereum>

                    // EVM Specific
                    // ============

                    <evm>

                      // Mutable during a single transaction
                      // -----------------------------------

                      <callStack> .CallStack </callStack>
                      <op> .K </op>
                      <txExecState>
                        <program>   .Map        </program>              // I_b

                        // I_*
                        <id>        0:Word     </id>                    // I_a
                        <caller>    0:Word     </caller>                // I_s
                        <callData>  .WordStack </callData>              // I_d
                        <callValue> 0:Word     </callValue>             // I_v

                        // \mu_*
                        <wordStack> .WordStack </wordStack>             // \mu_s
                        <localMem>  .Map       </localMem>              // \mu_m
                        <pc>        0:Word     </pc>                    // \mu_pc
                        <gas>       0:Word     </gas>                   // \mu_g
                      </txExecState>

                      // A_* (execution substate)
                      <substate>
                        <selfDestruct> .Set         </selfDestruct>     // A_s
                        <log>          .SubstateLog </log>              // A_l
                        <refund>       0:Word       </refund>           // A_r
                      </substate>

                      // Immutable during a single transaction
                      // -------------------------------------

                      <gasPrice>   0:Word     </gasPrice>               // I_p
                      <origin>     0:Word     </origin>                 // I_o

                      // I_H* (block information)
                      <gasLimit>   0:Word </gasLimit>                   // I_Hl
                      <coinbase>   0:Word </coinbase>                   // I_Hc
                      <timestamp>  0:Word </timestamp>                  // I_Hs
                      <number>     0:Word </number>                     // I_Hi
                      <difficulty> 0:Word </difficulty>                 // I_Hd

                      // Testing Information
                      // -------------------

                      <testInfo>
                        <currOps> .Set </currOps>
                        <prevOps> .Set </prevOps>
                      </testInfo>

                    </evm>

                    // Ethereum Network
                    // ================

                    <network>

                      // Accounts Record
                      // ---------------

                      <activeAccounts> .Set </activeAccounts>

                      <accounts>
                        <account multiplicity="*">
                          <acctID>  .AcctID </acctID>
                          <balance> .Value  </balance>
                          <code>    .Code   </code>
                          <storage> .Map    </storage>
                          <acctMap> .Map    </acctMap>
                        </account>
                      </accounts>

                      // Transactions Record
                      // -------------------

                      <messages>
                        <message multiplicity="*">
                          <msgID>  .MsgID   </msgID>
                          <to>     .AcctID  </to>
                          <from>   .AcctID  </from>
                          <amount> .Value   </amount>
                          <data>   .Map     </data>
                        </message>
                      </messages>

                    </network>

                  </ethereum>

    syntax AcctID ::= Word | ".AcctID"
    syntax Code   ::= Map  | ".Code"
    syntax MsgID  ::= Word | ".MsgID"
    syntax Value  ::= Word | ".Value"
```

Machine Plumbing
----------------

When the `op` cell becomes empty, it's time to load the next opcode.
The gas needed is calculated first (by putting `#gas(_)` at the front of the `op` cell).

Note that we must treat loading of `PUSH` specially, given that the arguments of `PUSH` are inline with the code itself.
Given the several special treatments of `PUSH`, the usefulness of this design for EVM becomes dubious.

```k
    syntax InternalOp ::= "#next"
 // -----------------------------
    rule <op> #next => #gas(OP) ~> #checkGas ~> OP ~> #next ... </op>
         <pc> PCOUNT => PCOUNT +Word 1 </pc>
         <program> ... PCOUNT |-> OP:OpCode ... </program>
         <currOps> ... (.Set => SetItem(OP)) </currOps>
      requires notBool isPushOp(OP)

    rule <op> #next => #gas(PUSH(N, W)) ~> #checkGas ~> PUSH(N, W) ~> #next ... </op>
         <pc> PCOUNT => PCOUNT +Word (1 +Word N) </pc>
         <program> ... PCOUNT |-> PUSH(N, W) ... </program>
         <currOps> ... (.Set => SetItem(PUSH(N, W))) </currOps>

    syntax InternalOp ::= "#endOfProgram"
 // -------------------------------------
    rule <op> #next => #endOfProgram ... </op>
         <pc> PCOUNT </pc>
         <program> CODE </program>
      requires notBool (PCOUNT in keys(CODE))
```

Depending on the sort of the opcode loaded, the correct number of arguments are loaded off the `wordStack`.
This allows more "local" definition of each of the corresponding operators.

```k
    syntax OpCode ::= NullStackOp | UnStackOp | BinStackOp | TernStackOp | QuadStackOp
                    | StackOp | InternalOp | CallOp | PushOp | LogOp
 // ----------------------------------------------------------------

    syntax KItem ::= OpCode
                   | UnStackOp Word
                   | BinStackOp Word Word
                   | TernStackOp Word Word Word
                   | QuadStackOp Word Word Word Word
 // ------------------------------------------------
    rule <op> UOP:UnStackOP   => #stackUnderflow ... </op> <wordStack> WS </wordStack> requires #size(WS) <Int 1
    rule <op> BOP:BinStackOp  => #stackUnderflow ... </op> <wordStack> WS </wordStack> requires #size(WS) <Int 2
    rule <op> TOP:TernStackOP => #stackUnderflow ... </op> <wordStack> WS </wordStack> requires #size(WS) <Int 3
    rule <op> QOP:QuadStackOP => #stackUnderflow ... </op> <wordStack> WS </wordStack> requires #size(WS) <Int 4

    rule <op> UOP:UnStackOp   => UOP W0          ... </op> <wordStack> W0 : WS                => WS </wordStack>
    rule <op> BOP:BinStackOp  => BOP W0 W1       ... </op> <wordStack> W0 : W1 : WS           => WS </wordStack>
    rule <op> TOP:TernStackOp => TOP W0 W1 W2    ... </op> <wordStack> W0 : W1 : W2 : WS      => WS </wordStack>
    rule <op> QOP:QuadStackOp => QOP W0 W1 W2 W3 ... </op> <wordStack> W0 : W1 : W2 : W3 : WS => WS </wordStack>

    syntax KItem ::= CallOp Word Word Word Word Word Word Word
                   | "DELEGATECALL" Word Word Word Word Word Word
 // -------------------------------------------------------------
    rule <op> DELEGATECALL => #stackUnderflow ... </op> <wordStack> WS </wordStack> requires #size(WS) <Int 6
    rule <op> CO:CallOp    => #stackUnderflow ... </op> <wordStack> WS </wordStack> requires #size(WS) <Int 7

    rule <op> DELEGATECALL => DELEGATECALL W0 W1 W2 W3 W4 W5    ... </op> <wordStack> W0 : W1 : W2 : W3 : W4 : W5 : WS      => WS </wordStack>
    rule <op> CO:CallOp    => CO           W0 W1 W2 W3 W4 W5 W6 ... </op> <wordStack> W0 : W1 : W2 : W3 : W4 : W5 : W6 : WS => WS </wordStack>
      requires CO =/=K DELEGATECALL

    syntax KItem ::= StackOp WordStack
 // ----------------------------------
    rule <op> SO:StackOp => SO WS ... </op> <wordStack> WS </wordStack>

    syntax KItem ::= Exception
 // --------------------------
```

Testing Information
-------------------

We need to keep track of some information for making debugging the semantics easier.
This won't be needed once we are passing tests, but helps us get there.

The cell `currOps` stores the operators we've seen during this execution, and `prevOps` store operators we've seen throughout this `krun`.
This well help us determine which operators are new in this run so that we can get an idea of how the test failed.
We don't care about keeping multiple versions of each parametric operator around though, so here we get rid of duplicates.

```k
    rule <currOps> ... SetItem(LOG(_))     (SetItem(LOG(_))     => .Set) </currOps>
    rule <currOps> ... SetItem(DUP(_))     (SetItem(DUP(_))     => .Set) </currOps>
    rule <currOps> ... SetItem(SWAP(_))    (SetItem(SWAP(_))    => .Set) </currOps>
    rule <currOps> ... SetItem(PUSH(_, _)) (SetItem(PUSH(_, _)) => .Set) </currOps>

    rule <prevOps> ... SetItem(LOG(_))     (SetItem(LOG(_))     => .Set) </prevOps>
    rule <prevOps> ... SetItem(DUP(_))     (SetItem(DUP(_))     => .Set) </prevOps>
    rule <prevOps> ... SetItem(SWAP(_))    (SetItem(SWAP(_))    => .Set) </prevOps>
    rule <prevOps> ... SetItem(PUSH(_, _)) (SetItem(PUSH(_, _)) => .Set) </prevOps>
```

EVM Programs
------------

Lists of opcodes form programs.
Deciding if an opcode is in a list will be useful for modeling gas, and converting a program into a map of program-counter to opcode is useful for execution.

Note that `_in_` ignores the arguments to operators that are parametric.

```k
    syntax OpCodes ::= ".OpCodes" | OpCode ";" OpCodes
 // --------------------------------------------------

    syntax Bool ::= OpCode "in" OpCodes [function]
 // ----------------------------------------------
    rule OP         in .OpCodes            => false
    rule OP         in (OP' ; OPS)         => (OP ==K OP') orElseBool (OP in OPS) requires notBool (isStackOp(OP) orBool isPushOp(OP) orBool isLogOp(OP))
    rule LOG(_)     in (LOG(_) ; OPS)      => true
    rule DUP(_)     in (DUP(_) ; OPS)      => true
    rule SWAP(_)    in (SWAP(_) ; OPS)     => true
    rule PUSH(_, _) in (PUSH(_, _) ; OPS)  => true

    syntax Map ::= #asMap ( OpCodes )       [function]
                 | #asMap ( Int , OpCodes ) [function]
 // --------------------------------------------------
    rule #asMap( OPS:OpCodes )         => #asMap(0, OPS)
    rule #asMap( N , .OpCodes )        => .Map
    rule #asMap( N , OP:OpCode ; OCS ) => (N |-> OP) #asMap(N +Int 1, OCS) requires notBool isPushOp(OP)
    rule #asMap( N , PUSH(M, W) ; OCS) => (N |-> PUSH(M, W)) #asMap(N +Int 1 +Int M, OCS)

    syntax OpCodes ::= #asOpCodes ( Map )       [function]
                     | #asOpCodes ( Int , Map ) [function]
 // ------------------------------------------------------
    rule #asOpCodes(M) => #asOpCodes(0, M)
    rule #asOpCodes(N, .Map) => .OpCodes
    rule #asOpCodes(N, N |-> OP         M) => OP         ; #asOpCodes(N +Int 1,        M) requires notBool isPushOp(OP)
    rule #asOpCodes(N, N |-> PUSH(S, W) M) => PUSH(S, W) ; #asOpCodes(N +Int 1 +Int S, M)
```

EVM Opcodes
===========

Each subsection has a different class of opcodes.
Organization is based roughly on what parts of the execution state are needed to compute the result of each operator.
This sometimes corresponds to the organization in the yellowpaper.

Implementations immediately follow declarations, so if an operator is declared here but not implemented then it isn't implemented at all.

Internal Operations
-------------------

These are just used by the other operators for shuffling local execution state around on the EVM.

-   `#push` will push an element to the `wordStack` without any checks.
-   `#setStack_` will set the current stack to the given one.

```k
    syntax InternalOp ::= "#push" | "#setStack" WordStack
 // -----------------------------------------------------
    rule <op> W0:Word ~> #push => . ... </op> <wordStack> WS => W0 : WS </wordStack>
    rule <op> #setStack WS     => . ... </op> <wordStack> _  => WS      </wordStack>
```

-   `#checkStackSize` will ensure that there hasn't been a stack overflow.
-   `#stackOverflow`/`#stackUnderflow` signals that there has been a stack over/under-flow.

```k
    syntax Exception  ::= "#stackOverflow" | "#stackUnderflow"
    syntax InternalOp ::= "#checkStackSize"
 // ---------------------------------------
    rule <op> #checkStackSize => #size(WS) ~> #checkStackSize ... </op> <wordStack> WS </wordStack>
    rule <op> I:Int ~> #checkStackSize => .              ... </op> requires I <Int  1024
    rule <op> I:Int ~> #checkStackSize => #stackOverflow ... </op> requires I >=Int 1024
```

Previous process states must be stored, so a tuple of sort `Process` is supplied for that.
The `CallStack` is a cons-list of `Process`.

-   `#pushCallStack` stores the current state on the `callStack`.
-   `#popCallStack` replaces the current state with the top of the `callStack`.

```k
    syntax CallStack ::= ".CallStack" | Bag CallStack
 // -------------------------------------------------

    syntax Int ::= #size ( CallStack ) [function]
 // ---------------------------------------------
    rule #size( .CallStack         ) => 0
    rule #size( B:Bag CS:CallStack ) => 1 +Int #size(CS)

    syntax InternalOp ::= "#pushCallStack" | "#popCallStack"
 // --------------------------------------------------------
    rule <op> #pushCallStack => . </op>
         <callStack> CS => TXSTATE CS </callStack>
         <txExecState> TXSTATE </txExecState>

    rule <op> #popCallStack => . </op>
         <callStack> TXSTATE CS => CS </callStack>
         <txExecState> _ => TXSTATE </txExecState>
```

Adding Accounts
---------------

```k
    syntax Exception  ::= "#badAccount"
    syntax InternalOp ::= "#newAccount" Word
 // ----------------------------------------
    rule <op> #newAccount ACCT => . ... </op>
         <activeAccounts> ACCTS </activeAccounts>
      requires #addr(ACCT) in ACCTS

    rule <op> #newAccount ACCT => . ... </op>
         <activeAccounts> ACCTS (.Set => SetItem(#addr(ACCT))) </activeAccounts>
         <accounts>
           ( .Bag
          => <account>
               <acctID>  #addr(ACCT)   </acctID>
               <balance> 0             </balance>
               <code>    .Map          </code>
               <storage> .Map          </storage>
               <acctMap> "nonce" |-> 0 </acctMap>
             </account>
           )
           ...
         </accounts>
      requires notBool #addr(ACCT) in ACCTS
```

EVM Substate Log
----------------

During execution of a transaction some things are recorded in the substate log.
This is a right cons-list of `SubstateLogEntry` (which contains the account ID along with the specified portions of the `wordStack` and `localMem`).

```k
    syntax SubstateLog      ::= ".SubstateLog" | SubstateLog "." SubstateLogEntry
    syntax SubstateLogEntry ::= "{" Word "|" WordStack "|" WordStack "}"
```

After executing a transaction, it's necessary to have the effect of the substate log recorded.

-   `#finalize` makes the substate log actually have an effect on the state.

```k
    syntax InternalOp ::= "#finalize"
 // ---------------------------------
    rule <op> #finalize => . ... </op>
         <selfDestruct> .Set </selfDestruct>
         <refund>       0    </refund>

    rule <op> #finalize ... </op>
         <id> ACCT </id>
         <refund> BAL => 0 </refund>
         <account>
           <acctID> ACCT </acctID>
           <balance> CURRBAL => CURRBAL +Word BAL </balance>
           ...
         </account>
      requires BAL =/=K 0

    rule <op> #finalize ... </op>
         <selfDestruct> ... (SetItem(ACCT) => .Set) </selfDestruct>
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
```

Stack Manipulations
-------------------

Some operators don't calculate anything, they just push the stack around a bit.

```k
    syntax UnStackOp ::= "POP"
 // --------------------------
    rule <op> POP W => . ... </op>

    syntax StackOp ::= DUP ( Word ) | SWAP ( Word )
 // -----------------------------------------------
    rule <op> DUP(N)  WS => #stackUnderflow ... </op> requires #size(WS) <Int N
    rule <op> SWAP(N) WS => #stackUnderflow ... </op> requires #size(WS) <=Int N

    rule <op> DUP(N)  WS:WordStack => #setStack ((WS [ N -Word 1 ]) : WS) ~> #checkStackSize    ... </op>
    rule <op> SWAP(N) (W0 : WS)    => #setStack ((WS [ N -Word 1 ]) : (WS [ N -Word 1 := W0 ])) ... </op>

    syntax PushOp ::= PUSH ( Word , Word )
 // --------------------------------------
    rule <op> PUSH(_, W) => W ~> #push ~> #checkStackSize ... </op>
```

Local Memory
------------

These operations are getters/setters of the local execution memory.

TODO: Calculate \mu_i.

```k
    syntax UnStackOp  ::= "MLOAD"
    syntax BinStackOp ::= "MSTORE"
                        | "MSTORE8"
 // ------------------------------
    rule <op> MLOAD   INDEX       => VALUE ~> #push ... </op> <localMem> ... INDEX |-> VALUE ...  </localMem>
    rule <op> MSTORE  INDEX VALUE => .              ... </op> <localMem> LM => LM [ INDEX <- VALUE ] </localMem>
    rule <op> MSTORE8 INDEX VALUE => .              ... </op> <localMem> LM => LM [ INDEX <- (VALUE %Int 256) ] </localMem>
```

Expressions
-----------

Expression calculations are simple and don't require anything but the arguments from the `wordStack` to operate.

NOTE: We have to call the opcode `OR` by `EVMOR` instead, because K has trouble parsing it/compiling the definition otherwise.

```k
    syntax UnStackOp ::= "ISZERO" | "NOT"
 // -------------------------------------
    rule <op> ISZERO 0 => bool2Word(true)  ~> #push ... </op>
    rule <op> ISZERO W => bool2Word(false) ~> #push ... </op> requires W =/=K 0
    rule <op> NOT    W => ~Word W          ~> #push ... </op>

    syntax BinStackOp ::= "ADD" | "MUL" | "SUB" | "DIV" | "EXP" | "MOD"
 // -------------------------------------------------------------------
    rule <op> ADD W0 W1 => W0 +Word W1 ~> #push ... </op>
    rule <op> MUL W0 W1 => W0 *Word W1 ~> #push ... </op>
    rule <op> SUB W0 W1 => W0 -Word W1 ~> #push ... </op>
    rule <op> DIV W0 W1 => W0 /Word W1 ~> #push ... </op>
    rule <op> EXP W0 W1 => W0 ^Word W1 ~> #push ... </op>
    rule <op> MOD W0 W1 => W0 %Word W1 ~> #push ... </op>

    syntax BinStackOp ::= "SDIV" | "SMOD"
 // -------------------------------------
    rule <op> SDIV W0 W1 => W0 /sWord W1 ~> #push ... </op>
    rule <op> SMOD W0 W1 => W0 %sWord W1 ~> #push ... </op>

    syntax TernStackOp ::= "ADDMOD" | "MULMOD"
 // ------------------------------------------
    rule <op> ADDMOD W0 W1 W2 => (W0 +Int W1) %Word W2 ~> #push ... </op>
    rule <op> MULMOD W0 W1 W2 => (W0 *Int W1) %Word W2 ~> #push ... </op>

    syntax BinStackOp ::= "BYTE"
 // ----------------------------
    rule <op> BYTE INDEX W  => byte(INDEX, W) ~> #push ... </op>

    syntax BinStackOp ::= "AND" | "EVMOR" | "XOR"
 // ---------------------------------------------
    rule <op> AND   W0 W1 => W0 &Word W1   ~> #push ... </op>
    rule <op> EVMOR W0 W1 => W0 |Word W1   ~> #push ... </op>
    rule <op> XOR   W0 W1 => W0 xorWord W1 ~> #push ... </op>

    syntax BinStackOp ::= "LT" | "GT" | "EQ"
 // ----------------------------------------
    rule <op> LT W0 W1 => W0 <Word W1  ~> #push ... </op>
    rule <op> GT W0 W1 => W0 >Word W1  ~> #push ... </op>
    rule <op> EQ W0 W1 => W0 ==Word W1 ~> #push ... </op>

    syntax BinStackOp ::= "SLT" | "SGT"
 // -----------------------------------
    rule <op> SLT W0 W1 => W0 s<Word W1 ~> #push ... </op>
    rule <op> SGT W0 W1 => W0 s>Word W1 ~> #push ... </op>
```

TODO: Calculate \mu_i

```k
    syntax BinStackOp ::= "SHA3"
 // ----------------------------
    rule <op> SHA3 MEMSTART MEMWIDTH => keccak(#range(LM, MEMSTART, MEMWIDTH)) ... </op>
         <localMem> LM </localMem>
```

Local State
-----------

These operators make queries about the current execution state.

```k
    syntax NullStackOp ::= "PC" | "GAS" | "GASPRICE" | "GASLIMIT"
 // -------------------------------------------------------------
    rule <op> PC       => (PCOUNT -Int 1) ~> #push ~> #checkStackSize ... </op> <pc> PCOUNT </pc>
    rule <op> GAS      => GAVAIL          ~> #push ~> #checkStackSize ... </op> <gas> GAVAIL </gas>
    rule <op> GASPRICE => GPRICE          ~> #push ~> #checkStackSize ... </op> <gasPrice> GPRICE </gasPrice>
    rule <op> GASLIMIT => GLIMIT          ~> #push ~> #checkStackSize ... </op> <gasLimit> GLIMIT </gasLimit>

    syntax NullStackOp ::= "COINBASE" | "TIMESTAMP" | "NUMBER" | "DIFFICULTY"
 // -------------------------------------------------------------------------
    rule <op> COINBASE   => CB   ~> #push ~> #checkStackSize ... </op> <coinbase> CB </coinbase>
    rule <op> TIMESTAMP  => TS   ~> #push ~> #checkStackSize ... </op> <timestamp> TS </timestamp>
    rule <op> NUMBER     => NUMB ~> #push ~> #checkStackSize ... </op> <number> NUMB </number>
    rule <op> DIFFICULTY => DIFF ~> #push ~> #checkStackSize ... </op> <difficulty> DIFF </difficulty>

    syntax NullStackOp ::= "ADDRESS" | "ORIGIN" | "CALLER" | "CALLVALUE"
 // --------------------------------------------------------------------
    rule <op> ADDRESS   => ACCT ~> #push ~> #checkStackSize ... </op> <id> ACCT </id>
    rule <op> ORIGIN    => ORG  ~> #push ~> #checkStackSize ... </op> <origin> ORG </origin>
    rule <op> CALLER    => CL   ~> #push ~> #checkStackSize ... </op> <caller> CL </caller>
    rule <op> CALLVALUE => CV   ~> #push ~> #checkStackSize ... </op> <callValue> CV </callValue>

    syntax NullStackOp ::= "MSIZE" | "CODESIZE"
 // -------------------------------------------
    rule <op> MSIZE    => 32 *Word size(LM) ~> #push ~> #checkStackSize ... </op> <localMem> LM </localMem>
    rule <op> CODESIZE => size(PGM)         ~> #push ~> #checkStackSize ... </op> <program> PGM </program>
```

TODO: Calculate \mu_i

```k
    syntax TernStackOp ::= "CODECOPY"
 // ---------------------------------
    rule <op> CODECOPY MEMSTART PGMSTART WIDTH => . ... </op>
         <program> PGM </program>
         <localMem> LM => LM [ MEMSTART := #asmOpCodes(#asOpCodes(PGM)) [ PGMSTART .. WIDTH ] ] </localMem>
```

`JUMP*`
-------

The `JUMP*` family of operations affect the current program counter.

```k
    syntax Exception   ::= "#invalidJumpDest"

    syntax NullStackOp ::= "JUMPDEST"
    syntax UnStackOp   ::= "JUMP"
    syntax BinStackOp  ::= "JUMPI"
 // ------------------------------
    rule <op> JUMPDEST => . ... </op>

    rule <op> JUMP  DEST   => #invalidJumpDest ... </op> <program> ... DEST |-> OP ... </program> requires OP =/=K JUMPDEST
    rule <op> JUMPI DEST _ => #invalidJumpDest ... </op> <program> ... DEST |-> OP ... </program> requires OP =/=K JUMPDEST

    rule <op> JUMP  DEST   => . ... </op> <program> ... DEST |-> JUMPDEST ... </program> <pc> _ => DEST </pc>
    rule <op> JUMPI DEST 0 => . ... </op> <program> ... DEST |-> JUMPDEST ... </program>
    rule <op> JUMPI DEST I => . ... </op> <program> ... DEST |-> JUMPDEST ... </program> <pc> _ => DEST </pc> requires I =/=K 0
```

Call Data
---------

These operators query about the current `CALL*` state.

TODO: Is the `DATASTART`/`DATAWIDTH` in `CALLDATALOAD`/`CALLDATACOPY` a byte-list width or a word-list width?
TODO: Calculate \mu_i.

```k
    syntax NullStackOp ::= "CALLDATASIZE"
    syntax UnStackOp   ::= "CALLDATALOAD"
    syntax TernStackOp ::= "CALLDATACOPY"
 // -------------------------------------
    rule <op> CALLDATASIZE => #size(CD) ~> #push ~> #checkStackSize ... </op>
         <callData> CD </callData>

    rule <op> CALLDATALOAD DATASTART => #asWord(CD [ DATASTART .. 32 ]) ~> #push ... </op>
         <callData> CD </callData>

    rule <op> CALLDATACOPY MEMSTART DATASTART DATAWIDTH => . ... </op>
         <localMem> LM => LM [ MEMSTART := CD [ DATASTART .. DATAWIDTH ] ] </localMem>
         <callData> CD </callData>
```

Log Operations
--------------

TODO: Calculate \mu_i.

```k
    syntax LogOp  ::= LOG ( Word )
 // ------------------------------
    rule <op> LOG(N) => . ... </op>
         <id> ACCT </id>
         <wordStack> W0 : W1 : WS => #drop(N, WS) </wordStack>
         <localMem> LM </localMem>
         <log> CURRLOG => CURRLOG . { ACCT | #take(N, WS) | #range(LM, W0, W1) } </log>
      requires word2Bool(#size(WS) >=Word N)

    syntax Exception   ::= "#invalidInstruction"
    syntax NullStackOp ::= "INVALID"
 // --------------------------------
    rule <op> INVALID => #invalidInstruction ... </op>
```

Ethereum Network
================

Operators that require access to the rest of the Ethereum network world-state can be taken as a first draft of a "blockchain generic" language.

Account Queries
---------------

TODO: It's unclear what to do in the case of an account not existing for these operators.
`BALANCE` is specified to push 0 in this case, but the others are not specified.
For now, I assume that they instantiate an empty account and use the empty data.

```k
    syntax UnStackOp ::= "BALANCE"
 // ------------------------------
    rule <op> BALANCE ACCT => BAL ~> #push ... </op>
         <account>
           <acctID> ACCTACT </acctID>
           <balance> BAL </balance>
           ...
         </account>
      requires #addr(ACCT) ==K ACCTACT

    rule <op> BALANCE ACCT => #newAccount ACCT ~> 0 ~> #push ... </op>
         <activeAccounts> ACCTS </activeAccounts>
      requires notBool #addr(ACCT) in ACCTS

    syntax UnStackOp ::= "EXTCODESIZE"
 // ----------------------------------
    rule <op> EXTCODESIZE ACCTTO => size(CODE) ~> #push ... </op>
         <account>
           <acctID> ACCTTOACT </acctID>
           <code> CODE </code>
           ...
         </account>
      requires #addr(ACCTTO) ==K ACCTTOACT

    rule <op> EXTCODESIZE ACCTTO => #newAccount ACCTTO ~> 0 ~> #push ... </op>
         <activeAccounts> ACCTS </activeAccounts>
      requires notBool #addr(ACCTTO) in ACCTS
```

TODO: Calculate \mu_i

```k
    syntax QuadStackOp ::= "EXTCODECOPY"
 // ------------------------------------
    rule <op> EXTCODECOPY ACCT MEMSTART PGMSTART WIDTH => . ... </op>
         <localMem> LM => LM [ MEMSTART := #asmOpCodes(#asOpCodes(PGM)) [ PGMSTART .. WIDTH ] ] </localMem>
         <account>
           <acctID> ACCTACT </acctID>
           <code> PGM </code>
           ...
         </account>
      requires #addr(ACCT) ==K ACCTACT

    rule <op> EXTCODECOPY ACCT MEMSTART PGMSTART WIDTH => #newAccount ACCT ... </op>
         <activeAccounts> ACCTS </activeAccounts>
      requires notBool #addr(ACCT) in ACCTS
```

Storage Operations
------------------

These operations interact with the account storage.

```k
    syntax UnStackOp  ::= "SLOAD"
 // -----------------------------
    rule <op> SLOAD INDEX => VALUE ~> #push ... </op>
         <id> ACCT </id>
         <account>
           <acctID> ACCT </acctID>
           <storage> ... INDEX |-> VALUE ... </storage>
           ...
         </account>

    syntax BinStackOp ::= "SSTORE"
 // ------------------------------
    rule <op> SSTORE INDEX 0 => . ... </op>
         <account>
           <acctID> ACCT </acctID>
           <storage> ... (INDEX |-> VALUE => .Map) ... </storage>
           ...
         </account>
         <refund> R => R +Word Rsclear </refund>

    rule <op> SSTORE INDEX 0 => . ... </op>
         <account>
           <acctID> ACCT </acctID>
           <storage> STORAGE </storage>
           ...
         </account>
      requires notBool (INDEX in keys(STORAGE))

    rule <op> SSTORE INDEX VALUE => . ... </op>
         <account>
           <acctID> ACCT </acctID>
           <storage> STORAGE => STORAGE [ INDEX <- VALUE ] </storage>
           ...
         </account>
      requires VALUE =/=K 0
```

Call Operations
---------------

The various `CALL*` (and other inter-contract control flow) operations will be desugared into these `InternalOp`s.

-   `#returnLoc__` is a placeholder for the calling program, specifying where to place the returned data in memory.
-   `#return_` contains the word-stack of returned data.

```k
    syntax InternalOp ::= "#returnLoc" Word Word
                        | "#return" WordStack
 // -----------------------------------------
    rule <op> #return (WS:WordStack) ~> #returnLoc RETSTART RETWIDTH => . ... </op>
         <localMem> LM => LM [ RETSTART := #take(minWord(RETWIDTH, #size(WS)), WS) ] </localMem>
```

-   `#call_____` takes the calling account, the account to execute as, the accounts code to use, the amount to transfer, and the arguments.
    It actually performs the code-call.

```k
    syntax InternalOp ::= "#call" Word Word Word Word WordStack
 // -----------------------------------------------------------
    rule <op> #call ACCTFROM ACCTTO ACCTEXEC VALUE ARGS => . ... </op>
         <callStack> CS </callStack>
         <id>       _ => ACCTTO       </id>
         <pc>       _ => 0            </pc>
         <caller>   _ => ACCTFROM     </caller>
         <localMem> _ => #asMap(ARGS) </localMem>
         <program>  _ => CODE         </program>
         <account>
           <acctID> ACCTEXEC </acctID>
           <code>   CODE     </code>
           ...
         </account>
         <account>
           <acctID>  ACCTFROM </acctID>
           <balance> BAL      </balance>
           ...
         </account>
      requires word2Bool(VALUE <=Word BAL) andBool (#size(CS) <Int 1024)
```

TODO: (Entire section): Calculate \mu_i.

```k
    syntax BinStackOp ::= "RETURN"
 // ------------------------------
    rule <op> RETURN RETSTART RETWIDTH => #popCallStack ~> #return #range(LM, RETSTART, RETWIDTH) ... </op>
         <localMem> LM </localMem>

    syntax CallOp ::= "CALL" | "CALLCODE" | "DELEGATECALL"
 // ------------------------------------------------------
    rule <op> CALL GASCAP ACCTTO VALUE ARGSTART ARGWIDTH RETSTART RETWIDTH
           => #pushCallStack
           ~> #call ACCTFROM #addr(ACCTTO) #addr(ACCTTO) VALUE #range(LM, ARGSTART, ARGWIDTH)
           ~> #returnLoc RETSTART RETWIDTH
           ...
         </op>
         <id> ACCTFROM </id>
         <localMem> LM </localMem>

    rule <op> CALLCODE GASCAP ACCTTO VALUE ARGSTART ARGWIDTH RETSTART RETWIDTH
           => #pushCallStack
           ~> #call ACCTFROM ACCTFROM #addr(ACCTTO) VALUE #range(LM, ARGSTART, ARGWIDTH)
           ~> #returnLoc RETSTART RETWIDTH
           ...
         </op>
         <id> ACCTFROM </id>
         <localMem> LM </localMem>

    rule <op> DELEGATECALL GASCAP ACCTTO ARGSTART ARGWIDTH RETSTART RETWIDTH
           => #pushCallStack
           ~> #call ACCTFROM ACCTFROM #addr(ACCTTO) 0 #range(LM, ARGSTART, ARGWIDTH)
           ~> #returnLoc RETSTART RETWIDTH
           ...
         </op>
         <id> ACCTFROM </id>
         <localMem> LM </localMem>
```

TODO: Calculating gas for `SELFDESTRUCT` needs to take into account the cost of creating an account if the recipient address doesn't exist yet. Should it also actually create the recipient address if not? Perhaps `#transfer` can take that into account automatically for us?

```k
    syntax UnStackOp ::= "SELFDESTRUCT"
 // -----------------------------------
    rule <op> SELFDESTRUCT ACCTTO => . ... </op>
         <id> ACCT </id>
         <selfDestruct> SDS (.Set => SetItem(ACCT)) </selfDestruct>
         <refund> RF => #ifWord ACCT in SDS #then RF #else RF +Word Rself-destruct #fi </refund>
         <account>
           <acctID> ACCT </acctID>
           <balance> BALFROM => 0 </balance>
           ...
         </account>
         <account>
           <acctID> ACCTTOACT </acctID>
           <balance> BALTO => BALTO +Word BALFROM </balance>
           ...
         </account>
      requires #addr(ACCTTO) ==K ACCTTOACT

    rule <op> SELFDESTRUCT ACCTTO => . ... </op>
         <id> ACCT </id>
         <selfDestruct> SDS (.Set => SetItem(ACCT)) </selfDestruct>
         <refund> RF => #ifWord ACCT in SDS #then RF #else RF +Word Rself-destruct #fi </refund>
         <activeAccounts> ACCTS (.Set => SetItem(#addr(ACCTTO))) </activeAccounts>
         <accounts>
           <account>
             <acctID> ACCT </acctID>
             <balance> BALFROM => 0 </balance>
             ...
           </account>
           ( .Bag
          => <account>
               <acctID>  #addr(ACCTTO) </acctID>
               <balance> BALFROM       </balance>
               <code>    .Map          </code>
               <storage> .Map          </storage>
               <acctMap> "nonce" |-> 0 </acctMap>
             </account>
           )
           ...
         </accounts>
      requires notBool #addr(ACCTTO) in ACCTS
```

Unimplemented
=============

These operators should be implemented and binned into the correct sections above.

```k
    syntax BinStackOp ::= "SIGNEXTEND"
 // ----------------------------------
    rule <op> SIGNEXTEND W0 W1 => signextend(W0, W1) ~> #push ... </op>

    syntax NullStackOp ::= "STOP"
 // -----------------------------

    syntax UnStackOp ::= "BLOCKHASH"
 // --------------------------------

    syntax TernStackOp ::= "CREATE"
 // -------------------------------
```

Ethereum Gas Calculation
========================

-   `#gas` will compute the gas used and then deduct it from the total gas available.
-   `#outOfGas` signals an out-of-gas exception.

```k
    syntax Exception ::= "#outOfGas"
    syntax KItem     ::= "#checkGas"
                       | #gas ( Word ) [function]
 // ---------------------------------------------
    rule <op> G':Int ~> #checkGas => .         ... </op> <gas> G => G -Int G' </gas> requires G' <=Int G
    rule <op> G':Int ~> #checkGas => #outOfGas ... </op> <gas> G              </gas> requires G' >Int G
```

The gas calculation is designed to mirror the style of the yellowpaper.

```k
    syntax Word ::= "Gzero" | "Gbase" | "Gverylow" | "Glow" | "Gmid" | "Ghigh" | "Gextcode"
                  | "Gbalance" | "Gsload" | "Gjumpdest" | "Gsset" | "Gsreset" | "Rsclear"
                  | "Rself-destruct" | "Gself-destruct" | "Gcreate" | "Gcodedeposit" | "Gcall"
                  | "Gcallvalue" | "Gcallstipend" | "Gnewaccount" | "Gexp" | "Gexpbyte"
                  | "Gmemory" | "Gtxcreate" | "Gtxdatazero" | "Gtxdatanonzero" | "Gtransaction"
                  | "Glog" | "Glogdata" | "Glogtopic" | "Gsha3" | "Gsha3word" | "Gcopy" | "Gblockhash"
                  | "#gasSSTORE" | "#gasCALL" | "#gasSELFDESTRUCT"
 // --------------------------------------------------------------
    rule Gzero          => 0        [macro]
    rule Gbase          => 2        [macro]
    rule Gverylow       => 3        [macro]
    rule Glow           => 5        [macro]
    rule Gmid           => 8        [macro]
    rule Ghigh          => 10       [macro]
    rule Gextcode       => 700      [macro]
    rule Gbalance       => 400      [macro]
    rule Gsload         => 200      [macro]
    rule Gjumpdest      => 1        [macro]
    rule Gsset          => 20000    [macro]
    rule Gsreset        => 5000     [macro]
    rule Rsclear        => 15000    [macro]
    rule Rself-destruct => 24000    [macro]
    rule Gself-destruct => 5000     [macro]
    rule Gcreate        => 32000    [macro]
    rule Gcodedeposit   => 200      [macro]
    rule Gcall          => 700      [macro]
    rule Gcallvalue     => 9000     [macro]
    rule Gcallstipend   => 2300     [macro]
    rule Gnewaccount    => 25000    [macro]
    rule Gexp           => 10       [macro]
    rule Gexpbyte       => 10       [macro]
    rule Gmemory        => 3        [macro]
    rule Gtxcreate      => 32000    [macro]
    rule Gtxdatazero    => 4        [macro]
    rule Gtxdatanonzero => 68       [macro]
    rule Gtransaction   => 21000    [macro]
    rule Glog           => 375      [macro]
    rule Glogdata       => 8        [macro]
    rule Glogtopic      => 375      [macro]
    rule Gsha3          => 30       [macro]
    rule Gsha3word      => 6        [macro]
    rule Gcopy          => 3        [macro]
    rule Gblockhash     => 20       [macro]

    syntax OpCodes ::= "Wzero" | "Wbase" | "Wverylow" | "Wlow" | "Wmid" | "Whigh" | "Wextcode" | "Wcopy" | "Wcall"
 // --------------------------------------------------------------------------------------------------------------
    rule Wzero    => STOP ; RETURN ; .OpCodes                                               [macro]
    rule Wbase    =>   ADDRESS ; ORIGIN ; CALLER ; CALLVALUE ; CALLDATASIZE
                     ; CODESIZE ; GASPRICE ; COINBASE ; TIMESTAMP ; NUMBER
                     ; DIFFICULTY ; GASLIMIT ; POP ; PC ; MSIZE ; GAS ; .OpCodes            [macro]
    rule Wverylow =>   ADD ; SUB ; NOT ; LT ; GT ; SLT ; SGT ; EQ ; ISZERO ; AND
                     ; EVMOR ; XOR ; BYTE ; CALLDATALOAD ; MLOAD ; MSTORE ; MSTORE8
                     ; PUSH(0, 0) ; DUP(0) ; SWAP(0) ; .OpCodes                             [macro]
    rule Wlow     => MUL ; DIV ; SDIV ; MOD ; SMOD ; SIGNEXTEND ; .OpCodes                  [macro]
    rule Wmid     => ADDMOD ; MULMOD ; JUMP ; JUMPI; .OpCodes                               [macro]
    rule Wextcode => EXTCODESIZE ; .OpCodes                                                 [macro]
    rule Wcopy    => CALLDATACOPY ; CODECOPY ; .OpCodes                                     [macro]
    rule Wcall    => CALL ; CALLCODE ; DELEGATECALL ; .OpCodes                              [macro]
```

TODO: The rules marked as `INCORRECT` below are performing simpler gas calculations than the actual yellowpaper specifies.

```k
    syntax Word ::= #gas ( OpCode ) [function]
 // ------------------------------------------
    // rule <op> #gas(OP)           => ???                           ... </op> requires OP in Wcall
    // rule <op> #gas(SELFDESTRUCT) => ???                           ... </op>
    rule <op> #gas(EXP)          => Gexp                          ... </op>                        // INCORRECT
    rule <op> #gas(OP)           => Gverylow +Word Gcopy          ... </op> requires OP in Wcopy   // INCORRECT
    rule <op> #gas(EXTCODECOPY)  => Gextcode +Word Gcopy          ... </op>                        // INCORRECT
    rule <op> #gas(LOG(N))       => Glog +Word (N *Word Glogdata) ... </op>                        // INCORRECT
    rule <op> #gas(CREATE)       => Gcreate                       ... </op>
    rule <op> #gas(SHA3)         => Gsha3                         ... </op>                        // INCORRECT
    rule <op> #gas(JUMPDEST)     => Gjumpdest                     ... </op>

    rule <op> #gas(SLOAD)  => Gsload  ... </op>
    rule <op> #gas(SSTORE) => #if W1 =/=K 0 andBool notBool W0 in keys(STORAGE) #then Gsset #else Gsreset #fi ... </op>
         <wordStack> W0 : W1 : WS </wordStack> <storage> STORAGE </storage>

    rule <op> #gas(OP)           => Gzero                         ... </op> requires OP in Wzero
    rule <op> #gas(OP)           => Gbase                         ... </op> requires OP in Wbase
    rule <op> #gas(OP)           => Gverylow                      ... </op> requires OP in Wverylow
    rule <op> #gas(OP)           => Glow                          ... </op> requires OP in Wlow
    rule <op> #gas(OP)           => Gmid                          ... </op> requires OP in Wmid
    rule <op> #gas(OP)           => Ghigh                         ... </op> requires OP in Whigh
    rule <op> #gas(OP)           => Gextcode                      ... </op> requires OP in Wextcode
    rule <op> #gas(BALANCE)      => Gbalance                      ... </op>
    rule <op> #gas(BLOCKHASH)    => Gblockhash                    ... </op>
endmodule
```
