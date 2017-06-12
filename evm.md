EVM Execution
=============

The EVM is a stack machine over some simple opcodes. Most of the opcodes are
"local" to the execution state of the machine, but some of them must interact
with the world state. This file only defines the local execution operations, the
file `ethereum.md` will define the interactions with the world state.

Configuration
-------------

The configuration has cells for the current account id, the current opcode, the
program counter, the current gas, the gas price, the current program, the word
stack, and the local memory. In addition, there are cells for the callstack and
execution substate.

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
                      <op> . </op>
                      <txExecState>
                        <id>        0:Word     </id>                  // I_a
                        <wordStack> .WordStack </wordStack>           // \mu_s
                        <localMem>  .Map       </localMem>            // \mu_m
                        <program>   .Map       </program>
                        <pc>        0:Word     </pc>                  // \mu_pc
                        <gas>       0:Word     </gas>                 // \mu_g
                        <caller>    0:Word     </caller>              // I_s
                      </txExecState>

                      // A_* (execution substate)
                      <substate>
                        <selfDestruct> .WordStack   </selfDestruct>   // A_s
                        <log>          .SubstateLog </log>            // A_l
                        <refund>       0:Word       </refund>         // A_r
                      </substate>

                      // Immutable during a single transaction
                      // -------------------------------------

                      <gasPrice>   0:Word </gasPrice>                 // I_p
                      <origin>     0:Word </origin>                   // I_o
                      <callValue>  0:Word </callValue>                // I_v

                      // I_H* (block information)
                      <gasLimit>   0:Word </gasLimit>                 // I_Hl
                      <coinbase>   0:Word </coinbase>                 // I_Hc
                      <timestamp>  0:Word </timestamp>                // I_Hs
                      <number>     0:Word </number>                   // I_Hi
                      <difficulty> 0:Word </difficulty>               // I_Hd

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
The gas needed is calculated here.

Note that we must treat loading of `PUSH` specially, given that the arguments of `PUSH` are inline with the code itself.
Given the several special treatments of `PUSH`, the usefulness of this design for EVM becomes dubious.

```k
    rule <op> . => OP </op>
         <pc> PCOUNT => PCOUNT +Word 1 </pc>
         <gas> G => G -Word #gas(OP) </gas>
         <program> ... PCOUNT |-> OP ... </program>
         <currOps> ... (.Set => SetItem(OP)) </currOps>
      requires word2Bool(G >=Word #gas(OP)) andBool notBool isPushOp(OP)

    rule <op> . => PUSH(N, W) </op>
         <pc> PCOUNT => PCOUNT +Word (1 +Word N) </pc>
         <gas> G => G -Word #gas(PUSH(N, W)) </gas>
         <program> ... PCOUNT |-> PUSH(N, W) ... </program>
         <currOps> ... (.Set => SetItem(PUSH(N, W))) </currOps>
      requires word2Bool(G >=Word #gas(PUSH(N, W)))
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
    rule <op> UOP:UnStackOp   => UOP W0          ... </op> <wordStack> W0 : WS                => WS </wordStack>
    rule <op> BOP:BinStackOp  => BOP W0 W1       ... </op> <wordStack> W0 : W1 : WS           => WS </wordStack>
    rule <op> TOP:TernStackOp => TOP W0 W1 W2    ... </op> <wordStack> W0 : W1 : W2 : WS      => WS </wordStack>
    rule <op> QOP:QuadStackOp => QOP W0 W1 W2 W3 ... </op> <wordStack> W0 : W1 : W2 : W3 : WS => WS </wordStack>

    syntax KItem ::= CallOp Word Word Word Word Word Word Word
                   | "DELEGATECALL" Word Word Word Word Word Word
 // -------------------------------------------------------------
    rule <op> DELEGATECALL => DELEGATECALL W0 W1 W2 W3 W4 W5    ... </op> <wordStack> W0 : W1 : W2 : W3 : W4 : W5 : WS      => WS </wordStack>
    rule <op> CO:CallOp    => CO           W0 W1 W2 W3 W4 W5 W6 ... </op> <wordStack> W0 : W1 : W2 : W3 : W4 : W5 : W6 : WS => WS </wordStack>
      requires CO =/=K DELEGATECALL

    syntax KItem ::= StackOp WordStack
 // ----------------------------------
    rule <op> SO:StackOp => SO WS ... </op> <wordStack> WS </wordStack>
```

EVM Substate Log
----------------

During execution of a transaction some things are recorded in the substate log.
This is a right cons-list of `SubstateLogEntry` (which contains the account ID along with the specified portions of the `wordStack` and `localMem`).

```k
    syntax SubstateLog      ::= ".SubstateLog" | SubstateLog "." SubstateLogEntry
    syntax SubstateLogEntry ::= "{" Word "|" WordStack "|" WordStack "}"
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
-   `#stackOverflow` signals that there has been a stack overflow.

```k
    syntax InternalOp ::= "#checkStackSize" | "#stackOverflow"
 // ----------------------------------------------------------
    rule <op> #checkStackSize => #stackSize(WS) ~> #checkStackSize ... </op> <wordStack> WS </wordStack>
    rule <op> I:Int ~> #checkStackSize => .              ... </op> requires I <Int  1024
    rule <op> I:Int ~> #checkStackSize => #stackOverflow ... </op> requires I >=Int 1024
```

Callstack
---------

Previous process states must be stored, so a tuple of sort `Process` is supplied for that.
The `CallStack` is a cons-list of `Process`.

-   `#pushCallStack` stores the current state on the `callStack`.
-   `#popCallStack` replaces the current state with the top of the `callStack`.

```k
    syntax CallStack ::= ".CallStack" | Bag CallStack

    syntax InternalOp ::= "#pushCallStack" | "#popCallStack"
 // --------------------------------------------------------
    rule <op> #pushCallStack => . </op>
         <callStack> CS => TXSTATE CS </callStack>
         <txExecState> TXSTATE </txExecState>

    rule <op> #popCallStack => . </op>
         <callStack> TXSTATE CS => CS </callStack>
         <txExecState> _ => TXSTATE </txExecState>
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
    rule <op> DUP(N)  WS:WordStack => #setStack ((WS [ N -Word 1 ]) : WS) ~> #checkStackSize    ... </op>
    rule <op> SWAP(N) (W0 : WS)    => #setStack ((WS [ N -Word 1 ]) : (WS [ N -Word 1 := W0 ])) ... </op>

    syntax PushOp ::= PUSH ( Word , Word )
 // --------------------------------------
    rule <op> PUSH(_, W) => W ~> #push ~> #checkStackSize ... </op>
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

    syntax TernStackOp ::= "ADDMOD" | "MULMOD"
 // ------------------------------------------
    rule <op> ADDMOD W0 W1 W2 => (W0 +Word W1) %Word W2 ~> #push ... </op>
    rule <op> MULMOD W0 W1 W2 => (W0 *Word W1) %Word W2 ~> #push ... </op>
```

TODO: Unimplemented.

```k
    syntax BinStackOp ::= "SLT" | "SGT" | "SDIV" | "SMOD" | "SIGNEXTEND" | "BYTE" | "SHA3"
 // --------------------------------------------------------------------------------------
```

`JUMP*`
-------

The `JUMP*` family of operations affect the current program counter.

```k
    syntax NullStackOp ::= "JUMPDEST"
    syntax UnStackOp   ::= "JUMP"
    syntax BinStackOp  ::= "JUMPI"
 // ------------------------------
    rule <op> JUMPDEST     => .         ... </op>
    rule <op> JUMP  DEST   => .         ... </op> <pc> _ => DEST </pc>
    rule <op> JUMPI DEST 0 => .         ... </op>
    rule <op> JUMPI DEST W => JUMP DEST ... </op> requires W =/=K 0
```

Local State
-----------

These operators make queries about the current execution state.

```k
    syntax NullStackOp ::= "PC" | "GAS" | "GASPRICE" | "GASLIMIT"
 // -------------------------------------------------------------
    rule <op> PC       => (PCOUNT -Int 1) ~> #push ... </op> <pc> PCOUNT </pc>
    rule <op> GAS      => GAVAIL          ~> #push ... </op> <gas> GAVAIL </gas>
    rule <op> GASPRICE => GPRICE          ~> #push ... </op> <gasPrice> GPRICE </gasPrice>
    rule <op> GASLIMIT => GLIMIT          ~> #push ... </op> <gasLimit> GLIMIT </gasLimit>

    syntax NullStackOp ::= "COINBASE" | "TIMESTAMP" | "NUMBER" | "DIFFICULTY"
 // -------------------------------------------------------------------------
    rule <op> COINBASE   => CB   ~> #push ... </op> <coinbase> CB </coinbase>
    rule <op> TIMESTAMP  => TS   ~> #push ... </op> <timestamp> TS </timestamp>
    rule <op> NUMBER     => NUMB ~> #push ... </op> <number> NUMB </number>
    rule <op> DIFFICULTY => DIFF ~> #push ... </op> <difficulty> DIFF </difficulty>

    syntax NullStackOp ::= "ADDRESS" | "ORIGIN" | "CALLER" | "CALLVALUE"
 // --------------------------------------------------------------------
    rule <op> ADDRESS   => ACCT ~> #push ... </op> <id> ACCT </id>
    rule <op> ORIGIN    => ORG  ~> #push ... </op> <origin> ORG </origin>
    rule <op> CALLER    => CL   ~> #push ... </op> <caller> CL </caller>
    rule <op> CALLVALUE => CV   ~> #push ... </op> <callValue> CV </callValue>

    syntax NullStackOp ::= "MSIZE" | "CODESIZE"
 // -------------------------------------------
    rule <op> MSIZE    => 32 *Word size(LM) ~> #push ... </op> <localMem> LM </localMem>
    rule <op> CODESIZE => size(PGM)         ~> #push ... </op> <program> PGM </program>
```

These operations are getters/setters of the local execution memory.

TODO: `MSTORE8` is unimplemented.
TODO: Calculate \mu_i.

```k
    syntax UnStackOp  ::= "MLOAD"
    syntax BinStackOp ::= "MSTORE" | "MSTORE8"
 // ------------------------------------------
    rule <op> MLOAD  INDEX       => VALUE ~> #push ... </op> <localMem> ... INDEX |-> VALUE ...  </localMem>
    rule <op> MSTORE INDEX VALUE => .              ... </op> <localMem> LM => LM [ INDEX <- VALUE ] </localMem>
```

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
```

Ethereum Network
================

```k
    syntax UnStackOp  ::= "BALANCE"
 // -------------------------------
    rule <op> BALANCE ACCT => BAL ~> #push ... </op>
         <account>
           <acctID> ACCT </acctID>
           <balance> BAL </balance>
           ...
         </account>
```

TODO: Calculate \mu_i.

```k
    syntax UnStackOp  ::= "SLOAD"
    syntax BinStackOp ::= "SSTORE"
 // ------------------------------
    rule <op> SLOAD INDEX => VALUE ~> #push ... </op>
         <id> ACCT </id>
         <account>
           <acctID> ACCT </acctID>
           <storage> ... INDEX |-> VALUE ... </storage>
           ...
         </account>

    rule <op> SSTORE INDEX VALUE => . ... </op>
         <id> ACCT </id>
         <account>
           <acctID> ACCT </acctID>
           <storage> STORAGE => STORAGE [ INDEX <- VALUE ] </storage>
           ...
         </account>
```

Call Operations
---------------

TODO: (Entire section): Calculate \mu_i.

```k
    syntax CallOp ::= "CALL" | "CALLCODE" | "DELEGATECALL"
 // ------------------------------------------------------
    rule <op> CALL GASCAP ACCTTO VALUE ARGSTART ARGWIDTH RETSTART RETWIDTH
           =>  ( #call ACCTFROM #addr(ACCTTO) #addr(ACCTTO) #range(LM, ARGSTART, ARGWIDTH)
              ~> #return RETSTART RETWIDTH
               )
         </op>
         <id> ACCTFROM </id>
         <localMem> LM </localMem>

    syntax InternalOp ::= "#call" Word Word Word WordStack
                        | "#return" Word Word
                        | "#return" WordStack

    syntax BinStackOp ::= "RETURN"
 // ------------------------------
    rule <op> RETURN RETSTART RETWIDTH => #popCallStack ~> #return #range(LM, RETSTART, RETWIDTH) ... </op>
         <localMem> LM </localMem>

    rule <op> #return (WS:WordStack) ~> #return RETSTART RETWIDTH => . ... </op>
         <localMem> LM => LM [ RETSTART := #take(minWord(RETWIDTH, #size(WS)), WS) ] </localMem>
```

TODO: Calculating gas for `SELFDESTRUCT` needs to take into account the cost of creating an account if the recipient address doesn't exist yet. Should it also actually create the recipient address if not? Perhaps `#transfer` can take that into account automatically for us?

```k
    syntax UnStackOp ::= "SELFDESTRUCT"
 // -----------------------------------
    rule <op> SELFDESTRUCT ACCTTO => . ... </op>
         <id> ACCT </id>
         <selfDestruct> SD </selfDestruct>
         <account>
           <acctID> ACCT </acctID>
           <balance> BALFROM => 0 </balance>
           ...
         </account>
         <account>
           <acctID> ACCTTO </acctID>
           <balance> BALTO => BALTO +Word BALFROM </balance>
           ...
         </account>
      requires ACCT in SD

    rule <op> SELFDESTRUCT ACCTTO => . ... </op>
         <id> ACCT </id>
         <selfDestruct> SD => ACCT : SD               </selfDestruct>
         <refund>       RF => RF +Word Rself-destruct </refund>
         <account>
           <acctID> ACCT </acctID>
           <balance> BALFROM => 0 </balance>
           ...
         </account>
         <account>
           <acctID> ACCTTO </acctID>
           <balance> BALTO => BALTO +Word BALFROM </balance>
           ...
         </account>
      requires notBool (ACCT in SD)
```

TODO: Unimplemented.

```k
    syntax NullStackOp ::= "INVALID" | "STOP"
 // -----------------------------------------

    syntax UnStackOp   ::= "BLOCKHASH" | "CALLDATALOAD" | "EXTCODESIZE"
 // -------------------------------------------------------------------

    syntax TernStackOp ::= "CALLDATACOPY" | "CODECOPY" | "CREATE"
 // -------------------------------------------------------------

    syntax QuadStackOp ::= "EXTCODECOPY"
 // ------------------------------------

    syntax NullStackOp ::= "CALLDATASIZE"
 // -------------------------------------
```

Ethereum Gas Calculation
========================

Here we define the gas-cost of each instruction in the instruction set. Many of
the instructions gas cost is fixed and not dependent on any parts of the
configuration; for those that do have some dependence, their associated cost
must be defined after the configuration is defined.

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

TODO: The rules marked as `INCORRECT` below are performing simpler gas
calculations than the actual yellowpaper specifies.

```k
    syntax Word ::= #gas ( OpCode ) [function]
 // ------------------------------------------
    rule #gas(SSTORE)       => #gasSSTORE                                           // INCORRECT
    rule #gas(EXP)          => Gexp                                                 // INCORRECT
    rule #gas(OP)           => Gverylow +Word Gcopy          requires OP in Wcopy   // INCORRECT
    rule #gas(EXTCODECOPY)  => Gextcode +Word Gcopy                                 // INCORRECT
    rule #gas(LOG(N))       => Glog +Word (N *Word Glogdata)                        // INCORRECT
    rule #gas(OP)           => #gasCALL                      requires OP in Wcall   // INCORRECT
    rule #gas(SELFDESTRUCT) => #gasSELFDESTRUCT                                     // INCORRECT
    rule #gas(CREATE)       => Gcreate
    rule #gas(SHA3)         => Gsha3                                                // INCORRECT
    rule #gas(JUMPDEST)     => Gjumpdest
    rule #gas(SLOAD)        => Gsload
    rule #gas(OP)           => Gzero                         requires OP in Wzero
    rule #gas(OP)           => Gbase                         requires OP in Wbase
    rule #gas(OP)           => Gverylow                      requires OP in Wverylow
    rule #gas(OP)           => Glow                          requires OP in Wlow
    rule #gas(OP)           => Gmid                          requires OP in Wmid
    rule #gas(OP)           => Ghigh                         requires OP in Whigh
    rule #gas(OP)           => Gextcode                      requires OP in Wextcode
    rule #gas(BALANCE)      => Gbalance
    rule #gas(BLOCKHASH)    => Gblockhash
endmodule
```
