YellowPaper
===========

In the yellowpaper the function `#exceptional?` is called `Z` (Section 9.4.2 in yellowpaper).
It checks, in order:

-   The instruction isn't `INVALID`.
-   There are enough elements on the stack to supply the arguments.
-   If it's a `JUMP*` operation, the destination is a valid `JUMPDEST`.
-   Upon placing the results on the stack, there won't be a stack overflow.
-   There is enough gas.

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

```{.k .rvk}
requires "krypto.k"
```

```{.k .uiuck .rvk}
requires "data.k"

module ETHEREUM
    imports EVM-DATA
    imports STRING

    configuration <k> $PGM:EthereumSimulation </k>
                  <exit-code exit=""> 0 </exit-code>

                  <ethereum>

                    // EVM Specific
                    // ============

                    <evm>

                      // Mutable during a single transaction
                      // -----------------------------------

                      <op>         .K          </op>
                      <output>     .WordStack  </output>                // H_RETURN
                      <memoryUsed> 0:Word      </memoryUsed>            // \mu_i
                      <callDepth>  0:Word      </callDepth>
                      <callStack>  .List       </callStack>
                      <callLog>    .CallLog    </callLog>

                      <txExecState>
                        <program> .Map </program>                       // I_b

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
                        <selfDestruct> .Set   </selfDestruct>           // A_s
                        <log>          .Set   </log>                    // A_l
                        <refund>       0:Word </refund>                 // A_r
                      </substate>

                      // Immutable during a single transaction
                      // -------------------------------------

                      <gasPrice> 0:Word </gasPrice>                     // I_p
                      <origin>   0:Word </origin>                       // I_o

                      // I_H* (block information)
                      <gasLimit>   0:Word </gasLimit>                   // I_Hl
                      <coinbase>   0:Word </coinbase>                   // I_Hc
                      <timestamp>  0:Word </timestamp>                  // I_Hs
                      <number>     0:Word </number>                     // I_Hi
                      <difficulty> 0:Word </difficulty>                 // I_Hd

                    </evm>

                    // Ethereum Network
                    // ================

                    <network>

                      // Accounts Record
                      // ---------------

                      <activeAccounts> .Set </activeAccounts>
                      <accounts>
```

-   UIUC-K and RV-K have slight differences of opinion here.

```{.k .uiuck}
                        <account multiplicity="*" type="Bag">
```

```{.k .rvk}
                        <account multiplicity="*" type="Map">
```

```{.k .uiuck .rvk}
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
```

-   UIUC-K and RV-K have slight differences of opinion here.

```{.k .uiuck}
                        <message multiplicity="*" type="Bag">
```

```{.k .rvk}
                        <message multiplicity="*" type="Map">
```

```{.k .uiuck .rvk}
                          <msgID>  .MsgID   </msgID>
                          <to>     .AcctID  </to>
                          <from>   .AcctID  </from>
                          <amount> .Value   </amount>
                          <data>   .Map     </data>
                        </message>
                      </messages>

                    </network>

                  </ethereum>

    syntax EthereumSimulation
    syntax AcctID ::= Word | ".AcctID"
    syntax Code   ::= Map  | ".Code"
    syntax MsgID  ::= Word | ".MsgID"
    syntax Value  ::= Word | ".Value"
```

Hardware
--------

The `callStack` stores a list of previous states (so that they can be restored).

-   `#pushCallStack` saves a copy of all the relevant state on the `callStack`
-   `#popCallStack` restores the top element of all the relevant state on the `callStack`

```{.k .uiuck .rvk}
    syntax KItem ::= "{" Word "|" Map "|" Word "|" WordStack "|" Word "|" WordStack "|" Map "|" Word "}"
 // ----------------------------------------------------------------------------------------------------

    syntax InternalOp ::= "#pushCallStack"
 // --------------------------------------
    rule <op> #pushCallStack => . ... </op>
         <callStack> (.List => ListItem({ ACCT | PGM | CR | CD | CV | WS | LM | PCOUNT })) ... </callStack>
         <id>        ACCT   </id>
         <program>   PGM    </program>
         <caller>    CR     </caller>
         <callData>  CD     </callData>
         <callValue> CV     </callValue>
         <wordStack> WS     </wordStack>
         <localMem>  LM     </localMem>
         <pc>        PCOUNT </pc>

    syntax InternalOp ::= "#popCallStack"
 // -------------------------------------
    rule <op> #popCallStack => . ... </op>
         <callStack> (ListItem({ ACCT | PGM | CR | CD | CV | WS | LM | PCOUNT }) => .List) ... </callStack>
         <id>        _ => ACCT   </id>
         <program>   _ => PGM    </program>
         <caller>    _ => CR     </caller>
         <callData>  _ => CD     </callData>
         <callValue> _ => CV     </callValue>
         <wordStack> _ => WS     </wordStack>
         <pc>        _ => PCOUNT </pc>

    syntax InternalOp ::= "#dropCallStack"
 // --------------------------------------
    rule <op> #dropCallStack => . ... </op>
         <callStack> (ListItem(_) => .List) ... </callStack>
```

Simple commands controlling exceptions provide control-flow.

-   `#catch` is used to catch exceptional states so that the state can be rolled back.
-   `#try` automatically puts the correct `#pushCallStack` and `#catch` in place.
-   `#end` is used to indicate the (non-exceptional) end of execution.
-   `#exception` is used to indicate exceptional states (it consumes any operations to be performed after it).

```{.k .uiuck .rvk}
    syntax KItem ::= "#catch" | "#try" K | "#exception" | "#end"
 // ------------------------------------------------------------
    rule <op> #catch => #dropCallStack ... </op>
    rule <op> #try K => #pushCallStack ~> K ~> #catch ... </op>
    rule <op> #exception ~> #catch => #popCallStack ... </op>

    rule <op> #exception ~> (#try _    => .) ... </op>
    rule <op> #exception ~> (W:Word    => .) ... </op>
    rule <op> #exception ~> (OP:OpCode => .) ... </op>
```

OpCode Execution Cycle
----------------------

`OpCode` is broken into several subsorts for easier handling.
Here all `OpCode`s are subsorted into `KItem` (allowing sequentialization), and the various sorts of opcodes are subsorted into `OpCode`.

```{.k .uiuck .rvk}
    syntax KItem  ::= OpCode
    syntax OpCode ::= OpCodeOp "[" OpCode "]"
                    | NullStackOp | UnStackOp | BinStackOp | TernStackOp | QuadStackOp
                    | InvalidOp | StackOp | InternalOp | CallOp | CallSixOp | PushOp | LogOp
 // ----------------------------------------------------------------------------------------
```

Execution follows a simple cycle where first the state is checked for exceptions, then if no exceptions will be thrown the opcode is run.

-   `#next` signals that it's time to begin the next execution cycle.

```{.k .uiuck .rvk}
    syntax InternalOp ::= "#next"
 // -----------------------------
    rule <op> #next => #try (#exceptional? [ OP ] ~> #exec [ OP ] ~> #pc [ OP ]) </op>
         <pc> PCOUNT </pc>
         <program> ... PCOUNT |-> OP ... </program>

    rule <op> #next => #if word2Bool(PCOUNT <Word #sizeOpCodeMap(PGM)) #then #exception #else #end #fi </op>
         <pc> PCOUNT </pc> <program> PGM </program>
      requires notBool (PCOUNT in keys(PGM))
```

### Exceptional Opcodes

Some checks if an opcode will throw an exception are relatively quick and done up front.

-   `#exceptional?` checks if the operator is invalid and will not cause `wordStack` size issues.

```{.k .uiuck .rvk}
    syntax OpCodeOp ::= "#exceptional?"
 // -----------------------------------
    rule <op> #exceptional? [ OP ] => #invalid? [ OP ] ~> #stackNeeded? [ OP ] ~> #badJumpDest? [ OP ] ... </op>
```

-   `#invalid?` checks if it's the designated invalid opcode.

```{.k .uiuck .rvk}
    syntax OpCodeOp ::= "#invalid?"
 // -------------------------------
    rule <op> #invalid? [ INVALID ] => #exception ... </op>
    rule <op> #invalid? [ OP      ] => .          ... </op> requires OP =/=K INVALID
```

-   `#stackNeeded?` checks that the stack will be not be under/overflown.
-   `#stackNeeded`, `#stackAdded`, and `#stackDelta` are helpers for deciding `#stackNeeded?`.

```{.k .uiuck .rvk}
    syntax OpCodeOp ::= "#stackNeeded?"
 // -----------------------------------
    rule <op> #stackNeeded? [ OP ]
           => #if #sizeWordStack(WS) <Int #stackNeeded(OP) orBool #sizeWordStack(WS) +Int #stackDelta(OP) >Int 1024
              #then #exception #else .K #fi
          ...
         </op>
         <wordStack> WS </wordStack>

    syntax Int ::= #stackNeeded ( OpCode ) [function]
 // -------------------------------------------------
    rule #stackNeeded(PUSH(_, _))      => 0
    rule #stackNeeded(NOP:NullStackOp) => 0
    rule #stackNeeded(UOP:UnStackOp)   => 1
    rule #stackNeeded(BOP:BinStackOp)  => 2
    rule #stackNeeded(TOP:TernStackOp) => 3
    rule #stackNeeded(DUP(N))          => N
    rule #stackNeeded(SWAP(N))         => N +Int 1
    rule #stackNeeded(LOG(N))          => N +Int 2
    rule #stackNeeded(DELEGATECALL)    => 6
    rule #stackNeeded(COP:CallOp)      => 7 requires COP =/=K DELEGATECALL

    syntax Int ::= #stackAdded ( OpCode ) [function]
 // ------------------------------------------------
    rule #stackAdded(OP)        => 0 requires OP in #zeroRet
    rule #stackAdded(PUSH(_,_)) => 1
    rule #stackAdded(LOG(_))    => 0
    rule #stackAdded(SWAP(N))   => N
    rule #stackAdded(DUP(N))    => N +Int 1
    rule #stackAdded(OP)        => 1 requires notBool (OP in #zeroRet orBool isPushOp(OP) orBool isLogOp(OP) orBool isStackOp(OP))

    syntax Int ::= #stackDelta ( OpCode ) [function]
 // ------------------------------------------------
    rule #stackDelta(OP) => #stackAdded(OP) -Int #stackNeeded(OP)

    syntax Set ::= "#zeroRet" [function]
 // ------------------------------------
    rule #zeroRet => ( SetItem(CALLDATACOPY) SetItem(CODECOPY) SetItem(EXTCODECOPY)
                       SetItem(POP) SetItem(MSTORE) SetItem(MSTORE8) SetItem(SSTORE)
                       SetItem(JUMP) SetItem(JUMPI) SetItem(JUMPDEST)
                       SetItem(STOP) SetItem(RETURN) SetItem(SELFDESTRUCT)
                     )
```

-   `#badJumpDest?` determines if the opcode will result in a bad jump destination.

```{.k .uiuck .rvk}
    syntax OpCodeOp ::= "#badJumpDest?"
 // -----------------------------------
    rule <op> #badJumpDest? [ OP    ] => . ... </op> requires notBool isJumpOp(OP)
    rule <op> #badJumpDest? [ OP    ] => . ... </op> <wordStack> DEST  : WS </wordStack> <program> ... DEST |-> JUMPDEST ... </program>
    rule <op> #badJumpDest? [ JUMPI ] => . ... </op> <wordStack> _ : 0 : WS </wordStack>

    rule <op> #badJumpDest? [ JUMP  ] => #exception ... </op> <wordStack> DEST :     WS </wordStack> <program> ... DEST |-> OP ... </program> requires OP =/=K JUMPDEST
    rule <op> #badJumpDest? [ JUMPI ] => #exception ... </op> <wordStack> DEST : W : WS </wordStack> <program> ... DEST |-> OP ... </program> requires OP =/=K JUMPDEST andBool W =/=K 0

    rule <op> #badJumpDest? [ JUMP  ] => #exception ... </op> <wordStack> DEST :     WS </wordStack> <program> PGM </program> requires notBool (DEST in keys(PGM))
    rule <op> #badJumpDest? [ JUMPI ] => #exception ... </op> <wordStack> DEST : W : WS </wordStack> <program> PGM </program> requires (notBool (DEST in keys(PGM))) andBool W =/=K 0
```

### Execution Step

-   `#exec` will load the arguments of the opcode (it assumes `#stackNeeded?` is accurate and has been called) and trigger the subsequent operations.

```{.k .uiuck .rvk}
    syntax OpCodeOp ::= "#exec"
 // ---------------------------
    rule <op> #exec [ OP:InternalOp ] => #try (#gas [ OP ] ~> OP) ... </op>
```

Here we load the correct number of arguments from the `wordStack` based on the sort of the opcode.
Some of them require an argument to be interpereted as an address (modulo 160 bits), so the `#addr?` function performs that check.

```{.k .uiuck .rvk}
    syntax InternalOp ::= UnStackOp Word
                        | BinStackOp Word Word
                        | TernStackOp Word Word Word
                        | QuadStackOp Word Word Word Word
 // -----------------------------------------------------
    rule <op> #exec [ UOP:UnStackOp   => UOP #addr?(UOP, W0)          ] ... </op> <wordStack> W0 : WS                => WS </wordStack>
    rule <op> #exec [ BOP:BinStackOp  => BOP #addr?(BOP, W0) W1       ] ... </op> <wordStack> W0 : W1 : WS           => WS </wordStack>
    rule <op> #exec [ TOP:TernStackOp => TOP #addr?(TOP, W0) W1 W2    ] ... </op> <wordStack> W0 : W1 : W2 : WS      => WS </wordStack>
    rule <op> #exec [ QOP:QuadStackOp => QOP #addr?(QOP, W0) W1 W2 W3 ] ... </op> <wordStack> W0 : W1 : W2 : W3 : WS => WS </wordStack>

    syntax Word ::= "#addr?" "(" OpCode "," Word ")" [function]
 // -----------------------------------------------------------
    rule #addr?(BALANCE,      W) => #addr(W)
    rule #addr?(EXTCODESIZE,  W) => #addr(W)
    rule #addr?(EXTCODECOPY,  W) => #addr(W)
    rule #addr?(SELFDESTRUCT, W) => #addr(W)
    rule #addr?(OP, W) => W requires notBool OP in (SetItem(BALANCE) SetItem(EXTCODESIZE) SetItem(EXTCODECOPY) SetItem(SELFDESTRUCT))
```

`StackOp` is used for opcodes which require a large portion of the stack.

```{.k .uiuck .rvk}
    syntax InternalOp ::= StackOp WordStack
 // ---------------------------------------
    rule <op> #exec [ SO:StackOp => SO WS ] ... </op> <wordStack> WS </wordStack>
```

The `CallOp` opcodes all interperet their second argument as an address.

```{.k .uiuck .rvk}
    syntax InternalOp ::= CallSixOp Word Word      Word Word Word Word
                        | CallOp    Word Word Word Word Word Word Word
 // ------------------------------------------------------------------
    rule <op> #exec [ CSO:CallSixOp => CSO  W0 #addr(W1)    W2 W3 W4 W5 ] ... </op> <wordStack> W0 : W1 : W2 : W3 : W4 : W5 : WS      => WS </wordStack>
    rule <op> #exec [ CO:CallOp     => CO   W0 #addr(W1) W2 W3 W4 W5 W6 ] ... </op> <wordStack> W0 : W1 : W2 : W3 : W4 : W5 : W6 : WS => WS </wordStack>
```

-   `#gas` calculates how much gas this operation costs, and takes into account the memory consumed.

```{.k .uiuck .rvk}
    syntax OpCodeOp ::= "#gas"
 // --------------------------
```

```
    rule <op> #gas [ OP ] => #gas(OP) ~> #deductGas ... </op>

    syntax InternalOp ::= "#deductGas"
 // ----------------------------------
    rule <op> G:Int ~> #deductGas => .          ... </op> <gas> GAVAIL => GAVAIL -Int G </gas> requires GAVAIL >=Int G
    rule <op> G:Int ~> #deductGas => #exception ... </op> <gas> GAVAIL                  </gas> requires GAVAIL <Int G
```

### Program Counter

All operators except for `PUSH` and `JUMP*` increment the program counter by 1.
The arguments to `PUSH` must be skipped over (as they are inline), and the opcode `JUMP` already affects the program counter in the correct way.

-   `#pc` calculates the next program counter of the given operator.

```{.k .uiuck .rvk}
    syntax OpCodeOp ::= "#pc"
 // -------------------------
    rule <op> #pc [ OP         ] => . ... </op> <pc> PCOUNT => PCOUNT +Word 1           </pc> requires notBool (isPushOp(OP) orBool isJumpOp(OP))
    rule <op> #pc [ PUSH(N, _) ] => . ... </op> <pc> PCOUNT => PCOUNT +Word (1 +Word N) </pc> 
    rule <op> #pc [ OP         ] => . ... </op> requires isJumpOp(OP)

    syntax Bool ::= isJumpOp ( OpCode ) [function]
 // ----------------------------------------------
    rule isJumpOp(OP) => OP ==K JUMP orBool OP ==K JUMPI
```

### Substate Log

During execution of a transaction some things are recorded in the substate log (Section 6.1 in yellowpaper).
This is a right cons-list of `SubstateLogEntry` (which contains the account ID along with the specified portions of the `wordStack` and `localMem`).

```{.k .uiuck .rvk}
    syntax SubstateLogEntry ::= "{" Word "|" WordStack "|" WordStack "}"
 // --------------------------------------------------------------------
```

After executing a transaction, it's necessary to have the effect of the substate log recorded.

-   `#finalize` makes the substate log actually have an effect on the state.

```{.k .uiuck .rvk}
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

### Memory Consumption

Gas needs to be deducted when the maximum memory to a program increases, so
we track the maximum used so far.

```{.k .uiuck .rvk}
    syntax InternalOp ::= "#updateMemory"
 // -----------------------------------
    rule <op> NEWMEM:Int ~> #updateMemory => . ... </op>
         <memoryUsed> MU => maxInt(MU, NEWMEM) </memoryUsed>
```

```{.k .uiuck .rvk}
    syntax Set ::= "#consumesMem" [function]
    rule #consumesMem => ( SetItem(MSTORE) )

    syntax InternalOp ::= #times(Int)
    rule <op> M:Int ~> #times(N:Int) => M *Int N ... </op>

    syntax InternalOp ::= #memory ( OpCode )
 // ----------------------------------------
    rule <op> #memory(OP) => 0 ... </op> requires notBool (OP in #consumesMem)

    rule <op> #memory(MSTORE) => (INDEX +Int 32) up/Int 32 ... </op>
         <wordStack> INDEX : VALUE : WS </wordStack>
```

-   `#memoryUsageUpdate` is the function `M` in appendix H of the yellowpaper which helps track the memory used.

```{.k .uiuck .rvk}
    syntax Word ::= #memoryUsageUpdate ( Word , Word , Word ) [function]
 // --------------------------------------------------------------------
    rule #memoryUsageUpdate(S:Int, F:Int, 0)     => S
    rule #memoryUsageUpdate(S:Int, F:Int, L:Int) => maxWord(S, (F +Int L) up/Int 32)
```

EVM Programs
============

Lists of opcodes form programs.
Deciding if an opcode is in a list will be useful for modeling gas, and converting a program into a map of program-counter to opcode is useful for execution.

Note that `_in_` ignores the arguments to operators that are parametric.

```{.k .uiuck .rvk}
    syntax OpCodes ::= ".OpCodes" | OpCode ";" OpCodes
 // --------------------------------------------------

    syntax Map ::= #asMapOpCodes ( OpCodes )       [function]
                 | #asMapOpCodes ( Int , OpCodes ) [function, klabel(#asMapOpCodesAux)]
 // -----------------------------------------------------------------------------------
    rule #asMapOpCodes( OPS:OpCodes )         => #asMapOpCodes(0, OPS)
    rule #asMapOpCodes( N , .OpCodes )        => .Map
    rule #asMapOpCodes( N , OP:OpCode ; OCS ) => (N |-> OP) #asMapOpCodes(N +Int 1, OCS) requires notBool isPushOp(OP)
    rule #asMapOpCodes( N , PUSH(M, W) ; OCS) => (N |-> PUSH(M, W)) #asMapOpCodes(N +Int 1 +Int M, OCS)

    syntax OpCodes ::= #asOpCodes ( Map )       [function]
                     | #asOpCodes ( Int , Map ) [function, klabel(#asOpCodesAux)]
 // -----------------------------------------------------------------------------
    rule #asOpCodes(M) => #asOpCodes(0, M)
    rule #asOpCodes(N, .Map) => .OpCodes
    rule #asOpCodes(N, N |-> OP         M) => OP         ; #asOpCodes(N +Int 1,        M) requires notBool isPushOp(OP)
    rule #asOpCodes(N, N |-> PUSH(S, W) M) => PUSH(S, W) ; #asOpCodes(N +Int 1 +Int S, M)

    syntax Word ::= #sizeOpCodeMap ( Map ) [function]
 // -------------------------------------------------
    rule #sizeOpCodeMap(M) => #sizeWordStack(#asmOpCodes(#asOpCodes(M)))
```

EVM OpCodes
-----------

Each subsection has a different class of opcodes.
Organization is based roughly on what parts of the execution state are needed to compute the result of each operator.
This sometimes corresponds to the organization in the yellowpaper.

### Internal Operations

These are just used by the other operators for shuffling local execution state around on the EVM.

-   `#push` will push an element to the `wordStack` without any checks.
-   `#setStack_` will set the current stack to the given one.

```{.k .uiuck .rvk}
    syntax InternalOp ::= "#push" | "#setStack" WordStack
 // -----------------------------------------------------
    rule <op> W0:Word ~> #push => . ... </op> <wordStack> WS => W0 : WS </wordStack>
    rule <op> #setStack WS     => . ... </op> <wordStack> _  => WS      </wordStack>
```

-   `#newAccount_` allows declaring a new empty account with the given address (and assumes the rounding to 160 bits has already occured).

```{.k .uiuck .rvk}
    syntax InternalOp ::= "#newAccount" Word
 // ----------------------------------------
    rule <op> #newAccount ACCT => . ... </op>
         <activeAccounts> ACCTS </activeAccounts>
      requires ACCT in ACCTS

    rule <op> #newAccount ACCT => . ... </op>
         <activeAccounts> ACCTS (.Set => SetItem(ACCT)) </activeAccounts>
         <accounts>
           ( .Bag
          => <account>
               <acctID>  ACCT          </acctID>
               <balance> 0             </balance>
               <code>    .Map          </code>
               <storage> .Map          </storage>
               <acctMap> "nonce" |-> 0 </acctMap>
             </account>
           )
           ...
         </accounts>
      requires notBool ACCT in ACCTS
```

### Invalid Operator

```{.k .uiuck .rvk}
    syntax InvalidOp ::= "INVALID"
 // ------------------------------
```

### Stack Manipulations

Some operators don't calculate anything, they just push the stack around a bit.

```{.k .uiuck .rvk}
    syntax UnStackOp ::= "POP"
 // --------------------------
    rule <op> POP W => . ... </op>

    syntax StackOp ::= DUP ( Word ) | SWAP ( Word )
 // -----------------------------------------------
    rule <op> DUP(N)  WS:WordStack => #setStack ((WS [ N -Word 1 ]) : WS)                       ... </op>
    rule <op> SWAP(N) (W0 : WS)    => #setStack ((WS [ N -Word 1 ]) : (WS [ N -Word 1 := W0 ])) ... </op>

    syntax PushOp ::= PUSH ( Word , Word )
 // --------------------------------------
    rule <op> PUSH(_, W) => W ~> #push ... </op>
```

### Local Memory

These operations are getters/setters of the local execution memory.

```{.k .uiuck .rvk}
    syntax UnStackOp ::= "MLOAD"
 // ----------------------------
    rule <op> MLOAD INDEX => #asWord(#range(LM, INDEX, 32)) ~> #push ... </op>
         <localMem> LM </localMem>
         <memoryUsed> MU => maxInt(MU, (INDEX +Int 32) up/Int 32) </memoryUsed>

    syntax BinStackOp ::= "MSTORE" | "MSTORE8"
 // ------------------------------------------
    rule <op> MSTORE INDEX VALUE => . ... </op>
         <localMem> LM => LM [ INDEX := #padToWidth(32, #asByteStack(VALUE)) ] </localMem>

    rule <op> MSTORE8 INDEX VALUE => . ... </op>
         <localMem> LM => LM [ INDEX <- (VALUE %Int 256) ]    </localMem>
         <memoryUsed> MU => maxInt(MU, (INDEX +Int 1) up/Int 32) </memoryUsed>
```

### Expressions

Expression calculations are simple and don't require anything but the arguments from the `wordStack` to operate.

NOTE: We have to call the opcode `OR` by `EVMOR` instead, because K has trouble parsing it/compiling the definition otherwise.

```{.k .uiuck .rvk}
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

    syntax BinStackOp ::= "BYTE" | "SIGNEXTEND"
 // -------------------------------------------
    rule <op> BYTE INDEX W     => byte(INDEX, W)     ~> #push ... </op>
    rule <op> SIGNEXTEND W0 W1 => signextend(W0, W1) ~> #push ... </op>

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
    rule <op> SGT W0 W1 => W1 s<Word W0 ~> #push ... </op>

    syntax BinStackOp ::= "SHA3"
 // ----------------------------
    rule <op> SHA3 MEMSTART MEMWIDTH => keccak(#range(LM, MEMSTART, MEMWIDTH)) ~> #push ... </op>
         <localMem> LM </localMem>
         <memoryUsed> MU => #memoryUsageUpdate(MU, MEMSTART, MEMWIDTH) </memoryUsed>
```

### Local State

These operators make queries about the current execution state.

```{.k .uiuck .rvk}
    syntax NullStackOp ::= "PC" | "GAS" | "GASPRICE" | "GASLIMIT"
 // -------------------------------------------------------------
    rule <op> PC       => PCOUNT ~> #push ... </op> <pc> PCOUNT </pc>
    rule <op> GAS      => GAVAIL ~> #push ... </op> <gas> GAVAIL </gas>
    rule <op> GASPRICE => GPRICE ~> #push ... </op> <gasPrice> GPRICE </gasPrice>
    rule <op> GASLIMIT => GLIMIT ~> #push ... </op> <gasLimit> GLIMIT </gasLimit>

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
    rule <op> MSIZE    => 32 *Word MU    ~> #push ... </op> <memoryUsed> MU </memoryUsed>
    rule <op> CODESIZE => #sizeOpCodeMap(PGM) ~> #push ... </op> <program> PGM </program>

    syntax TernStackOp ::= "CODECOPY"
 // ---------------------------------
    rule <op> CODECOPY MEMSTART PGMSTART WIDTH => . ... </op>
         <program> PGM </program>
         <localMem> LM => LM [ MEMSTART := #asmOpCodes(#asOpCodes(PGM)) [ PGMSTART .. WIDTH ] ] </localMem>
         <memoryUsed> MU => #memoryUsageUpdate(MU, MEMSTART, WIDTH) </memoryUsed>

    syntax UnStackOp ::= "BLOCKHASH"
 // --------------------------------
    rule <op> BLOCKHASH N => keccak(N : .WordStack) ~> #push ... </op>
```

### `JUMP*`

The `JUMP*` family of operations affect the current program counter.

```{.k .uiuck .rvk}
    syntax NullStackOp ::= "JUMPDEST"
 // ------------------------------
    rule <op> JUMPDEST => . ... </op>

    syntax UnStackOp ::= "JUMP"
 // ---------------------------
    rule <op> JUMP DEST => . ... </op> <pc> _ => DEST </pc>

    syntax BinStackOp ::= "JUMPI"
 // -----------------------------
    rule <op> JUMPI DEST I => . ... </op> <pc> _ => DEST </pc> requires I =/=K 0
    rule <op> JUMPI DEST 0 => . ... </op>
```

### `STOP` and `RETURN`

```{.k .uiuck .rvk}
    syntax NullStackOp ::= "STOP"
 // -----------------------------
    rule <op> STOP ~> K => #end </op>

    syntax BinStackOp ::= "RETURN"
 // ------------------------------
    rule <op> RETURN RETSTART RETWIDTH => . ... </op>
         <output> _ => #range(LM, RETSTART, RETWIDTH) </output>
         <localMem> LM </localMem>
         <memoryUsed> MU => #memoryUsageUpdate(MU, RETSTART, RETWIDTH) </memoryUsed>
```

### Call Data

These operators query about the current `CALL*` state.

```{.k .uiuck .rvk}
    syntax NullStackOp ::= "CALLDATASIZE"
 // -------------------------------------
    rule <op> CALLDATASIZE => #sizeWordStack(CD) ~> #push ... </op>
         <callData> CD </callData>

    syntax UnStackOp ::= "CALLDATALOAD"
 // -----------------------------------
    rule <op> CALLDATALOAD DATASTART => #asWord(CD [ DATASTART .. 32 ]) ~> #push ... </op>
         <callData> CD </callData>

    syntax TernStackOp ::= "CALLDATACOPY"
 // -------------------------------------
    rule <op> CALLDATACOPY MEMSTART DATASTART DATAWIDTH => . ... </op>
         <localMem> LM => LM [ MEMSTART := CD [ DATASTART .. DATAWIDTH ] ] </localMem>
         <callData> CD </callData>
         <memoryUsed> MU => #memoryUsageUpdate(MU, MEMSTART, DATAWIDTH) </memoryUsed>
```

### Log Operations

```{.k .uiuck .rvk}
    syntax LogOp ::= LOG ( Word )
 // -----------------------------
    rule <op> LOG(N) => . ... </op>
         <id> ACCT </id>
         <wordStack> W0 : W1 : WS => #drop(N, WS) </wordStack>
         <localMem> LM </localMem>
         <memoryUsed> MU => #memoryUsageUpdate(MU, W0, W1) </memoryUsed>
         <log> ... (.Set => SetItem({ ACCT | #take(N, WS) | #range(LM, W0, W1) })) </log>
      requires word2Bool(#sizeWordStack(WS) >=Word N)
```

Ethereum Network OpCodes
------------------------

Operators that require access to the rest of the Ethereum network world-state can be taken as a first draft of a "blockchain generic" language.

### Account Queries

TODO: It's unclear what to do in the case of an account not existing for these operators.
`BALANCE` is specified to push 0 in this case, but the others are not specified.
For now, I assume that they instantiate an empty account and use the empty data.

```{.k .uiuck .rvk}
    syntax UnStackOp ::= "BALANCE"
 // ------------------------------
    rule <op> BALANCE ACCT => BAL ~> #push ... </op>
         <account>
           <acctID> ACCT </acctID>
           <balance> BAL </balance>
           ...
         </account>

    rule <op> BALANCE ACCT => #newAccount ACCT ~> 0 ~> #push ... </op>
         <activeAccounts> ACCTS </activeAccounts>
      requires notBool ACCT in ACCTS

    syntax UnStackOp ::= "EXTCODESIZE"
 // ----------------------------------
    rule <op> EXTCODESIZE ACCT => #sizeOpCodeMap(CODE) ~> #push ... </op>
         <account>
           <acctID> ACCT </acctID>
           <code> CODE </code>
           ...
         </account>

    rule <op> EXTCODESIZE ACCT => #newAccount ACCT ~> 0 ~> #push ... </op>
         <activeAccounts> ACCTS </activeAccounts>
      requires notBool ACCT in ACCTS
```

TODO: What should happen in the case that the account doesn't exist with `EXTCODECOPY`?
Should we pad zeros (for the copied "program")?

```{.k .uiuck .rvk}
    syntax QuadStackOp ::= "EXTCODECOPY"
 // ------------------------------------
    rule <op> EXTCODECOPY ACCT MEMSTART PGMSTART WIDTH => . ... </op>
         <localMem> LM => LM [ MEMSTART := #asmOpCodes(#asOpCodes(PGM)) [ PGMSTART .. WIDTH ] ] </localMem>
         <memoryUsed> MU => #memoryUsageUpdate(MU, MEMSTART, WIDTH) </memoryUsed>
         <account>
           <acctID> ACCT </acctID>
           <code> PGM </code>
           ...
         </account>

    rule <op> EXTCODECOPY ACCT MEMSTART PGMSTART WIDTH => #newAccount ACCT ... </op>
         <activeAccounts> ACCTS </activeAccounts>
      requires notBool ACCT in ACCTS
```

### Account Storage Operations

These operations interact with the account storage.

```{.k .uiuck .rvk}
    syntax UnStackOp ::= "SLOAD"
 // ----------------------------
    rule <op> SLOAD INDEX => 0 ~> #push ... </op>
         <id> ACCT </id>
         <account>
           <acctID> ACCT </acctID>
           <storage> STORAGE </storage>
           ...
         </account> requires notBool INDEX in keys(STORAGE)

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
         <id> ACCT </id>
         <account>
           <acctID> ACCT </acctID>
           <storage> ... (INDEX |-> VALUE => .Map) ... </storage>
           ...
         </account>
         <refund> R => R +Word Rsclear </refund>

    rule <op> SSTORE INDEX 0 => . ... </op>
         <id> ACCT </id>
         <account>
           <acctID> ACCT </acctID>
           <storage> STORAGE </storage>
           ...
         </account>
      requires notBool (INDEX in keys(STORAGE))

    rule <op> SSTORE INDEX VALUE => . ... </op>
         <id> ACCT </id>
         <account>
           <acctID> ACCT </acctID>
           <storage> STORAGE => STORAGE [ INDEX <- VALUE ] </storage>
           ...
         </account>
      requires VALUE =/=K 0
```

### Call Operations

The various `CALL*` (and other inter-contract control flow) operations will be desugared into these `InternalOp`s.

-   `#return__` is a placeholder for the calling program, specifying where to place the returned data in memory.

```{.k .uiuck .rvk}
    syntax InternalOp ::= "#return" Word Word
 // -----------------------------------------
    rule <op> #return RETSTART RETWIDTH => . ... </op>
         <output> OUT </output>
         <localMem> LM => LM [ RETSTART := #take(minWord(RETWIDTH, #sizeWordStack(OUT)), OUT) ] </localMem>
```

-   The `callLog` is used to store the `CALL*`/`CREATE` operations so that we can compare them against the test-set.

TODO: The `Call` sort needs to store the available gas to the `CALL*` as well, but we are not right now because gas calculation isn't finished.

```{.k .uiuck .rvk}
    syntax Call ::= "{" Word "|" Word "|" WordStack "}"
    syntax CallLog ::= ".CallLog" | Call ";" CallLog
 // ------------------------------------------------

    syntax Bool ::= Call "in" CallLog [function]
 // --------------------------------------------
    rule C      in .CallLog       => false
    rule C:Call in (C':Call ; CL) => C ==K C' orElseBool C in CL
```

-   `#call_____` takes the calling account, the account to execute as, the code to execute, the amount to transfer, and the arguments.

TODO: `#call` is neutured to make sure that we can pass the VMTests. The following is closer to what it should be.

```
    syntax InternalOp ::= "#call" Word Word Map Word WordStack
 // ----------------------------------------------------------
    rule <op> #call ACCTFROM ACCTTO CODE VALUE ARGS => . ... </op>
         <callDepth> CD => CD +Int 1 </callDepth>
         <callLog> CL => { ACCTTO | VALUE | ARGS } ; CL </callLog>
         <id>       _ => ACCTTO                </id>
         <pc>       _ => 0                     </pc>
         <caller>   _ => ACCTFROM              </caller>
         <localMem> _ => #WordStackAsMap(ARGS) </localMem>
         <program>  _ => CODE                  </program>
         <account>
           <acctID>  ACCTFROM </acctID>
           <balance> BAL => BAL -Word VALUE </balance>
           <acctMap> ... "nonce" |-> (NONCE => NONCE +Word 1) ... </acctMap>
           ...
         </account>
      requires word2Bool(VALUE <=Word BAL) andBool CD <Int 1024
```

Here is what we're actually using.
The test-set isn't clear about whach should happen when `#call` is run, but it seems that it should push `1` onto the stack.

```{.k .uiuck .rvk}
    syntax InternalOp ::= "#call" Word Word Map Word WordStack
 // ----------------------------------------------------------
    rule <op> #call ACCTFROM ACCTTO CODE VALUE ARGS => 1 ~> #push ... </op>
         <callDepth> CD </callDepth>
         <callLog> CL => { ACCTTO | VALUE | ARGS } ; CL </callLog>
         <account>
           <acctID>  ACCTFROM </acctID>
           <balance> BAL </balance>
           ...
         </account>
      requires word2Bool(VALUE <=Word BAL) andBool CD <Int 1024

    rule <op> #call ACCTFROM ACCTTO CODE VALUE ARGS => #exception ... </op>
         <account>
           <acctID> ACCTFROM </acctID>
           <balance> BAL </balance>
           ...
         </account>
      requires word2Bool(VALUE >Word BAL)

    rule <op> #call ACCTFROM ACCTTO CODE VALUE ARGS => #exception ... </op>
         <callDepth> CD </callDepth>
      requires CD >=Int 1024
```

For each `CALL*` operation, we make a corresponding call to `#call` and a state-change to setup the custom parts of the calling environment.

TODO: The `#catch` being used in each case needs to be filled in with the actual code to run on exception.

```{.k .uiuck .rvk}
    syntax CallOp ::= "CALL"
 // ------------------------
    rule <op> CALL GASCAP ACCTTO VALUE ARGSTART ARGWIDTH RETSTART RETWIDTH
           => #try ( #call ACCTFROM #addr(ACCTTO) CODE VALUE #range(LM, ARGSTART, ARGWIDTH)
                  ~> #return RETSTART RETWIDTH
                   )
           ...
         </op>
         <id> ACCTFROM </id>
         <localMem> LM </localMem>
         <memoryUsed> MU => #memoryUsageUpdate(#memoryUsageUpdate(MU, ARGSTART, ARGWIDTH), RETSTART, RETWIDTH) </memoryUsed>
         <account>
           <acctID> ACCTTO </acctID>
           <code> CODE </code>
           ...
         </account>

    syntax CallOp ::= "CALLCODE"
 // ----------------------------
    rule <op> CALLCODE GASCAP ACCTTO VALUE ARGSTART ARGWIDTH RETSTART RETWIDTH
           => #try ( #call ACCTFROM ACCTFROM CODE VALUE #range(LM, ARGSTART, ARGWIDTH)
                  ~> #return RETSTART RETWIDTH
                   )
           ...
         </op>
         <id> ACCTFROM </id>
         <localMem> LM </localMem>
         <memoryUsed> MU => #memoryUsageUpdate(#memoryUsageUpdate(MU, ARGSTART, ARGWIDTH), RETSTART, RETWIDTH) </memoryUsed>
         <account>
           <acctID> ACCTTO </acctID>
           <code> CODE </code>
           ...
         </account>

    syntax CallSixOp ::= "DELEGATECALL"
 // -----------------------------------
    rule <op> DELEGATECALL GASCAP ACCTTO ARGSTART ARGWIDTH RETSTART RETWIDTH
           => #try ( #call ACCTFROM ACCTFROM CODE 0 #range(LM, ARGSTART, ARGWIDTH)
                  ~> #return RETSTART RETWIDTH
                   )
           ...
         </op>
         <id> ACCTFROM </id>
         <localMem> LM </localMem>
         <memoryUsed> MU => #memoryUsageUpdate(#memoryUsageUpdate(MU, ARGSTART, ARGWIDTH), RETSTART, RETWIDTH) </memoryUsed>
         <account>
           <acctID> ACCTTO </acctID>
           <code> CODE </code>
           ...
         </account>
```

### Account Creation/Deletion

Code is allowed to create a new contract by using the `CREATE` instruction.
First, `#call` is used to execute the "initialization code", which returns the code of the newly created account.
On successful initialization, the output is the code to deposit in the account (done with `#codeDeposit`).
This process can fail in two places, either in the initialization code or in depositing the output code (so `#catch_` is provided for each).

TODO: The `#catch_` being used need to be filled in with actual code to run.

```{.k .uiuck .rvk}
    syntax TernStackOp ::= "CREATE"
 // -------------------------------
    rule <op> CREATE VALUE MEMSTART MEMWIDTH
           => #try ( #call ACCT #newAddr(ACCT, NONCE) #asMapOpCodes(#dasmOpCodes(#range(LM, MEMSTART, MEMWIDTH))) VALUE .WordStack
                  ~> #try #codeDeposit
                   )
          ...
         </op>
         <id> ACCT </id>
         <localMem> LM </localMem>
         <memoryUsed> MU => #memoryUsageUpdate(MU, MEMSTART, MEMWIDTH) </memoryUsed>
         <activeAccounts> ACCTS </activeAccounts>
         <account>
           <acctID> ACCT </acctID>
           <acctMap> ... "nonce" |-> NONCE ... </acctMap>
           ...
         </account>
```

-   `#codeDeposit` attempts to deposit code into the account being called (which requires gas to be spent).
-   `#newAddr` is a placeholder for the new address until we get the actual calculation setup.

TODO: Right now `#codeDeposit` isn't performing the correct gas check.
We should wait for the `#gas` calculations to be fixed before doing so.

```{.k .uiuck .rvk}
    syntax InternalOp  ::= "#codeDeposit"
 // -------------------------------------
    rule <op> #codeDeposit => . ... </op>
         <id> ACCT </id>
         <output> OUT => .WordStack </output>
         <account>
           <acctID> ACCT </acctID>
           <code> _ => #asMapOpCodes(#dasmOpCodes(OUT)) </code>
           ...
         </account>

    syntax Word ::= #newAddr ( Word , Word )
 // ----------------------------------------
```

`SELFDESTRUCT` marks the current account for deletion and transfers funds out of the current account.

```{.k .uiuck .rvk}
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
           <acctID> ACCTTO </acctID>
           <balance> BALTO => BALTO +Word BALFROM </balance>
           ...
         </account>

    rule <op> SELFDESTRUCT ACCTTO => #newAccount ACCTTO ... </op>
         <id> ACCT </id>
         <selfDestruct> SDS (.Set => SetItem(ACCT)) </selfDestruct>
         <refund> RF => #ifWord ACCT in SDS #then RF #else RF +Word Rself-destruct #fi </refund>
         <activeAccounts> ACCTS (.Set => SetItem(ACCTTO)) </activeAccounts>
         <account>
           <acctID> ACCT </acctID>
           <balance> BALFROM => 0 </balance>
           ...
         </account>
      requires notBool ACCTTO in ACCTS
```

Ethereum Gas Calculation
========================

The gas calculation is designed to mirror the style of the yellowpaper.

```{.k .uiuck .rvk}
    syntax Word ::= #gas ( OpCode )
 // -------------------------------
    rule <op> #gas(OP) => #if W1 =/=K 0 andBool notBool W0 in keys(STORAGE)
                          #then Gsset #else Gsreset #fi ... </op>
         <wordStack> W0 : W1 : WS </wordStack>
         <storage> STORAGE </storage>                  requires OP ==K SSTORE

    rule <op> #gas(OP) => Gexp ... </op>
         <wordStack> W0 : 0 : WS </wordStack>               requires OP ==K EXP
    rule <op> #gas(OP) => Gexp +Word (Gexpbyte *Word (1 +Word (log256Int(W1)))) ... </op>
         <wordStack> W0 : W1 : WS </wordStack>         requires OP ==K EXP andBool W1 =/=K 0

    rule <op> #gas(OP)         => Gsload     ... </op> requires OP ==K SLOAD

    rule <op> #gas(OP)         => Gzero      ... </op> requires OP in Wzero
    rule <op> #gas(OP)         => Gbase      ... </op> requires OP in Wbase
    rule <op> #gas(DUP(_))    => Gverylow   ... </op>
    rule <op> #gas(PUSH(_, _)) => Gverylow   ... </op>
    rule <op> #gas(SWAP(_))    => Gverylow   ... </op>
    rule <op> #gas(OP)         => Gverylow   ... </op> requires OP in Wverylow
    rule <op> #gas(OP)         => Glow       ... </op> requires OP in Wlow
    rule <op> #gas(OP)         => Gmid       ... </op> requires OP in Wmid
    rule <op> #gas(OP)         => Ghigh      ... </op> requires OP in Whigh
    rule <op> #gas(OP)         => Gextcode   ... </op> requires OP in Wextcode

    rule <op> #gas(OP)         => Gbalance   ... </op> requires OP ==K BALANCE
    rule <op> #gas(OP)         => Gblockhash ... </op> requires OP ==K BLOCKHASH

```

TODO: Gas calculation for the following operators is not implemented.

```{.k .uiuck .rvk}
    rule <op> #gas(OP)           => Gzero   ... </op> requires OP in Wcall
    rule <op> #gas(OP)           => Gzero   ... </op> requires OP ==K SELFDESTRUCT
    rule <op> #gas(OP)           => Gzero   ... </op> requires OP in Wcopy
    rule <op> #gas(OP)           => Gzero   ... </op> requires OP ==K EXTCODECOPY
    rule <op> #gas(LOG(N))       => Gzero   ... </op>
    rule <op> #gas(OP)           => Gzero   ... </op> requires OP ==K SHA3
    rule <op> #gas(OP)           => Gzero   ... </op> requires OP ==K JUMPDEST
    rule <op> #gas(OP)           => Gcreate ... </op> requires OP ==K CREATE
```

Here the lists of gas prices and gas opcodes are provided.

```{.k .uiuck .rvk}
    syntax Int ::= "Gzero"          [function] | "Gbase"          [function]
                 | "Gverylow"       [function] | "Glow"           [function]
                 | "Gmid"           [function] | "Ghigh"          [function]
                 | "Gextcode"       [function] | "Gbalance"       [function]
                 | "Gsload"         [function] | "Gjumpdest"      [function]
                 | "Gsset"          [function] | "Gsreset"        [function]
                 | "Rsclear"        [function] | "Rself-destruct" [function]
                 | "Gself-destruct" [function] | "Gcreate"        [function]
                 | "Gcodedeposit"   [function] | "Gcall"          [function]
                 | "Gcallvalue"     [function] | "Gcallstipend"   [function]
                 | "Gnewaccount"    [function] | "Gexp"           [function]
                 | "Gexpbyte"       [function] | "Gmemory"        [function]
                 | "Gtxcreate"      [function] | "Gtxdatazero"    [function]
                 | "Gtxdatanonzero" [function] | "Gtransaction"   [function]
                 | "Glog"           [function] | "Glogdata"       [function]
                 | "Glogtopic"      [function] | "Gsha3"          [function]
                 | "Gsha3word"      [function] | "Gcopy"          [function]
                 | "Gblockhash"     [function]
 // ------------------------------------------
    rule Gzero          => 0
    rule Gbase          => 2
    rule Gverylow       => 3
    rule Glow           => 5
    rule Gmid           => 8
    rule Ghigh          => 10
    rule Gextcode       => 700
    rule Gbalance       => 400
    rule Gsload         => 200
    rule Gjumpdest      => 1
    rule Gsset          => 20000
    rule Gsreset        => 5000
    rule Rsclear        => 15000
    rule Rself-destruct => 24000
    rule Gself-destruct => 5000
    rule Gcreate        => 32000
    rule Gcodedeposit   => 200
    rule Gcall          => 700
    rule Gcallvalue     => 9000
    rule Gcallstipend   => 2300
    rule Gnewaccount    => 25000
    rule Gexp           => 10
    rule Gexpbyte       => 10
    rule Gmemory        => 3
    rule Gtxcreate      => 32000
    rule Gtxdatazero    => 4
    rule Gtxdatanonzero => 68
    rule Gtransaction   => 21000
    rule Glog           => 375
    rule Glogdata       => 8
    rule Glogtopic      => 375
    rule Gsha3          => 30
    rule Gsha3word      => 6
    rule Gcopy          => 3
    rule Gblockhash     => 20

    syntax Set ::= "Wzero"    [function] | "Wbase" [function]
                 | "Wverylow" [function] | "Wlow"  [function]
                 | "Wmid"     [function] | "Whigh" [function]
                 | "Wextcode" [function] | "Wcall" [function]
                 | "Wcopy"    [function]
 // ------------------------------------
    rule Wzero    => (SetItem(STOP) SetItem(RETURN))
    rule Wbase    => ( SetItem(ADDRESS) SetItem(ORIGIN) SetItem(CALLER) SetItem(CALLVALUE) SetItem(CALLDATASIZE)
                       SetItem(CODESIZE) SetItem(GASPRICE) SetItem(COINBASE) SetItem(TIMESTAMP) SetItem(NUMBER)
                       SetItem(DIFFICULTY) SetItem(GASLIMIT) SetItem(POP) SetItem(PC) SetItem(MSIZE) SetItem(GAS)
                     )
    rule Wverylow => ( SetItem(ADD) SetItem(SUB) SetItem(NOT) SetItem(LT) SetItem(GT) SetItem(SLT) SetItem(SGT)
                       SetItem(EQ) SetItem(ISZERO) SetItem(AND) SetItem(EVMOR) SetItem(XOR) SetItem(BYTE)
                       SetItem(CALLDATALOAD) SetItem(MLOAD) SetItem(MSTORE) SetItem(MSTORE8)
                     )
    rule Wlow     => (SetItem(MUL) SetItem(DIV) SetItem(SDIV) SetItem(MOD) SetItem(SMOD) SetItem(SIGNEXTEND))
    rule Wmid     => (SetItem(ADDMOD) SetItem(MULMOD) SetItem(JUMP))
    rule Whigh    => (SetItem(JUMPI))
    rule Wextcode => (SetItem(EXTCODESIZE))
    rule Wcopy    => (SetItem(CALLDATACOPY) SetItem(CODECOPY))
    rule Wcall    => (SetItem(CALL) SetItem(CALLCODE) SetItem(DELEGATECALL))
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

-   `#dasmOpCodes` interperets `WordStack` as an `OpCodes`.
-   `#dasmPUSH` handles the case of a `PushOp`.
-   `#dasmOpCode` interperets a `Word` as an `OpCode`.

```{.k .uiuck .rvk}
    syntax OpCodes ::= #dasmOpCodes ( WordStack ) [function]
 // --------------------------------------------------------
    rule #dasmOpCodes( .WordStack ) => .OpCodes
    rule #dasmOpCodes( W : WS )     => #dasmOpCode(W)    ; #dasmOpCodes(WS) requires word2Bool(W >=Word 0)   andBool word2Bool(W <=Word 95)
    rule #dasmOpCodes( W : WS )     => #dasmOpCode(W)    ; #dasmOpCodes(WS) requires word2Bool(W >=Word 240) andBool word2Bool(W <=Word 255)
    rule #dasmOpCodes( W : WS )     => DUP(W -Word 127)  ; #dasmOpCodes(WS) requires word2Bool(W >=Word 128) andBool word2Bool(W <=Word 143)
    rule #dasmOpCodes( W : WS )     => SWAP(W -Word 143) ; #dasmOpCodes(WS) requires word2Bool(W >=Word 144) andBool word2Bool(W <=Word 159)
    rule #dasmOpCodes( W : WS )     => LOG(W -Word 160)  ; #dasmOpCodes(WS) requires word2Bool(W >=Word 160) andBool word2Bool(W <=Word 164)
    rule #dasmOpCodes( W : WS )     => #dasmPUSH( W -Word 95 , WS )         requires word2Bool(W >=Word 96)  andBool word2Bool(W <=Word 127)

    syntax OpCodes ::= #dasmPUSH ( Word , WordStack ) [function]
 // ------------------------------------------------------------
    rule #dasmPUSH( W , WS ) => PUSH(W, #asWord(#take(W, WS))) ; #dasmOpCodes(#drop(W, WS))

    syntax OpCode ::= #dasmOpCode ( Word ) [function]
 // -------------------------------------------------
    rule #dasmOpCode(   0 ) => STOP
    rule #dasmOpCode(   1 ) => ADD
    rule #dasmOpCode(   2 ) => MUL
    rule #dasmOpCode(   3 ) => SUB
    rule #dasmOpCode(   4 ) => DIV
    rule #dasmOpCode(   5 ) => SDIV
    rule #dasmOpCode(   6 ) => MOD
    rule #dasmOpCode(   7 ) => SMOD
    rule #dasmOpCode(   8 ) => ADDMOD
    rule #dasmOpCode(   9 ) => MULMOD
    rule #dasmOpCode(  10 ) => EXP
    rule #dasmOpCode(  11 ) => SIGNEXTEND
    rule #dasmOpCode(  16 ) => LT
    rule #dasmOpCode(  17 ) => GT
    rule #dasmOpCode(  18 ) => SLT
    rule #dasmOpCode(  19 ) => SGT
    rule #dasmOpCode(  20 ) => EQ
    rule #dasmOpCode(  21 ) => ISZERO
    rule #dasmOpCode(  22 ) => AND
    rule #dasmOpCode(  23 ) => EVMOR
    rule #dasmOpCode(  24 ) => XOR
    rule #dasmOpCode(  25 ) => NOT
    rule #dasmOpCode(  26 ) => BYTE
    rule #dasmOpCode(  32 ) => SHA3
    rule #dasmOpCode(  48 ) => ADDRESS
    rule #dasmOpCode(  49 ) => BALANCE
    rule #dasmOpCode(  50 ) => ORIGIN
    rule #dasmOpCode(  51 ) => CALLER
    rule #dasmOpCode(  52 ) => CALLVALUE
    rule #dasmOpCode(  53 ) => CALLDATALOAD
    rule #dasmOpCode(  54 ) => CALLDATASIZE
    rule #dasmOpCode(  55 ) => CALLDATACOPY
    rule #dasmOpCode(  56 ) => CODESIZE
    rule #dasmOpCode(  57 ) => CODECOPY
    rule #dasmOpCode(  58 ) => GASPRICE
    rule #dasmOpCode(  59 ) => EXTCODESIZE
    rule #dasmOpCode(  60 ) => EXTCODECOPY
    rule #dasmOpCode(  64 ) => BLOCKHASH
    rule #dasmOpCode(  65 ) => COINBASE
    rule #dasmOpCode(  66 ) => TIMESTAMP
    rule #dasmOpCode(  67 ) => NUMBER
    rule #dasmOpCode(  68 ) => DIFFICULTY
    rule #dasmOpCode(  69 ) => GASLIMIT
    rule #dasmOpCode(  80 ) => POP
    rule #dasmOpCode(  81 ) => MLOAD
    rule #dasmOpCode(  82 ) => MSTORE
    rule #dasmOpCode(  83 ) => MSTORE8
    rule #dasmOpCode(  84 ) => SLOAD
    rule #dasmOpCode(  85 ) => SSTORE
    rule #dasmOpCode(  86 ) => JUMP
    rule #dasmOpCode(  87 ) => JUMPI
    rule #dasmOpCode(  88 ) => PC
    rule #dasmOpCode(  89 ) => MSIZE
    rule #dasmOpCode(  90 ) => GAS
    rule #dasmOpCode(  91 ) => JUMPDEST
    rule #dasmOpCode( 240 ) => CREATE
    rule #dasmOpCode( 241 ) => CALL
    rule #dasmOpCode( 242 ) => CALLCODE
    rule #dasmOpCode( 243 ) => RETURN
    rule #dasmOpCode( 244 ) => DELEGATECALL
    rule #dasmOpCode( 254 ) => INVALID
    rule #dasmOpCode( 255 ) => SELFDESTRUCT
```

Assembler
---------

-   `#asmOpCodes` gives the `WordStack` representation of an `OpCodes`.

```{.k .uiuck .rvk}
    syntax WordStack ::= #asmOpCodes ( OpCodes ) [function]
 // -------------------------------------------------------
    rule #asmOpCodes( .OpCodes )           => .WordStack
    rule #asmOpCodes( STOP         ; OPS ) =>   0 : #asmOpCodes(OPS)
    rule #asmOpCodes( ADD          ; OPS ) =>   1 : #asmOpCodes(OPS)
    rule #asmOpCodes( MUL          ; OPS ) =>   2 : #asmOpCodes(OPS)
    rule #asmOpCodes( SUB          ; OPS ) =>   3 : #asmOpCodes(OPS)
    rule #asmOpCodes( DIV          ; OPS ) =>   4 : #asmOpCodes(OPS)
    rule #asmOpCodes( SDIV         ; OPS ) =>   5 : #asmOpCodes(OPS)
    rule #asmOpCodes( MOD          ; OPS ) =>   6 : #asmOpCodes(OPS)
    rule #asmOpCodes( SMOD         ; OPS ) =>   7 : #asmOpCodes(OPS)
    rule #asmOpCodes( ADDMOD       ; OPS ) =>   8 : #asmOpCodes(OPS)
    rule #asmOpCodes( MULMOD       ; OPS ) =>   9 : #asmOpCodes(OPS)
    rule #asmOpCodes( EXP          ; OPS ) =>  10 : #asmOpCodes(OPS)
    rule #asmOpCodes( SIGNEXTEND   ; OPS ) =>  11 : #asmOpCodes(OPS)
    rule #asmOpCodes( LT           ; OPS ) =>  16 : #asmOpCodes(OPS)
    rule #asmOpCodes( GT           ; OPS ) =>  17 : #asmOpCodes(OPS)
    rule #asmOpCodes( SLT          ; OPS ) =>  18 : #asmOpCodes(OPS)
    rule #asmOpCodes( SGT          ; OPS ) =>  19 : #asmOpCodes(OPS)
    rule #asmOpCodes( EQ           ; OPS ) =>  20 : #asmOpCodes(OPS)
    rule #asmOpCodes( ISZERO       ; OPS ) =>  21 : #asmOpCodes(OPS)
    rule #asmOpCodes( AND          ; OPS ) =>  22 : #asmOpCodes(OPS)
    rule #asmOpCodes( EVMOR        ; OPS ) =>  23 : #asmOpCodes(OPS)
    rule #asmOpCodes( XOR          ; OPS ) =>  24 : #asmOpCodes(OPS)
    rule #asmOpCodes( NOT          ; OPS ) =>  25 : #asmOpCodes(OPS)
    rule #asmOpCodes( BYTE         ; OPS ) =>  26 : #asmOpCodes(OPS)
    rule #asmOpCodes( SHA3         ; OPS ) =>  32 : #asmOpCodes(OPS)
    rule #asmOpCodes( ADDRESS      ; OPS ) =>  48 : #asmOpCodes(OPS)
    rule #asmOpCodes( BALANCE      ; OPS ) =>  49 : #asmOpCodes(OPS)
    rule #asmOpCodes( ORIGIN       ; OPS ) =>  50 : #asmOpCodes(OPS)
    rule #asmOpCodes( CALLER       ; OPS ) =>  51 : #asmOpCodes(OPS)
    rule #asmOpCodes( CALLVALUE    ; OPS ) =>  52 : #asmOpCodes(OPS)
    rule #asmOpCodes( CALLDATALOAD ; OPS ) =>  53 : #asmOpCodes(OPS)
    rule #asmOpCodes( CALLDATASIZE ; OPS ) =>  54 : #asmOpCodes(OPS)
    rule #asmOpCodes( CALLDATACOPY ; OPS ) =>  55 : #asmOpCodes(OPS)
    rule #asmOpCodes( CODESIZE     ; OPS ) =>  56 : #asmOpCodes(OPS)
    rule #asmOpCodes( CODECOPY     ; OPS ) =>  57 : #asmOpCodes(OPS)
    rule #asmOpCodes( GASPRICE     ; OPS ) =>  58 : #asmOpCodes(OPS)
    rule #asmOpCodes( EXTCODESIZE  ; OPS ) =>  59 : #asmOpCodes(OPS)
    rule #asmOpCodes( EXTCODECOPY  ; OPS ) =>  60 : #asmOpCodes(OPS)
    rule #asmOpCodes( BLOCKHASH    ; OPS ) =>  64 : #asmOpCodes(OPS)
    rule #asmOpCodes( COINBASE     ; OPS ) =>  65 : #asmOpCodes(OPS)
    rule #asmOpCodes( TIMESTAMP    ; OPS ) =>  66 : #asmOpCodes(OPS)
    rule #asmOpCodes( NUMBER       ; OPS ) =>  67 : #asmOpCodes(OPS)
    rule #asmOpCodes( DIFFICULTY   ; OPS ) =>  68 : #asmOpCodes(OPS)
    rule #asmOpCodes( GASLIMIT     ; OPS ) =>  69 : #asmOpCodes(OPS)
    rule #asmOpCodes( POP          ; OPS ) =>  80 : #asmOpCodes(OPS)
    rule #asmOpCodes( MLOAD        ; OPS ) =>  81 : #asmOpCodes(OPS)
    rule #asmOpCodes( MSTORE       ; OPS ) =>  82 : #asmOpCodes(OPS)
    rule #asmOpCodes( MSTORE8      ; OPS ) =>  83 : #asmOpCodes(OPS)
    rule #asmOpCodes( SLOAD        ; OPS ) =>  84 : #asmOpCodes(OPS)
    rule #asmOpCodes( SSTORE       ; OPS ) =>  85 : #asmOpCodes(OPS)
    rule #asmOpCodes( JUMP         ; OPS ) =>  86 : #asmOpCodes(OPS)
    rule #asmOpCodes( JUMPI        ; OPS ) =>  87 : #asmOpCodes(OPS)
    rule #asmOpCodes( PC           ; OPS ) =>  88 : #asmOpCodes(OPS)
    rule #asmOpCodes( MSIZE        ; OPS ) =>  89 : #asmOpCodes(OPS)
    rule #asmOpCodes( GAS          ; OPS ) =>  90 : #asmOpCodes(OPS)
    rule #asmOpCodes( JUMPDEST     ; OPS ) =>  91 : #asmOpCodes(OPS)
    rule #asmOpCodes( CREATE       ; OPS ) => 240 : #asmOpCodes(OPS)
    rule #asmOpCodes( CALL         ; OPS ) => 241 : #asmOpCodes(OPS)
    rule #asmOpCodes( CALLCODE     ; OPS ) => 242 : #asmOpCodes(OPS)
    rule #asmOpCodes( RETURN       ; OPS ) => 243 : #asmOpCodes(OPS)
    rule #asmOpCodes( DELEGATECALL ; OPS ) => 244 : #asmOpCodes(OPS)
    rule #asmOpCodes( INVALID      ; OPS ) => 254 : #asmOpCodes(OPS)
    rule #asmOpCodes( SELFDESTRUCT ; OPS ) => 255 : #asmOpCodes(OPS)
    rule #asmOpCodes( DUP(W)       ; OPS ) => W +Word 127 : #asmOpCodes(OPS)
    rule #asmOpCodes( SWAP(W)      ; OPS ) => W +Word 143 : #asmOpCodes(OPS)
    rule #asmOpCodes( LOG(W)       ; OPS ) => W +Word 160 : #asmOpCodes(OPS)
    rule #asmOpCodes( PUSH(N, W)   ; OPS ) => N +Word 95  : (#padToWidth(N, #asByteStack(W)) ++ #asmOpCodes(OPS))
endmodule
```
