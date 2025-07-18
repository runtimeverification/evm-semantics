EVM Execution
=============

### Overview

The EVM is a stack machine over some simple opcodes.
Most of the opcodes are "local" to the execution state of the machine, but some of them must interact with the world state.
This file only defines the local execution operations, the file `driver.md` will define the interactions with the world state.

```k
requires "data.md"
requires "network.md"
requires "gas.md"
requires "kllvm.k"

module EVM
    imports STRING
    imports EVM-DATA
    imports NETWORK
    imports GAS
    imports KLLVM
```

Configuration
-------------

The configuration has cells for the current account id, the current opcode, the program counter, the current gas, the gas price, the current program, the word stack, and the local memory.
In addition, there are cells for the callstack and execution substate.

We've broken up the configuration into two components; those parts of the state that mutate during execution of a single transaction and those that are static throughout.
In the comments next to each cell, we've marked which component of the YellowPaper state corresponds to each cell.

```k
    configuration
        <k> #loadProgram($PGM:Bytes) ~> #precompiled?($ACCTCODE:Int, getSchedule($SCHEDULE:Int)) ~> #execute </k>
        <exit-code exit=""> 1 </exit-code>
        <schedule> getSchedule($SCHEDULE:Int) </schedule>

        <ethereum>

          // EVM Specific
          // ============

          <evm>

            // Mutable during a single transaction
            // -----------------------------------

            <output>          .Bytes      </output>           // H_RETURN
            <statusCode>      .StatusCode </statusCode>
            <callStack>       .List       </callStack>

            <callState>
              <program>   .Bytes </program>
              <jumpDests> .Bytes </jumpDests>

              // I_*
              <id>        Int2MInt($ID:Int)::MInt{256}        </id>        // I_a
              <caller>    Int2MInt($CALLER:Int)::MInt{256}    </caller>    // I_s
              <callData>  $CALLDATA:Bytes                     </callData>  // I_d
              <callValue> Int2MInt($CALLVALUE:Int)::MInt{256} </callValue> // I_v

              // \mu_*
              <wordStack>   .List  </wordStack>           // \mu_s
              <localMem>    .Bytes </localMem>            // \mu_m
              <pc>          0p256  </pc>                  // \mu_pc
              <gas>         $GAS:Gas </gas>               // \mau_g
              <memoryUsed>  0      </memoryUsed>          // \mu_i
              <callGas>     0:Gas  </callGas>

              <static>    $STATIC:Bool </static>
              <callDepth> 0     </callDepth>
            </callState>
          </evm>
        </ethereum>
```

For symbolic execution, we create an additional cell, to capture the
side-effects of impure hooks.

```symbolic
        <symbolicWorldState> .SymbolicWorldState </symbolicWorldState>

    syntax SymbolicWorldState ::= ".SymbolicWorldState" [function, total]
    rule <k> WS:SymbolicWorldState => .K ... </k>
         <symbolicWorldState> _ => WS </symbolicWorldState>
```

```k
    syntax EthereumSimulation
 // -------------------------
```

Output Extraction
-----------------

```k
    rule getStatus(<generatedTop>... <statusCode> STATUS:StatusCode </statusCode> ...</generatedTop>) => getStatus(STATUS)

    syntax Int ::= getStatus(StatusCode) [function]
    rule getStatus(EVMC_REJECTED) => EVMC_REJECTED
    rule getStatus(EVMC_INTERNAL_ERROR) => EVMC_INTERNAL_ERROR
    rule getStatus(EVMC_SUCCESS) => EVMC_SUCCESS
    rule getStatus(EVMC_REVERT) => EVMC_REVERT
    rule getStatus(EVMC_FAILURE) => EVMC_FAILURE
    rule getStatus(EVMC_INVALID_INSTRUCTION) => EVMC_INVALID_INSTRUCTION
    rule getStatus(EVMC_UNDEFINED_INSTRUCTION) => EVMC_UNDEFINED_INSTRUCTION
    rule getStatus(EVMC_OUT_OF_GAS) => EVMC_OUT_OF_GAS
    rule getStatus(EVMC_BAD_JUMP_DESTINATION) => EVMC_BAD_JUMP_DESTINATION
    rule getStatus(EVMC_STACK_OVERFLOW) => EVMC_STACK_OVERFLOW
    rule getStatus(EVMC_STACK_UNDERFLOW) => EVMC_STACK_UNDERFLOW
    rule getStatus(EVMC_CALL_DEPTH_EXCEEDED) => EVMC_CALL_DEPTH_EXCEEDED
    rule getStatus(EVMC_INVALID_MEMORY_ACCESS) => EVMC_INVALID_MEMORY_ACCESS
    rule getStatus(EVMC_STATIC_MODE_VIOLATION) => EVMC_STATIC_MODE_VIOLATION
    rule getStatus(EVMC_PRECOMPILE_FAILURE) => EVMC_PRECOMPILE_FAILURE
    rule getStatus(EVMC_NONCE_EXCEEDED) => EVMC_NONCE_EXCEEDED

    rule getGasLeft(G) => 0 requires getStatus(G) =/=Int EVMC_SUCCESS andBool getStatus(G) =/=Int EVMC_REVERT
    rule getGasLeft(<generatedTop>... <gas> G </gas> ...</generatedTop>) => G [priority(51)]

    rule getOutput(G) => .Bytes requires getStatus(G) =/=Int EVMC_SUCCESS andBool getStatus(G) =/=Int EVMC_REVERT
    rule getOutput(<generatedTop>... <output> O </output> ...</generatedTop>) => O [priority(51)]
```

### The CallStack

The `callStack` cell stores a list of previous VM execution states.

-   `#pushCallStack` saves a copy of VM execution state on the `callStack`.
-   `#popCallStack` restores the top element of the `callStack`.
-   `#dropCallStack` removes the top element of the `callStack`.

```k
    syntax InternalOp ::= "#pushCallStack"
 // --------------------------------------
    rule <k> #pushCallStack => .K ... </k>
         <callStack> STACK => ListItem(<callState> CALLSTATE </callState>) STACK </callStack>
         <callState> CALLSTATE </callState>

    syntax InternalOp ::= "#popCallStack"
 // -------------------------------------
    rule <k> #popCallStack => .K ... </k>
         <callStack> ListItem(<callState> CALLSTATE </callState>) REST => REST </callStack>
         <callState> _ => CALLSTATE </callState>

    syntax InternalOp ::= "#dropCallStack"
 // --------------------------------------
    rule <k> #dropCallStack => .K ... </k>
         <callStack> ListItem(_) REST => REST </callStack>
```

### The StateStack

- In this version that StateStack call hooks to GEth callbacks that save or restore a snapshot of the world state.

-   `#pushWorldState` save the current snapshot of the world state.
-   `#popWorldState` restores Nth snapshot of the world state.
-   `#dropWorldState` removes the last number of snapshots of the world state. It doesn't affect the state jornal. We follow this convention as GETh never decrease the size of its journal orinally.

```k
    syntax InternalOp ::= "#pushWorldState"
 // ---------------------------------------
    rule <k> #pushWorldState => PushState() ... </k>

    syntax InternalOp ::= "#popWorldState"
 // --------------------------------------
    rule <k> #popWorldState => RollbackState() ... </k>

    syntax InternalOp ::= "#dropWorldState"
 // ---------------------------------------
    rule <k> #dropWorldState => CommitState() ... </k>
```
Control Flow
------------

### Exception Based

-   `#halt` indicates end of execution.
    It will consume anything related to the current computation behind it on the `<k>` cell.
-   `#end_` sets the `statusCode` and the program counter of the last executed opcode, then halts execution.

```k
    syntax KItem ::= "#halt"           [symbol(halt)]
                   | "#end" StatusCode [symbol(end) ]
 // -------------------------------------------------
    rule [end]:
         <k> #end SC => #halt ... </k>
         <statusCode> _ => SC </statusCode>

    rule <k> #halt ~> (_:Int    => .K) ... </k>
    rule <k> #halt ~> (_:OpCode => .K) ... </k>
```

OpCode Execution
----------------

### Execution Macros

-   `#lookupOpCode` reads an `OpCode` from the program `Bytes` if the program-counter is within the bounds of the program, meaning that it points to an actual opcode.
    It will return `.NoOpCode` otherwise.

```k
    syntax MaybeOpCode ::= ".NoOpCode" | OpCode

    syntax MaybeOpCode ::= "#lookupOpCode" "(" Bytes "," MInt{256} "," Schedule ")" [function, total]
 // -------------------------------------------------------------------------------------------------
    rule #lookupOpCode(BA, I, SCHED) => #dasmOpCode(BA[I], SCHED) requires 0p256 <=uMInt I andBool I <uMInt lengthBytes(BA)
    rule #lookupOpCode(_, _, _)  => .NoOpCode [owise]
```

-   `#execute` loads the next opcode.

```k
    syntax KItem ::= "#execute" [symbol(execute)]
 // ---------------------------------------------
    rule [halt]:
         <k> #halt ~> (#execute => .K) ... </k>

    rule [step]:
         <k> (.K => #next [ #lookupOpCode(PGM, PCOUNT, SCHED) ]) ~> #execute ... </k>
         <program> PGM </program>
         <pc> PCOUNT </pc>
         <schedule> SCHED </schedule>
```

### Single Step

If the program-counter points to an actual opcode, it's loaded into the `#next [_]` operator.
If `.NoOpCode` is loaded into `#next [_]`, then it means that there is no next opcode and the execution will halt with an `EVMC_SUCCESS` status code.
The `#next [_]` operator initiates execution by:

1.  checking if there will be a stack over/underflow, or a static mode violation,
2.  calculate any address conversions needed for items on the wordstack,
3.  executing the opcode (which includes any gas deduction needed), and
4.  adjusting the program counter.

```k
    syntax InternalOp ::= "#next" "[" MaybeOpCode "]"
 // -------------------------------------------------
    rule <k> #next [ .NoOpCode ] => #end EVMC_SUCCESS ... </k>
         <output> _ => .Bytes </output>

    rule <k> #next [ OP:OpCode ]
          => #addr [ OP ]
          ~> #exec [ OP ]
          ~> #pc   [ OP ]
         ...
         </k>
         <wordStack> WS </wordStack>
         <static> STATIC:Bool </static>
      requires notBool ( #stackUnderflow(WS, OP) orBool #stackOverflow(WS, OP) )
       andBool notBool ( STATIC andBool #changesState(OP, WS) )

    rule <k> #next [ OP ] => #end EVMC_STACK_UNDERFLOW ... </k>
         <wordStack> WS </wordStack>
      requires #stackUnderflow(WS, OP)

    rule <k> #next [ OP ] => #end EVMC_STACK_OVERFLOW ... </k>
         <wordStack> WS </wordStack>
      requires #stackOverflow(WS, OP)

    rule <k> #next [ OP ] => #end EVMC_STATIC_MODE_VIOLATION ... </k>
         <wordStack> WS </wordStack>
         <static> STATIC:Bool </static>
      requires STATIC andBool #changesState(OP, WS)
       andBool notBool ( #stackUnderflow(WS, OP) orBool #stackOverflow(WS, OP) )
```

### Exceptional Checks

-   `#stackNeeded` is how many arguments that opcode will need off the top of the stack.
-   `#stackAdded` is how many arguments that opcode will push onto the top of the stack.
-   `#stackDelta` is the delta the stack will have after the opcode executes.

```k
    syntax Bool ::= #stackUnderflow ( List , OpCode ) [symbol(#stackUnderflow), macro]
                  | #stackOverflow  ( List , OpCode ) [symbol(#stackOverflow), macro]
 // ----------------------------------------------------------------------------------
    rule #stackUnderflow(WS, OP:OpCode) => size(WS) <Int #stackNeeded(OP)
    rule #stackOverflow (WS, OP) => size(WS) +Int #stackDelta(OP) >Int 1024

    syntax Int ::= #stackNeeded ( OpCode ) [symbol(#stackNeeded), function]
 // -----------------------------------------------------------------------
    rule #stackNeeded(_POP:PushOp)      => 0
    rule #stackNeeded(_IOP:InvalidOp)   => 0
    rule #stackNeeded(_NOP:NullStackOp) => 0
    rule #stackNeeded(_UOP:UnStackOp)   => 1
    rule #stackNeeded(BOP:BinStackOp)   => 2 requires notBool isLogOp(BOP)
    rule #stackNeeded(_TOP:TernStackOp) => 3
    rule #stackNeeded(_QOP:QuadStackOp) => 4
    rule #stackNeeded(DUP(N))           => N
    rule #stackNeeded(SWAP(N))          => N +Int 1
    rule #stackNeeded(LOG(N))           => N +Int 2
    rule #stackNeeded(_CSOP:CallSixOp)  => 6
    rule #stackNeeded(COP:CallOp)       => 7 requires notBool isCallSixOp(COP)

    syntax Int ::= #stackAdded ( OpCode ) [symbol(#stackAdded), function]
 // ---------------------------------------------------------------------
    rule #stackAdded(CALLDATACOPY)   => 0
    rule #stackAdded(RETURNDATACOPY) => 0
    rule #stackAdded(CODECOPY)       => 0
    rule #stackAdded(EXTCODECOPY)    => 0
    rule #stackAdded(POP)            => 0
    rule #stackAdded(MSTORE)         => 0
    rule #stackAdded(MSTORE8)        => 0
    rule #stackAdded(SSTORE)         => 0
    rule #stackAdded(JUMP)           => 0
    rule #stackAdded(JUMPI)          => 0
    rule #stackAdded(JUMPDEST)       => 0
    rule #stackAdded(STOP)           => 0
    rule #stackAdded(RETURN)         => 0
    rule #stackAdded(REVERT)         => 0
    rule #stackAdded(SELFDESTRUCT)   => 0
    rule #stackAdded(PUSH(_))        => 1
    rule #stackAdded(LOG(_))         => 0
    rule #stackAdded(SWAP(N))        => N +Int 1
    rule #stackAdded(DUP(N))         => N +Int 1
    rule #stackAdded(_IOP:InvalidOp) => 0
    rule #stackAdded(_OP)            => 1 [owise]

    syntax Int ::= #stackDelta ( OpCode ) [symbol(#stackDelta), function]
 // ---------------------------------------------------------------------
    rule #stackDelta(OP) => #stackAdded(OP) -Int #stackNeeded(OP)
```

-   `#changesState` is true if the given opcode will change `<network>` state given the arguments.

```k
    syntax Bool ::= #changesState ( OpCode , List ) [symbol(#changesState), total, function]
 // ---------------------------------------------------------------------------------
```

```k
    rule #changesState(CALL         , ListItem(_) ListItem(_) ListItem(VALUE) _) => true  requires VALUE =/=MInt 0p256
    rule #changesState(LOG(_)       , _)                 => true
    rule #changesState(SSTORE       , _)                 => true
    rule #changesState(CREATE       , _)                 => true
    rule #changesState(CREATE2      , _)                 => true
    rule #changesState(SELFDESTRUCT , _)                 => true
    rule #changesState(TSTORE       , _)                 => true
    rule #changesState(_            , _)                 => false [owise]
```

### Execution Step

-   `#exec` will load the arguments of the opcode (it assumes `#stackNeeded?` is accurate and has been called) and trigger the subsequent operations.

```k
    syntax InternalOp ::= "#exec" "[" OpCode "]"
 // --------------------------------------------
    rule <k> #exec [ IOP:InvalidOp ] => IOP ... </k>

    rule <k> #exec [ OP ] => #gas [ OP , OP ] ~> OP ... </k> requires isNullStackOp(OP) orBool isPushOp(OP)
```

Here we load the correct number of arguments from the `wordStack` based on the sort of the opcode.

```k
    syntax KItem  ::= OpCode
    syntax OpCode ::= NullStackOp | UnStackOp | BinStackOp | TernStackOp | QuadStackOp
                    | InvalidOp | StackOp | InternalOp | CallOp | CallSixOp | PushOp
 // --------------------------------------------------------------------------------

    syntax InternalOp ::= UnStackOp   MInt{256}
                        | BinStackOp  MInt{256} MInt{256}
                        | TernStackOp MInt{256} MInt{256} MInt{256}
                        | QuadStackOp MInt{256} MInt{256} MInt{256} MInt{256}
 // -------------------------------------------------------------------------
    rule <k> #exec [ UOP:UnStackOp   ] => #gas [ UOP , UOP W0          ] ~> UOP W0          ... </k> <wordStack> ListItem(W0) => .List ...</wordStack>
    rule <k> #exec [ BOP:BinStackOp  ] => #gas [ BOP , BOP W0 W1       ] ~> BOP W0 W1       ... </k> <wordStack> ListItem(W0) ListItem(W1) => .List ...</wordStack>
    rule <k> #exec [ TOP:TernStackOp ] => #gas [ TOP , TOP W0 W1 W2    ] ~> TOP W0 W1 W2    ... </k> <wordStack> ListItem(W0) ListItem(W1) ListItem(W2) => .List ...</wordStack>
    rule <k> #exec [ QOP:QuadStackOp ] => #gas [ QOP , QOP W0 W1 W2 W3 ] ~> QOP W0 W1 W2 W3 ... </k> <wordStack> ListItem(W0) ListItem(W1) ListItem(W2) ListItem(W3) => .List ...</wordStack>
```

`StackOp` is used for opcodes which require a large portion of the stack.

```k
    syntax InternalOp ::= StackOp List
 // ----------------------------------
    rule <k> #exec [ SO:StackOp ] => #gas [ SO , SO WS ] ~> SO WS ... </k> <wordStack> WS </wordStack>
```

The `CallOp` opcodes all interpret their second argument as an address.

```k
    syntax InternalOp ::= CallSixOp MInt{256} MInt{256}           MInt{256} MInt{256} MInt{256} MInt{256}
                        | CallOp    MInt{256} MInt{256} MInt{256} MInt{256} MInt{256} MInt{256} MInt{256}
 // -----------------------------------------------------------------------------------------------------
    rule <k> #exec [ CSO:CallSixOp ] => #gas [ CSO , CSO W0 W1    W2 W3 W4 W5 ] ~> CSO W0 W1    W2 W3 W4 W5 ... </k> <wordStack> ListItem(W0) ListItem(W1) ListItem(W2) ListItem(W3) ListItem(W4) ListItem(W5) => .List ...</wordStack>
    rule <k> #exec [ CO:CallOp     ] => #gas [ CO  , CO  W0 W1 W2 W3 W4 W5 W6 ] ~> CO  W0 W1 W2 W3 W4 W5 W6 ... </k> <wordStack> ListItem(W0) ListItem(W1) ListItem(W2) ListItem(W3) ListItem(W4) ListItem(W5) ListItem(W6) => .List ...</wordStack>
```

### Address Conversion

Some opcodes require accessing elements of the state at different addresses.
We make sure the given arguments (to be interpreted as addresses) are with 160 bits ahead of time.

```k
    syntax InternalOp ::= "#addr" "[" OpCode "]"
 // --------------------------------------------
    rule <k> #addr [ OP:OpCode ] => .K ... </k>
         <wordStack> WS => WS [ 0 <- #addrAsMInt256({WS [ 0 ]}:>MInt{256}) ] </wordStack>
      requires isAddr1Op(OP)

    rule <k> #addr [ OP:OpCode ] => .K ... </k>
         <wordStack> WS => WS [ 1 <- #addrAsMInt256({WS [ 1 ]}:>MInt{256}) ] </wordStack>
      requires isAddr2Op(OP)

    rule <k> #addr [ OP:OpCode ] => .K ... </k>
      requires notBool ( isAddr1Op(OP) orBool isAddr2Op(OP) )

    syntax Bool ::= isAddr1Op ( OpCode ) [symbol(isAddr1Op), function, total]
                  | isAddr2Op ( OpCode ) [symbol(isAddr2Op), function, total]
 // -------------------------------------------------------------------------
    rule isAddr1Op(BALANCE)      => true
    rule isAddr1Op(SELFDESTRUCT) => true
    rule isAddr1Op(EXTCODEHASH)  => true
    rule isAddr1Op(EXTCODESIZE)  => true
    rule isAddr1Op(EXTCODECOPY)  => true
    rule isAddr1Op(_)            => false [owise]

    rule isAddr2Op(_:CallOp)    => true
    rule isAddr2Op(_:CallSixOp) => true
    rule isAddr2Op(_)           => false [owise]
```

### Program Counter

All operators except for `PUSH` and `JUMP*` increment the program counter by 1.
The arguments to `PUSH` must be skipped over (as they are inline), and the opcode `JUMP` already affects the program counter in the correct way.

-   `#pc` calculates the next program counter of the given operator.

```k
    syntax InternalOp ::= "#pc" "[" OpCode "]" [symbol(pc)]
 // -------------------------------------------------------
    rule [pc.inc]:
         <k> #pc [ OP ] => .K ... </k>
         <pc> PCOUNT => PCOUNT +MInt #widthOp(OP) </pc>

    syntax MInt{256} ::= #widthOp ( OpCode ) [symbol(#widthOp), function, total]
 // ----------------------------------------------------------------------------
    rule #widthOp(PUSH(N)) => 1p256 +MInt Int2MInt(N)::MInt{256}
    rule #widthOp(_)       => 1p256                              [owise]
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
    syntax InternalOp ::= "#push" | "#setStack" List
 // ------------------------------------------------
    rule <k> W0:MInt{256}          ~> #push => .K ... </k> <wordStack> WS => pushList(W0, WS) </wordStack>
    rule <k> EvmWord(W0:MInt{256}) ~> #push => .K ... </k> <wordStack> WS => pushList(W0, WS) </wordStack>
    rule <k> #setStack WS                   => .K ... </k> <wordStack> _  => WS               </wordStack>
```

### Invalid Operator

We use `INVALID` both for marking the designated invalid operator, and `UNDEFINED(_)` for garbage bytes in the input program.

```k
    syntax InvalidOp ::= "INVALID" | "UNDEFINED" "(" Int ")"
 // --------------------------------------------------------
    rule <k> INVALID      => #end EVMC_INVALID_INSTRUCTION   ... </k>
    rule <k> UNDEFINED(_) => #end EVMC_UNDEFINED_INSTRUCTION ... </k>
```

### Stack Manipulations

Some operators don't calculate anything, they just push the stack around a bit.

```k
    syntax UnStackOp ::= "POP"
 // --------------------------
    rule <k> POP _ => .K ... </k>

    syntax StackOp ::= DUP  ( Int ) [symbol(DUP)]
                     | SWAP ( Int ) [symbol(SWAP)]
 // ----------------------------------------------
    rule <k> DUP(N)  WS:List => #setStack (pushList(WS [ N -Int 1 ], WS))                      ... </k>
    rule <k> SWAP(N) (ListItem(W0) WS)    => #setStack (pushList(WS [ N -Int 1 ], (WS [ N -Int 1 <- W0 ]))) ... </k>

    syntax PushOp ::= "PUSHZERO"
                    | PUSH ( Int ) [symbol(PUSH)]
 // ---------------------------------------------
    rule <k> PUSHZERO => 0p256 ~> #push ... </k>

    rule <k> PUSH(N) => Bytes2MInt(padLeftBytes(#rangeMInt256(PGM, PCOUNT +MInt 1p256, Int2MInt(N)::MInt{256}), 32, 0))::MInt{256} ~> #push ... </k>
         <pc> PCOUNT </pc>
         <program> PGM </program>
```

### Local Memory

These operations are getters/setters of the local execution memory.

```k
    syntax UnStackOp ::= "MLOAD"
 // ----------------------------
    rule <k> MLOAD INDEX => Bytes2MInt(#rangeMInt256(LM, INDEX, 32p256))::MInt{256} ~> #push ... </k>
         <localMem> LM </localMem>

    syntax BinStackOp ::= "MSTORE" | "MSTORE8"
 // ------------------------------------------
    rule <k> MSTORE INDEX VALUE => .K ... </k>
         <localMem> LM => LM [ INDEX :=MInt256 MInt2Bytes(VALUE) ] </localMem>

    rule <k> MSTORE8 INDEX VALUE => .K ... </k>
         <localMem> LM => #writeMInt256(LM, INDEX, VALUE %uMInt 256p256) </localMem>

    syntax TernStackOp ::= "MCOPY"
 // ------------------------------
     rule <k> MCOPY DST SRC LEN => .K ... </k>
          <localMem> LM => LM [ DST :=MInt256 #rangeMInt256(LM, SRC, LEN) ] </localMem>
```

### Expressions

Expression calculations are simple and don't require anything but the arguments from the `wordStack` to operate.

NOTE: We have to call the opcode `OR` by `EVMOR` instead, because K has trouble parsing it/compiling the definition otherwise.

```k
    syntax UnStackOp ::= "ISZERO" | "NOT"
 // -------------------------------------
    rule <k> ISZERO W => bool2MInt256(W ==MInt 0p256) ~> #push ... </k>
    rule <k> NOT    W => ~MInt W                      ~> #push ... </k>

    syntax BinStackOp ::= "ADD" | "MUL" | "SUB" | "DIV" | "EXP" | "MOD"
 // -------------------------------------------------------------------
    rule <k> ADD W0 W1 => W0 +MInt W1  ~> #push ... </k>
    rule <k> MUL W0 W1 => W0 *MInt W1  ~> #push ... </k>
    rule <k> SUB W0 W1 => W0 -MInt W1  ~> #push ... </k>
    rule <k> DIV  _ W1 => 0p256        ~> #push ... </k> requires W1  ==MInt 0p256
    rule <k> DIV W0 W1 => W0 /uMInt W1 ~> #push ... </k> requires W1 =/=MInt 0p256
    rule <k> EXP W0 W1 => W0 ^MInt W1  ~> #push ... </k>
    rule <k> MOD  _ W1 => 0p256        ~> #push ... </k> requires W1  ==MInt 0p256
    rule <k> MOD W0 W1 => W0 %uMInt W1 ~> #push ... </k> requires W1 =/=MInt 0p256

    syntax BinStackOp ::= "SDIV" | "SMOD"
 // -------------------------------------
    rule <k> SDIV _  W1 => 0p256        ~> #push ... </k> requires W1  ==MInt 0p256
    rule <k> SDIV W0 W1 => W0 /sMInt W1 ~> #push ... </k> requires W1 =/=MInt 0p256
    rule <k> SMOD _  W1 => 0p256        ~> #push ... </k> requires W1  ==MInt 0p256
    rule <k> SMOD W0 W1 => W0 %sMInt W1 ~> #push ... </k> requires W1 =/=MInt 0p256

    syntax TernStackOp ::= "ADDMOD" | "MULMOD"
 // ------------------------------------------
    rule <k> ADDMOD W0 W1 W2 => addmodMInt256(W0, W1, W2) ~> #push ... </k>
    rule <k> MULMOD W0 W1 W2 => mulmodMInt256(W0, W1, W2) ~> #push ... </k>

    syntax BinStackOp ::= "BYTE" | "SIGNEXTEND"
 // -------------------------------------------
    rule <k> BYTE INDEX W     => byteMInt256(INDEX, W)     ~> #push ... </k>
    rule <k> SIGNEXTEND W0 W1 => signextendMInt256(W0, W1) ~> #push ... </k>

    syntax BinStackOp ::= "SHL" | "SHR" | "SAR"
 // -------------------------------------------
    rule <k> SHL W0 W1 =>  W1 <<MInt  W0 ~> #push ... </k> requires W0 <uMInt  256p256
    rule <k> SHL W0  _ =>          0p256 ~> #push ... </k> requires W0 >=uMInt 256p256
    rule <k> SHR W0 W1 =>  W1 >>lMInt W0 ~> #push ... </k> requires W0 <uMInt  256p256
    rule <k> SHR W0  _ =>          0p256 ~> #push ... </k> requires W0 >=uMInt 256p256
    rule <k> SAR W0 W1 =>  W1 >>aMInt W0 ~> #push ... </k> requires W0 <uMInt  256p256
    rule <k> SAR W0 W1 =>          0p256 ~> #push ... </k> requires W0 >=uMInt 256p256 andBool W1 <=uMInt maxSInt256p256
    rule <k> SAR W0 W1 => maxUInt256p256 ~> #push ... </k> requires W0 >=uMInt 256p256 andBool W1 >uMInt  maxSInt256p256

    syntax BinStackOp ::= "AND" | "EVMOR" | "XOR"
 // ---------------------------------------------
    rule <k> AND   W0 W1 => W0 &MInt W1   ~> #push ... </k>
    rule <k> EVMOR W0 W1 => W0 |MInt W1   ~> #push ... </k>
    rule <k> XOR   W0 W1 => W0 xorMInt W1 ~> #push ... </k>

    syntax BinStackOp ::= "LT" | "GT" | "EQ"
 // ----------------------------------------
    rule <k> LT W0 W1 => bool2MInt256(W0 <uMInt W1) ~> #push ... </k>
    rule <k> GT W0 W1 => bool2MInt256(W0 >uMInt W1) ~> #push ... </k>
    rule <k> EQ W0 W1 => bool2MInt256(W0 ==MInt W1) ~> #push ... </k>

    syntax BinStackOp ::= "SLT" | "SGT"
 // -----------------------------------
    rule <k> SLT W0 W1 => bool2MInt256(W0 <sMInt W1) ~> #push ... </k>
    rule <k> SGT W0 W1 => bool2MInt256(W0 >sMInt W1) ~> #push ... </k>

    syntax BinStackOp ::= "SHA3"
 // ----------------------------
    rule <k> SHA3 MEMSTART MEMWIDTH => keccakMInt256(#rangeMInt256(LM, MEMSTART, MEMWIDTH)) ~> #push ... </k>
         <localMem> LM </localMem>
```

### Local State

These operators make queries about the current execution state.

```k
    syntax NullStackOp ::= "PC" | "GAS" | "GASPRICE" | "GASLIMIT" | "BASEFEE" | "BLOBBASEFEE"
 // -----------------------------------------------------------------------------------------
    rule <k> PC          => PCOUNT                               ~> #push ... </k> <pc> PCOUNT </pc>
    rule <k> GAS         => Int2MInt(gas2Int(GAVAIL))::MInt{256} ~> #push ... </k> <gas> GAVAIL </gas>
    rule <k> GASPRICE    => GasPrice()                           ~> #push ... </k>
    rule <k> GASLIMIT    => GasLimit()                           ~> #push ... </k>
    rule <k> BASEFEE     => BaseFee()                            ~> #push ... </k>
    rule <k> BLOBBASEFEE => BlobBaseFee()                        ~> #push ... </k>

    syntax NullStackOp ::= "COINBASE" | "TIMESTAMP" | "NUMBER" | "DIFFICULTY" | "PREVRANDAO"
 // ----------------------------------------------------------------------------------------
    rule <k> COINBASE   => Coinbase()        ~> #push ... </k>
    rule <k> TIMESTAMP  => BlockTimestamp()  ~> #push ... </k>
    rule <k> NUMBER     => BlockNumber()     ~> #push ... </k>
    rule <k> DIFFICULTY => BlockDifficulty() ~> #push ... </k>
    rule <k> PREVRANDAO => PrevRandao()      ~> #push ... </k>

    syntax NullStackOp ::= "ADDRESS" | "ORIGIN" | "CALLER" | "CALLVALUE" | "CHAINID" | "SELFBALANCE"
 // ------------------------------------------------------------------------------------------------
    rule <k> ADDRESS     => ACCT                             ~> #push ... </k> <id> ACCT </id>
    rule <k> ORIGIN      => Origin()                         ~> #push ... </k>
    rule <k> CALLER      => CL                               ~> #push ... </k> <caller> CL </caller>
    rule <k> CALLVALUE   => CV                               ~> #push ... </k> <callValue> CV </callValue>
    rule <k> CHAINID     => ChainId()                        ~> #push ... </k>
    rule <k> SELFBALANCE => GetAccountBalance(EvmWord(ACCT)) ~> #push ... </k> <id> ACCT </id>

    syntax NullStackOp ::= "MSIZE" | "CODESIZE"
 // -------------------------------------------
    rule <k> MSIZE    => 32p256 *MInt Int2MInt(MU)::MInt{256} ~> #push ... </k> <memoryUsed> MU </memoryUsed>
    rule <k> CODESIZE => lengthBytes(PGM)::MInt{256}          ~> #push ... </k> <program> PGM </program>

    syntax TernStackOp ::= "CODECOPY"
 // ---------------------------------
    rule <k> CODECOPY MEMSTART PGMSTART WIDTH => .K ... </k>
         <program> PGM </program>
         <localMem> LM =>  LM [ MEMSTART :=MInt256 #rangeMInt256(PGM, PGMSTART, WIDTH) ] </localMem>

    syntax UnStackOp ::= "BLOCKHASH"
 // --------------------------------
```

The blockhash is calculated here using the "shortcut" formula used for running tests.

```k
    rule <k> BLOCKHASH N => BlockHash(EvmWord(N)) ~> #push ... </k>
```

```k
    syntax UnStackOp ::= "BLOBHASH"
 // -------------------------------

    rule <k> BLOBHASH INDEX => 0p256 ~> #push ... </k>
       requires INDEX >=uMInt unwrapEvmWord(BlobHashesSize())

    rule <k> BLOBHASH INDEX => BlobHash(EvmWord(INDEX)) ~> #push ... </k>
       requires INDEX <uMInt unwrapEvmWord(BlobHashesSize())
```

EVM OpCodes
-----------

### EVM Control Flow

The `JUMP*` family of operations affect the current program counter.

```k
    syntax NullStackOp ::= "JUMPDEST"
 // ---------------------------------
    rule <k> JUMPDEST => .K ... </k>

    syntax UnStackOp ::= "JUMP"
 // ---------------------------
    rule [jump]:
         <k> JUMP DEST => #endBasicBlock ... </k>
         <pc> _ => DEST </pc>
         <jumpDests> DESTS </jumpDests>
      requires DEST <uMInt lengthBytes(DESTS) andBool DESTS[DEST] ==MInt 1p256

    rule <k> JUMP _ => #end EVMC_BAD_JUMP_DESTINATION ... </k> [owise]

    syntax BinStackOp ::= "JUMPI"
 // -----------------------------
    rule [jumpi.false]: <k> JUMPI _DEST I => .K        ... </k> requires I  ==MInt 0p256
    rule [jumpi.true]:  <k> JUMPI  DEST I => JUMP DEST ... </k> requires I =/=MInt 0p256

    syntax InternalOp ::= "#endBasicBlock"
 // --------------------------------------
    rule                    <k> #endBasicBlock ~> (_:OpCode => .K) ... </k>
    rule [end-basic-block]: <k> (#endBasicBlock => .K) ~> #execute ... </k>
```

### `STOP`, `REVERT`, and `RETURN`

```k
    syntax NullStackOp ::= "STOP"
 // -----------------------------
    rule <k> STOP => #end EVMC_SUCCESS ... </k>
         <output> _ => .Bytes </output>

    syntax BinStackOp ::= "RETURN"
 // ------------------------------
    rule <k> RETURN RETSTART RETWIDTH => #end EVMC_SUCCESS ... </k>
         <output> _ => #rangeMInt256(LM, RETSTART, RETWIDTH) </output>
         <localMem> LM </localMem>

    syntax BinStackOp ::= "REVERT"
 // ------------------------------
    rule <k> REVERT RETSTART RETWIDTH => #end EVMC_REVERT ... </k>
         <output> _ => #rangeMInt256(LM, RETSTART, RETWIDTH) </output>
         <localMem> LM </localMem>
```

### Call Data

These operators query about the current `CALL*` state.

```k
    syntax NullStackOp ::= "CALLDATASIZE"
 // -------------------------------------
   rule <k> CALLDATASIZE => lengthBytes(CD)::MInt{256} ~> #push ... </k>
         <callData> CD </callData>

    syntax UnStackOp ::= "CALLDATALOAD"
 // -----------------------------------
   rule <k> CALLDATALOAD DATASTART => Bytes2MInt(#rangeMInt256(CD, DATASTART, 32p256))::MInt{256} ~> #push ... </k>
         <callData> CD </callData>

    syntax TernStackOp ::= "CALLDATACOPY"
 // -------------------------------------
   rule <k> CALLDATACOPY MEMSTART DATASTART DATAWIDTH => .K ... </k>
         <localMem> LM => LM [ MEMSTART :=MInt256 #rangeMInt256(CD, DATASTART, DATAWIDTH) ] </localMem>
         <callData> CD </callData>
```

### Return Data

These operators query about the current return data buffer.

```k
    syntax NullStackOp ::= "RETURNDATASIZE"
 // ---------------------------------------
    rule <k> RETURNDATASIZE => lengthBytes(RD)::MInt{256} ~> #push ... </k>
         <output> RD </output>

    syntax TernStackOp ::= "RETURNDATACOPY"
 // ---------------------------------------
    rule <k> RETURNDATACOPY MEMSTART DATASTART DATAWIDTH => .K ... </k>
         <localMem> LM => LM [ MEMSTART :=MInt256 #rangeMInt256(RD, DATASTART, DATAWIDTH) ] </localMem>
         <output> RD </output>
      requires inBoundsMInt256(DATASTART, DATAWIDTH, lengthBytes(RD))

    rule <k> RETURNDATACOPY _MEMSTART DATASTART DATAWIDTH => #end EVMC_INVALID_MEMORY_ACCESS ... </k>
         <output> RD </output>
      requires notBool inBoundsMInt256(DATASTART, DATAWIDTH, lengthBytes(RD))
```

### Log Operations

```k
    syntax BinStackOp ::= LogOp
    syntax LogOp ::= LOG ( Int ) [symbol(LOG)]
 // ------------------------------------------
    rule <k> LOG(0) MEMSTART MEMWIDTH => Log0(EvmWord(ACCT), #rangeMInt256(LM, MEMSTART, MEMWIDTH)) ...</k>
         <id> ACCT </id>
         <localMem> LM </localMem>
    rule <k> LOG(1) MEMSTART MEMWIDTH => Log1(EvmWord(ACCT), EvmWord(T1), #rangeMInt256(LM, MEMSTART, MEMWIDTH)) ...</k>
         <id> ACCT </id>
         <wordStack> ListItem(T1) WS => WS </wordStack>
         <localMem> LM </localMem>
    rule <k> LOG(2) MEMSTART MEMWIDTH => Log2(EvmWord(ACCT), EvmWord(T1), EvmWord(T2), #rangeMInt256(LM, MEMSTART, MEMWIDTH)) ...</k>
         <id> ACCT </id>
         <wordStack> ListItem(T1) ListItem(T2) WS => WS </wordStack>
         <localMem> LM </localMem>
    rule <k> LOG(3) MEMSTART MEMWIDTH => Log3(EvmWord(ACCT), EvmWord(T1), EvmWord(T2), EvmWord(T3), #rangeMInt256(LM, MEMSTART, MEMWIDTH)) ...</k>
         <id> ACCT </id>
         <wordStack> ListItem(T1) ListItem(T2) ListItem(T3) WS => WS </wordStack>
         <localMem> LM </localMem>
    rule <k> LOG(4) MEMSTART MEMWIDTH => Log4(EvmWord(ACCT), EvmWord(T1), EvmWord(T2), EvmWord(T3), EvmWord(T4), #rangeMInt256(LM, MEMSTART, MEMWIDTH)) ...</k>
         <id> ACCT </id>
         <wordStack> ListItem(T1) ListItem(T2) ListItem(T3) ListItem(T4) WS => WS </wordStack>
         <localMem> LM </localMem>
```

Ethereum Network OpCodes
------------------------

Operators that require access to the rest of the Ethereum network world-state can be taken as a first draft of a "blockchain generic" language.

### Account Queries

```k
    syntax UnStackOp ::= "BALANCE"
 // ------------------------------
    rule <k> BALANCE ACCT => GetAccountBalance(EvmWord(ACCT)) ~> #push ... </k>

    syntax UnStackOp ::= "EXTCODESIZE"
 // ----------------------------------
    rule <k> EXTCODESIZE ACCT => lengthBytes(GetAccountCode(EvmWord(ACCT)))::MInt{256} ~> #push ... </k>

    syntax UnStackOp ::= "EXTCODEHASH"
 // ----------------------------------
    rule <k> EXTCODEHASH ACCT => GetCodeHash(EvmWord(ACCT)) ~> #push ... </k>
      requires notBool IsAccountEmpty(EvmWord(ACCT))

    rule <k> EXTCODEHASH ACCT => AccessAccount(EvmWord(ACCT)) ~> 0p256 ~> #push ... </k> [owise]

    syntax QuadStackOp ::= "EXTCODECOPY"
 // ------------------------------------
    rule <k> EXTCODECOPY ACCT MEMSTART PGMSTART WIDTH => .K ... </k>
         <localMem> LM => LM [ MEMSTART :=MInt256 #rangeMInt256(GetAccountCode(EvmWord(ACCT)), PGMSTART, WIDTH) ] </localMem>
```

### Account Storage Operations

These rules reach into the network state and load/store from account storage:

```k
    syntax UnStackOp ::= "SLOAD"
 // ----------------------------
    rule [sload]:
         <k> SLOAD INDEX => GetAccountStorage(EvmWord(ACCT), EvmWord(INDEX)) ~> #push ... </k>
         <id> ACCT </id>

    syntax BinStackOp ::= "SSTORE"
 // ------------------------------
    rule [sstore]:
         <k> SSTORE INDEX NEW => SetAccountStorage(EvmWord(ACCT), EvmWord(INDEX), EvmWord(NEW)) ... </k>
         <id> ACCT </id>
      [preserves-definedness]

    syntax UnStackOp ::= "TLOAD"
 // ----------------------------
    rule [tload]:
         <k> TLOAD INDEX => GetAccountTransientStorage(EvmWord(ACCT), EvmWord(INDEX)) ~> #push ... </k>
         <id> ACCT </id>

    syntax BinStackOp ::= "TSTORE"
 // ------------------------------
    rule [tstore]:
         <k> TSTORE INDEX NEW => SetAccountTransientStorage(EvmWord(ACCT), EvmWord(INDEX), EvmWord(NEW)) ... </k>
         <id> ACCT </id>
      [preserves-definedness]
```

### Transfer Operation
```k
    syntax InternalOp ::= "#transferFundsFrom" MInt{256} MInt{256} MInt{256}
   // -------------------------------------------------------------------------------------------------
    rule [transferFundsFrom.success]:
      <k> #transferFundsFrom ACCTFROM ACCTTO VALUE => .K ... </k>
      requires TransferFrom(EvmWord(ACCTFROM), EvmWord(ACCTTO), EvmWord(VALUE))

    rule [transferFundsFrom.failure]:
      <k> #transferFundsFrom _ _ _ => #end EVMC_BALANCE_UNDERFLOW ... </k> [owise]
```

### Call Operations

The various `CALL*` (and other inter-contract control flow) operations will be desugared into these `InternalOp`s.

-   `#checkCall` takes the calling account and the value of the call and triggers several checks before executing the call.
-   `#checkBalanceUnderflow` takes the calling account and the value of the call and checks if the call value is greater than the account balance.
-   `#checkDepthExceeded` checks if the current call depth is greater than or equal to `1024`.
-   `#checkNonceExceeded` takes the calling account and checks if the nonce is less than `maxUInt64` (`18446744073709551615`).
-   `#call` takes the calling account, the account to execute as, the account whose code should execute, the gas limit, the amount to transfer, the arguments, and the static flag.
-   `#callWithCode` takes the calling account, the account to execute as, the code to execute (as a `Bytes`), the gas limit, the amount to transfer, the arguments, and the static flag.
-   `#return` is a placeholder for the calling program, specifying where to place the returned data in memory.

```k
    syntax InternalOp ::= "#checkCall"             MInt{256} MInt{256}
                        | "#checkBalanceUnderflow" MInt{256} MInt{256}
                        | "#checkNonceExceeded"    MInt{256}
                        | "#checkDepthExceeded"
                        | "#call"                  MInt{256} MInt{256} MInt{256}       MInt{256} MInt{256} Bytes Bool
                        | "#callWithCode"          MInt{256} MInt{256} MInt{256} Bytes MInt{256} MInt{256} Bytes Bool [symbol(callwithcode_check_fork)]
                        | "#mkCall"                MInt{256} MInt{256} MInt{256} Bytes           MInt{256} Bytes Bool
 // -----------------------------------------------------------------------------------------------------------------
     rule <k> #checkBalanceUnderflow ACCT VALUE => #refund GCALL ~> #pushCallStack ~> #pushWorldState ~> #end EVMC_BALANCE_UNDERFLOW ... </k>
         <output> _ => .Bytes </output>
         <callGas> GCALL </callGas>
      requires VALUE >uMInt unwrapEvmWord(GetAccountBalance(EvmWord(ACCT)))

    rule <k> #checkBalanceUnderflow ACCT VALUE => .K ... </k>
      requires VALUE <=uMInt unwrapEvmWord(GetAccountBalance(EvmWord(ACCT)))

    rule <k> #checkDepthExceeded => #refund GCALL ~> #pushCallStack ~> #pushWorldState ~> #end EVMC_CALL_DEPTH_EXCEEDED ... </k>
         <output> _ => .Bytes </output>
         <callGas> GCALL </callGas>
         <callDepth> CD </callDepth>
      requires CD >=Int 1024

    rule <k> #checkDepthExceeded => .K ... </k>
         <callDepth> CD </callDepth>
      requires CD <Int 1024

    rule <k> #checkNonceExceeded ACCT => #refund GCALL ~> #pushCallStack ~> #pushWorldState ~> #end EVMC_NONCE_EXCEEDED ... </k>
         <output> _ => .Bytes </output>
         <callGas> GCALL </callGas>
      requires notBool #rangeNonceMInt256(unwrapEvmWord(GetAccountNonce(EvmWord(ACCT))))

    rule <k> #checkNonceExceeded ACCT => .K ... </k>
      requires #rangeNonceMInt256(unwrapEvmWord(GetAccountNonce(EvmWord(ACCT))))

    rule <k> #checkCall ACCT VALUE => #checkBalanceUnderflow ACCT VALUE ~> #checkDepthExceeded ... </k>

    rule [call.true]:
         <k> #call ACCTFROM ACCTTO ACCTCODE VALUE APPVALUE ARGS STATIC
          => #callWithCode ACCTFROM ACCTTO ACCTCODE GetAndResolveCode(EvmWord(ACCTCODE)) VALUE APPVALUE ARGS STATIC
         ...
         </k>
        requires AccountExists(EvmWord(ACCTCODE))

    rule [call.false]:
         <k> #call ACCTFROM ACCTTO ACCTCODE VALUE APPVALUE ARGS STATIC
          => #callWithCode ACCTFROM ACCTTO ACCTCODE .Bytes VALUE APPVALUE ARGS STATIC
         ...
         </k> [owise]

    rule <k> #callWithCode ACCTFROM ACCTTO ACCTCODE BYTES VALUE APPVALUE ARGS STATIC
          => #pushCallStack ~> #pushWorldState
          ~> #transferFundsFrom ACCTFROM ACCTTO VALUE
          ~> #mkCall ACCTFROM ACCTTO ACCTCODE BYTES APPVALUE ARGS STATIC
         ...
         </k>

    rule <k> #mkCall ACCTFROM ACCTTO ACCTCODE BYTES APPVALUE ARGS STATIC:Bool
          => AccessAccount(EvmWord(ACCTFROM)) ~> AccessAccount(EvmWord(ACCTTO)) ~> #loadProgram BYTES ~> #initVM ~> #precompiled?(MInt2Unsigned(ACCTCODE), SCHED) ~> #execute
         ...
         </k>
         <callDepth> CD => CD +Int 1 </callDepth>
         <callData> _ => ARGS </callData>
         <callValue> _ => APPVALUE </callValue>
         <id> _ => ACCTTO </id>
         <gas> _GAVAIL:Int => GCALL:Int </gas>
         <callGas> GCALL:Int => 0:Int </callGas>
         <caller> _ => ACCTFROM </caller>
         <static> OLDSTATIC:Bool => OLDSTATIC orBool STATIC </static>
         <schedule> SCHED </schedule>

    syntax InternalOp ::= "#precompiled?" "(" Int "," Schedule ")"
 // --------------------------------------------------------------
    rule [precompile.true]:  <k> #precompiled?(ACCTCODE, SCHED) => #next [ #precompiled(ACCTCODE) ] ... </k> requires         #isPrecompiledAccount(ACCTCODE, SCHED) [preserves-definedness]
    rule [precompile.false]: <k> #precompiled?(ACCTCODE, SCHED) => .K                               ... </k> requires notBool #isPrecompiledAccount(ACCTCODE, SCHED)

    syntax Bool ::= #isPrecompiledAccount ( Int , Schedule ) [symbol(isPrecompiledAccount), function, total, smtlib(isPrecompiledAccount)]
 // --------------------------------------------------------------------------------------------------------------------------------------
    rule [isPrecompiledAccount]:  #isPrecompiledAccount(ACCTCODE, SCHED) => 0 <Int ACCTCODE andBool ACCTCODE <=Int #precompiledAccountsUB(SCHED)

    syntax KItem ::= "#initVM"
 // --------------------------
    rule <k> #initVM      => .K ... </k>
         <pc>           _ => 0p256  </pc>
         <memoryUsed>   _ => 0      </memoryUsed>
         <output>       _ => .Bytes </output>
         <wordStack>    _ => .List  </wordStack>
         <localMem>     _ => .Bytes </localMem>

    syntax KItem ::= "#loadProgram" Bytes [symbol(loadProgram)]
 // -----------------------------------------------------------
    rule [program.load]:
         <k> #loadProgram BYTES => .K ... </k>
         <program> _ => BYTES </program>
         <jumpDests> _ => ComputeValidJumpDests(BYTES) </jumpDests>

    syntax KItem ::= "#return" MInt{256} MInt{256}
 // ----------------------------------------------
    rule [return.exception]:
         <statusCode> _:ExceptionalStatusCode </statusCode>
         <k> #halt ~> #return _ _
          => #popCallStack ~> #popWorldState ~> 0p256 ~> #push
          ...
         </k>
         <output> _ => .Bytes </output>

    rule [return.revert]:
         <statusCode> EVMC_REVERT </statusCode>
         <k> #halt ~> #return RETSTART RETWIDTH
          => #popCallStack ~> #popWorldState
          ~> 0p256 ~> #push ~> #refund GAVAIL ~> #setLocalMem RETSTART RETWIDTH OUT
         ...
         </k>
         <output> OUT </output>
         <gas> GAVAIL </gas>

    rule [return.success]:
         <statusCode> EVMC_SUCCESS </statusCode>
         <k> #halt ~> #return RETSTART RETWIDTH
          => #popCallStack ~> #dropWorldState
          ~> 1p256 ~> #push ~> #refund GAVAIL ~> #setLocalMem RETSTART RETWIDTH OUT
         ...
         </k>
         <output> OUT </output>
         <gas> GAVAIL </gas>


    syntax InternalOp ::= "#refund" Gas
                        | "#setLocalMem" MInt{256} MInt{256} Bytes
 // --------------------------------------------------------------
    rule [refund]: <k> #refund G:Int => .K ... </k> <gas> GAVAIL => GAVAIL +Int G </gas>


    rule <k> #setLocalMem START WIDTH WS => .K ... </k>
         <localMem> LM => LM [ START :=MInt256 #rangeMInt256(WS, 0p256, uMinMInt(WIDTH, lengthBytes(WS))) ] </localMem>
```

Ethereum Network OpCodes
------------------------

### Call Operations

For each `CALL*` operation, we make a corresponding call to `#call` and a state-change to setup the custom parts of the calling environment.


```k
    syntax CallOp ::= "CALL"
 // ------------------------
    rule [call]:
         <k> CALL _GCAP ACCTTO VALUE ARGSTART ARGWIDTH RETSTART RETWIDTH
          => AccessAccount(EvmWord(ACCTTO))
          ~> #checkCall ACCTFROM VALUE
          ~> #call ACCTFROM ACCTTO ACCTTO VALUE VALUE #rangeMInt256(LM, ARGSTART, ARGWIDTH) false
          ~> #return RETSTART RETWIDTH

         ...
         </k>
         <id> ACCTFROM </id>
         <localMem> LM </localMem>

    syntax CallOp ::= "CALLCODE"
 // ----------------------------
    rule [callcode]:
         <k> CALLCODE _GCAP ACCTTO VALUE ARGSTART ARGWIDTH RETSTART RETWIDTH
          => AccessAccount(EvmWord(ACCTTO))
          ~> #checkCall ACCTFROM VALUE
          ~> #call ACCTFROM ACCTFROM ACCTTO VALUE VALUE #rangeMInt256(LM, ARGSTART, ARGWIDTH) false
          ~> #return RETSTART RETWIDTH
         ...
         </k>
         <id> ACCTFROM </id>
         <localMem> LM </localMem>

    syntax CallSixOp ::= "DELEGATECALL"
 // -----------------------------------
    rule [delegatecall]:
         <k> DELEGATECALL _GCAP ACCTTO ARGSTART ARGWIDTH RETSTART RETWIDTH
          => AccessAccount(EvmWord(ACCTTO))
          ~> #checkCall ACCTFROM 0p256
          ~> #call ACCTAPPFROM ACCTFROM ACCTTO 0p256 VALUE #rangeMInt256(LM, ARGSTART, ARGWIDTH) false
          ~> #return RETSTART RETWIDTH
         ...
         </k>
         <id> ACCTFROM </id>
         <caller> ACCTAPPFROM </caller>
         <callValue> VALUE </callValue>
         <localMem> LM </localMem>

    syntax CallSixOp ::= "STATICCALL"
 // ---------------------------------
    rule [staticcall]:
         <k> STATICCALL _GCAP ACCTTO ARGSTART ARGWIDTH RETSTART RETWIDTH
          => AccessAccount(EvmWord(ACCTTO))
          ~> #checkCall ACCTFROM 0p256
          ~> #call ACCTFROM ACCTTO ACCTTO 0p256 0p256 #rangeMInt256(LM, ARGSTART, ARGWIDTH) true
          ~> #return RETSTART RETWIDTH
         ...
         </k>
         <id> ACCTFROM </id>
         <localMem> LM </localMem>
```

### Account Creation/Deletion

-   `#create____` transfers the endowment to the new account and triggers the execution of the initialization code.
-   `#codeDeposit_` checks the result of initialization code and whether the code deposit can be paid, indicating an error if not.
-   `#isValidCode_` checks if the code returned by the execution of the initialization code begins with a reserved byte. [EIP-3541]
-   `#hasValidInitCode` checks the length of the transaction data in a create transaction. [EIP-3860]

```k
    syntax InternalOp ::= "#create"      MInt{256} MInt{256} MInt{256} Bytes
                        | "#mkCreate"    MInt{256} MInt{256} MInt{256} Bytes
                        | "#newAccount"  MInt{256} MInt{256} MInt{256}
                        | "#checkCreate" MInt{256} MInt{256}
    // ---------------------------------------------------------------------
    rule [create]:
         <k> #create ACCTFROM ACCTTO VALUE INITCODE
          => IncrementNonce(EvmWord(ACCTFROM))
          ~> #pushCallStack ~> #pushWorldState
          ~> #newAccount ACCTFROM ACCTTO VALUE
          ~> #mkCreate ACCTFROM ACCTTO VALUE INITCODE
         ...
         </k>


    rule <k> #newAccount ACCTFROM ACCTTO VALUE
          => #if NewAccount(EvmWord(ACCTFROM), EvmWord(ACCTTO), EvmWord(VALUE)) #then .K #else #end EVMC_ACCOUNT_ALREADY_EXISTS #fi
         ...
         </k>

    rule <k> #mkCreate ACCTFROM ACCTTO VALUE INITCODE => #loadProgram INITCODE ~> #initVM ~> #execute ... </k>
         <id> _ => ACCTTO </id>
         <gas> _GAVAIL => GCALL </gas>
         <callGas> GCALL => 0 </callGas>
         <caller> _ => ACCTFROM </caller>
         <callDepth> CD => CD +Int 1 </callDepth>
         <callData> _ => .Bytes </callData>
         <callValue> _ => VALUE </callValue>
```

```k
    rule <k> #checkCreate ACCT VALUE => #checkBalanceUnderflow ACCT VALUE ~> #checkDepthExceeded ~> #checkNonceExceeded ACCT ... </k>

      syntax Bool ::= #isValidCode ( Bytes , Schedule ) [symbol(#isValidCode), function]
 // ----------------------------------------------------------------------------------
    rule #isValidCode( OUT ,  SCHED) => Ghasrejectedfirstbyte << SCHED >> impliesBool OUT[0] =/=Int 239 requires lengthBytes(OUT) >Int 0
    rule #isValidCode(_OUT , _SCHED) => true                                                            [owise]

    syntax Bool ::= #hasValidInitCode ( Int , Schedule ) [symbol(#hasValidInitCode), function]
 // ------------------------------------------------------------------------------------------
    rule #hasValidInitCode(INITCODELEN, SCHED) => notBool Ghasmaxinitcodesize << SCHED >> orBool INITCODELEN <=Int maxInitCodeSize < SCHED >

   syntax KItem ::= "#codeDeposit" MInt{256}
                   | "#mkCodeDeposit" MInt{256}
                   | "#finishCodeDeposit" MInt{256} Bytes

    rule <statusCode> _:ExceptionalStatusCode </statusCode>
         <k> #halt ~> #codeDeposit _ => #popCallStack ~> #popWorldState ~> 0p256 ~> #push ... </k> <output> _ => .Bytes </output>

    rule <statusCode> EVMC_REVERT </statusCode>
         <k> #halt ~> #codeDeposit _ => #popCallStack ~> #popWorldState ~> #refund GAVAIL ~> 0p256 ~> #push ... </k>
         <gas> GAVAIL </gas>

    rule <statusCode> EVMC_SUCCESS </statusCode>
         <k> #halt ~> #codeDeposit ACCT => #mkCodeDeposit ACCT ... </k>

    rule <k> #mkCodeDeposit ACCT
          => Gcodedeposit < SCHED > *Int lengthBytes(OUT) ~> #deductGas
          ~> #finishCodeDeposit ACCT OUT
         ...
         </k>
         <schedule> SCHED </schedule>
         <output> OUT => .Bytes </output>
      requires lengthBytes(OUT) <=Int maxCodeSize < SCHED > andBool #isValidCode(OUT, SCHED)

    rule <k> #mkCodeDeposit _ACCT => #popCallStack ~> #popWorldState ~> 0p256 ~> #push ... </k>
         <schedule> SCHED </schedule>
         <output> OUT => .Bytes </output>
      requires notBool ( lengthBytes(OUT) <=Int maxCodeSize < SCHED > andBool #isValidCode(OUT, SCHED) )

    rule <k> #finishCodeDeposit ACCT OUT
          => #popCallStack ~> #dropWorldState
          ~> #refund GAVAIL ~> SetAccountCode(EvmWord(ACCT), OUT) ~> ACCT ~> #push
         ...
         </k>
         <gas> GAVAIL </gas>

    rule <statusCode> _:ExceptionalStatusCode </statusCode>
         <k> #halt ~> #finishCodeDeposit ACCT _
          => #popCallStack ~> #dropWorldState
          ~> #refund GAVAIL ~> ACCT ~> #push
         ...
         </k>
         <gas> GAVAIL </gas>
         <schedule> FRONTIER </schedule>

    rule <statusCode> _:ExceptionalStatusCode </statusCode>
         <k> #halt ~> #finishCodeDeposit _ _ => #popCallStack ~> #popWorldState ~> 0p256 ~> #push ... </k>
         <schedule> SCHED </schedule>
      requires SCHED =/=K FRONTIER
```

`CREATE` will attempt to `#create` the account using the initialization code and cleans up the result with `#codeDeposit`.

```k
    syntax TernStackOp ::= "CREATE"
 // -------------------------------
    rule [create-valid]:
         <k> CREATE VALUE MEMSTART MEMWIDTH
          => AccessAccount(EvmWord(#newAddrMInt256(ACCT, unwrapEvmWord(GetAccountNonce(EvmWord(ACCT))))))
          ~> #checkCreate ACCT VALUE
          ~> #create ACCT #newAddrMInt256(ACCT, unwrapEvmWord(GetAccountNonce(EvmWord(ACCT)))) VALUE #rangeMInt256(LM, MEMSTART, MEMWIDTH)
          ~> #codeDeposit #newAddrMInt256(ACCT, unwrapEvmWord(GetAccountNonce(EvmWord(ACCT))))
         ...
         </k>
         <id> ACCT </id>
         <localMem> LM </localMem>
         <schedule> SCHED </schedule>
      requires #hasValidInitCode(MInt2Unsigned(MEMWIDTH), SCHED)
      [preserves-definedness]

    rule [create-invalid]:
         <k> CREATE _ _ MEMWIDTH => #end EVMC_OUT_OF_GAS ... </k>
         <schedule> SCHED </schedule>
      requires notBool #hasValidInitCode(MInt2Unsigned(MEMWIDTH), SCHED)
```

`CREATE2` will attempt to `#create` the account, but with the new scheme for choosing the account address.

```k
    syntax QuadStackOp ::= "CREATE2"
 // --------------------------------
    rule [create2-valid]:
         <k> CREATE2 VALUE MEMSTART MEMWIDTH SALT
          => AccessAccount(EvmWord(#newAddrMInt256(ACCT, SALT, #rangeMInt256(LM, MEMSTART, MEMWIDTH))))
          ~> #checkCreate ACCT VALUE
          ~> #create ACCT #newAddrMInt256(ACCT, SALT, #rangeMInt256(LM, MEMSTART, MEMWIDTH)) VALUE #rangeMInt256(LM, MEMSTART, MEMWIDTH)
          ~> #codeDeposit #newAddrMInt256(ACCT, SALT, #rangeMInt256(LM, MEMSTART, MEMWIDTH))
         ...
         </k>
         <id> ACCT </id>
         <localMem> LM </localMem>
         <schedule> SCHED </schedule>
      requires #hasValidInitCode(MInt2Unsigned(MEMWIDTH), SCHED)

    rule [create2-invalid]:
         <k> CREATE2 _ _ _ _ => #end EVMC_OUT_OF_GAS ... </k> [owise]
```

`SELFDESTRUCT` marks the current account for deletion and transfers funds out of the current account.
Self destructing to yourself, unlike a regular transfer, destroys the balance in the account, irreparably losing it.

```k
    syntax UnStackOp ::= "SELFDESTRUCT"
 // -----------------------------------
    rule <k> SELFDESTRUCT ACCTTO => SelfDestruct(EvmWord(IDACCT), EvmWord(ACCTTO)) ~> #end EVMC_SUCCESS ... </k>
         <id> IDACCT </id>
         <output> _ => .Bytes </output>
```

Precompiled Contracts
---------------------

-   `#precompiled` is a placeholder for the pre-compiled contracts of a given schedule. These contracts are located at contiguous addresses starting from 1.
-   `#precompiledAccountsUB`  returns the highest address (upper bound) of the precompiled contract accounts
-   `#precompiledAccountsSet` returns the set of addresses of the precompiled contract accounts

```k
    syntax NullStackOp   ::= PrecompiledOp
    syntax PrecompiledOp ::= #precompiled ( Int ) [symbol(#precompiled), function]
 // ------------------------------------------------------------------------------
    rule #precompiled(1) => ECREC
    rule #precompiled(2) => SHA256
    rule #precompiled(3) => RIP160
    rule #precompiled(4) => ID
    rule #precompiled(5) => MODEXP
    rule #precompiled(6) => ECADD
    rule #precompiled(7) => ECMUL
    rule #precompiled(8) => ECPAIRING
    rule #precompiled(9) => BLAKE2F
    rule #precompiled(10) => KZGPOINTEVAL
    rule #precompiled(11) => BLS12G1ADD
    rule #precompiled(12) => BLS12G1MSM
    rule #precompiled(13) => BLS12G2ADD
    rule #precompiled(14) => BLS12G2MSM
    rule #precompiled(15) => BLS12PAIRING_CHECK
    rule #precompiled(16) => BLS12MAPFPTOG1
    rule #precompiled(17) => BLS12MAPFP2TOG2

    syntax Int ::= #precompiledAccountsUB ( Schedule ) [symbol(#precompiledAccountsUB), function, total]
 // ----------------------------------------------------------------------------------------------------
    rule #precompiledAccountsUB(FRONTIER)          => 4
    rule #precompiledAccountsUB(HOMESTEAD)         => #precompiledAccountsUB(FRONTIER)
    rule #precompiledAccountsUB(TANGERINE_WHISTLE) => #precompiledAccountsUB(HOMESTEAD)
    rule #precompiledAccountsUB(SPURIOUS_DRAGON)   => #precompiledAccountsUB(TANGERINE_WHISTLE)
    rule #precompiledAccountsUB(BYZANTIUM)         => 8
    rule #precompiledAccountsUB(CONSTANTINOPLE)    => #precompiledAccountsUB(BYZANTIUM)
    rule #precompiledAccountsUB(PETERSBURG)        => #precompiledAccountsUB(CONSTANTINOPLE)
    rule #precompiledAccountsUB(ISTANBUL)          => 9
    rule #precompiledAccountsUB(BERLIN)            => #precompiledAccountsUB(ISTANBUL)
    rule #precompiledAccountsUB(LONDON)            => #precompiledAccountsUB(BERLIN)
    rule #precompiledAccountsUB(MERGE)             => #precompiledAccountsUB(LONDON)
    rule #precompiledAccountsUB(SHANGHAI)          => #precompiledAccountsUB(MERGE)
    rule #precompiledAccountsUB(CANCUN)            => 10
    rule #precompiledAccountsUB(PRAGUE)            => 17


    syntax Set ::= #precompiledAccountsSet    ( Schedule ) [symbol(#precompiledAccountsSet),    function, total]
    syntax Set ::= #precompiledAccountsSetAux ( Int      ) [symbol(#precompiledAccountsSetAux), function, total]
 // ------------------------------------------------------------------------------------------------------------
    rule #precompiledAccountsSet(SCHED) => #precompiledAccountsSetAux(#precompiledAccountsUB(SCHED))

    rule #precompiledAccountsSetAux(N)  => .Set requires N <=Int 0
    rule #precompiledAccountsSetAux(N)  => SetItem(N) #precompiledAccountsSetAux(N -Int 1) [owise, preserves-definedness]
```

-   `ECREC` performs ECDSA public key recovery.
-   `SHA256` performs the SHA2-256 hash function.
-   `RIP160` performs the RIPEMD-160 hash function.
-   `ID` is the identity function (copies input to output).
-   `MODEXP` performs arbitrary-precision modular exponentiation.
-   `ECADD`  performs point addition on the elliptic curve alt_bn128.
-   `ECMUL` performs scalar multiplication on the elliptic curve alt_bn128.
-   `ECPAIRING` performs an optimal ate pairing check on the elliptic curve alt_bn128.
-   `BLAKE2F` performs the compression function F used in the BLAKE2 hashing algorithm.
-   `KZGPOINTEVAL` performs the point evaluation precompile that is part of EIP 4844.

```k
    syntax PrecompiledOp ::= "ECREC"
 // --------------------------------
    rule <k> ECREC => #end EVMC_SUCCESS ... </k>
         <output> _ => #let DATA = CD #in #ecrec(#range(DATA, 0, 32), #range(DATA, 32, 32), #range(DATA, 64, 32), #range(DATA, 96, 32)) </output>
         <callData> CD </callData>

    syntax Bytes ::= #ecrec ( Bytes , Bytes , Bytes , Bytes ) [symbol(#ecrec),    function, total, smtlib(ecrec)]
                   | #ecrec ( Account )                       [symbol(#ecrecAux), function, total               ]
 // -------------------------------------------------------------------------------------------------------------
    rule [ecrec]: #ecrec(HASH, SIGV, SIGR, SIGS) => #ecrec(#sender(HASH, #asWord(SIGV), SIGR, SIGS)) [concrete]

    rule #ecrec(.Account) => .Bytes
    rule #ecrec(N:Int)    => #padToWidth(32, #asByteStack(N))

    syntax PrecompiledOp ::= "SHA256"
 // ---------------------------------
    rule <k> SHA256 => #end EVMC_SUCCESS ... </k>
         <output> _ => #parseHexBytes(Sha256(CD)) </output>
         <callData> CD </callData>

    syntax PrecompiledOp ::= "RIP160"
 // ---------------------------------
    rule <k> RIP160 => #end EVMC_SUCCESS ... </k>
         <output> _ => #padToWidth(32, #parseHexBytes(RipEmd160(CD))) </output>
         <callData> CD </callData>

    syntax PrecompiledOp ::= "ID"
 // -----------------------------
    rule <k> ID => #end EVMC_SUCCESS ... </k>
         <output> _ => CD </output>
         <callData> CD </callData>

    syntax PrecompiledOp ::= "MODEXP"
 // ---------------------------------
    rule <k> MODEXP => #end EVMC_SUCCESS ... </k>
         <output> _ => #let DATA = CD #in #modexp1(#asWord(#range(DATA, 0, 32)), #asWord(#range(DATA, 32, 32)), #asWord(#range(DATA, 64, 32)), #range(DATA, 96, maxInt(0, lengthBytes(DATA) -Int 96))) </output>
         <callData> CD </callData>

    syntax Bytes ::= #modexp1 ( Int , Int , Int , Bytes ) [symbol(#modexp1), function]
                   | #modexp2 ( Int , Int , Int , Bytes ) [symbol(#modexp2), function]
                   | #modexp3 ( Int , Int , Int , Bytes ) [symbol(#modexp3), function]
                   | #modexp4 ( Int , Int , Int )         [symbol(#modexp4), function]
 // ----------------------------------------------------------------------------------
    rule #modexp1(BASELEN, EXPLEN,   MODLEN, DATA) => #modexp2(#asInteger(#range(DATA, 0, BASELEN)), EXPLEN, MODLEN, #range(DATA, BASELEN, maxInt(0, lengthBytes(DATA) -Int BASELEN))) requires MODLEN =/=Int 0
    rule #modexp1(_,       _,        0,      _)    => .Bytes
    rule #modexp2(BASE,    EXPLEN,   MODLEN, DATA) => #modexp3(BASE, #asInteger(#range(DATA, 0, EXPLEN)), MODLEN, #range(DATA, EXPLEN, maxInt(0, lengthBytes(DATA) -Int EXPLEN)))
    rule #modexp3(BASE,    EXPONENT, MODLEN, DATA) => #padToWidth(MODLEN, #modexp4(BASE, EXPONENT, #asInteger(#range(DATA, 0, MODLEN))))
    rule #modexp4(BASE,    EXPONENT, MODULUS)      => #asByteStack(powmod(BASE, EXPONENT, MODULUS))

    syntax PrecompiledOp ::= "ECADD"
 // --------------------------------
    rule <k> ECADD => #let DATA = CD #in #ecadd((#asWord(#range(DATA, 0, 32)), #asWord(#range(DATA, 32, 32))), (#asWord(#range(DATA, 64, 32)), #asWord(#range(DATA, 96, 32)))) ... </k>
         <callData> CD </callData>

    syntax InternalOp ::= #ecadd(G1Point, G1Point) [symbol(#ecadd)]
 // ---------------------------------------------------------------
    rule <k> #ecadd(P1, P2) => #end EVMC_PRECOMPILE_FAILURE ... </k>
      requires notBool isValidPoint(P1) orBool notBool isValidPoint(P2)
    rule <k> #ecadd(P1, P2) => #end EVMC_SUCCESS ... </k> <output> _ => #point(BN128Add(P1, P2)) </output>
      requires isValidPoint(P1) andBool isValidPoint(P2)

    syntax PrecompiledOp ::= "ECMUL"
 // --------------------------------
    rule <k> ECMUL => #let DATA = CD #in #ecmul((#asWord(#range(DATA, 0, 32)), #asWord(#range(DATA, 32, 32))), #asWord(#range(DATA, 64, 32))) ... </k>
         <callData> CD </callData>

    syntax InternalOp ::= #ecmul(G1Point, Int) [symbol(#ecmul)]
 // -----------------------------------------------------------
    rule <k> #ecmul(P, _S) => #end EVMC_PRECOMPILE_FAILURE ... </k>
      requires notBool isValidPoint(P)
    rule <k> #ecmul(P,  S) => #end EVMC_SUCCESS ... </k> <output> _ => #point(BN128Mul(P, S)) </output>
      requires isValidPoint(P)

    syntax Bytes ::= #point ( G1Point ) [symbol(#point), function]
 // --------------------------------------------------------------
    rule #point((X, Y)) => #padToWidth(32, #asByteStack(X)) +Bytes #padToWidth(32, #asByteStack(Y))

    syntax PrecompiledOp ::= "ECPAIRING"
 // ------------------------------------
    rule <k> ECPAIRING => #ecpairing(.List, .List, 0, CD, lengthBytes(CD)) ... </k>
         <callData> CD </callData>
      requires lengthBytes(CD) modInt 192 ==Int 0
    rule <k> ECPAIRING => #end EVMC_PRECOMPILE_FAILURE ... </k>
         <callData> CD </callData>
      requires lengthBytes(CD) modInt 192 =/=Int 0

    syntax InternalOp ::= #ecpairing(List, List, Int, Bytes, Int) [symbol(#ecpairing)]
 // ----------------------------------------------------------------------------------
    rule <k> (.K => #checkPoint) ~> #ecpairing((.List => ListItem((#asWord(#range(DATA, I, 32)), #asWord(#range(DATA, I +Int 32, 32))))) _, (.List => ListItem((#asWord(#range(DATA, I +Int 96, 32)) x #asWord(#range(DATA, I +Int 64, 32)) , #asWord(#range(DATA, I +Int 160, 32)) x #asWord(#range(DATA, I +Int 128, 32))))) _, I => I +Int 192, DATA, LEN) ... </k>
      requires I =/=Int LEN
    rule <k> #ecpairing(A, B, LEN, _, LEN) => #end EVMC_SUCCESS ... </k>
         <output> _ => #padToWidth(32, #asByteStack(bool2Word(BN128AtePairing(A, B)))) </output>

    syntax InternalOp ::= "#checkPoint"
 // -----------------------------------
    rule <k> (#checkPoint => .K) ~> #ecpairing(ListItem(AK::G1Point) _, ListItem(BK::G2Point) _, _, _, _) ... </k>
      requires isValidPoint(AK) andBool isValidPoint(BK)
    rule <k> #checkPoint ~> #ecpairing(ListItem(AK::G1Point) _, ListItem(BK::G2Point) _, _, _, _) => #end EVMC_PRECOMPILE_FAILURE ... </k>
      requires notBool isValidPoint(AK) orBool notBool isValidPoint(BK)

    syntax PrecompiledOp ::= "BLAKE2F"
 // ----------------------------------
    rule <k> BLAKE2F => #end EVMC_SUCCESS ... </k>
         <output> _ => #parseByteStack( Blake2Compress( CD ) ) </output>
         <callData> CD </callData>
      requires lengthBytes( CD ) ==Int 213
       andBool CD[212] <=Int 1

    rule <k> BLAKE2F => #end EVMC_PRECOMPILE_FAILURE ... </k>
         <callData> CD </callData>
      requires lengthBytes( CD ) ==Int 213
       andBool notBool (CD[212] <=Int 1)

    rule <k> BLAKE2F => #end EVMC_PRECOMPILE_FAILURE ... </k>
         <callData> CD </callData>
      requires lengthBytes( CD ) =/=Int 213

    syntax PrecompiledOp ::= "KZGPOINTEVAL"
 // ---------------------------------------
    // FIELD_ELEMENTS_PER_BLOB = 4096
    rule <k> KZGPOINTEVAL => #end EVMC_SUCCESS ... </k>
         <output> _ => Int2Bytes(32, 4096, BE) +Bytes Int2Bytes(32, blsModulus, BE) </output>
         <callData> CD </callData>
      requires lengthBytes( CD ) ==Int 192
       andBool #kzg2vh(substrBytes(CD, 96, 144)) ==Bytes substrBytes(CD, 0, 32)
       andBool Bytes2Int(substrBytes(CD, 32, 64), BE, Unsigned) <Int blsModulus
       andBool Bytes2Int(substrBytes(CD, 64, 96), BE, Unsigned) <Int blsModulus
       andBool verifyKZGProof(substrBytes(CD, 96, 144), substrBytes(CD, 32, 64), substrBytes(CD, 64, 96), substrBytes(CD, 144, 192))

    rule <k> KZGPOINTEVAL => #end EVMC_PRECOMPILE_FAILURE ... </k>
         <callData> CD </callData>
      requires notBool
             ( lengthBytes( CD ) ==Int 192
       andBool #kzg2vh(substrBytes(CD, 96, 144)) ==Bytes substrBytes(CD, 0, 32)
       andBool Bytes2Int(substrBytes(CD, 32, 64), BE, Unsigned) <Int blsModulus
       andBool Bytes2Int(substrBytes(CD, 64, 96), BE, Unsigned) <Int blsModulus
       andBool verifyKZGProof(substrBytes(CD, 96, 144), substrBytes(CD, 32, 64), substrBytes(CD, 64, 96), substrBytes(CD, 144, 192)))

    syntax Bytes ::= #kzg2vh ( Bytes ) [symbol(#kzg2vh), function, total]
 // ---------------------------------------------------------------------
    // VERSIONED_HASH_VERSION_KZG = 0x01
    rule #kzg2vh ( C ) => Sha256raw(C)[0 <- 1]


    syntax Bytes ::= #bls12point ( G1Point ) [symbol(#bls12point1), function, total]
 // -------------------------------------------------------------------------
    rule #bls12point((X, Y)) => #padToWidth(64, #asByteStack(X)) +Bytes #padToWidth(64, #asByteStack(Y))

    syntax Bytes ::= #bls12point ( G2Point ) [symbol(#bls12point2), function, total]
 // -------------------------------------------------------------------------
    rule #bls12point((X0 x X1, Y0 x Y1))
        => #padToWidth(64, #asByteStack(X0)) +Bytes #padToWidth(64, #asByteStack(X1))
            +Bytes #padToWidth(64, #asByteStack(Y0)) +Bytes #padToWidth(64, #asByteStack(Y1))

    syntax Bool ::= isValidBLS12Coordinate ( Int ) [symbol(isValidBLS12Coordinate), function, total]
  // -----------------------------------------------------------------------------------------------
    rule isValidBLS12Coordinate(X) => isValidBLS12Fp(X)

    syntax Bool ::= isValidBLS12Fp ( Int ) [symbol(isValidBLS12Fp), function, total]
  // -------------------------------------------------------------------------------
    rule isValidBLS12Fp(X) => X >=Int 0 andBool X <Int (1 <<Int 384) andBool X <Int BLS12_FIELD_MODULUS

    syntax Bool ::= isValidBLS12Scalar ( Int ) [symbol(isValidBLS12Scalar), function, total]
  // ---------------------------------------------------------------------------------------
    rule isValidBLS12Scalar(X) => X >=Int 0 andBool X <Int (1 <<Int 256)

    syntax PrecompiledOp ::= "BLS12G1ADD"
 // -------------------------------------
    rule <k> BLS12G1ADD => #end EVMC_SUCCESS ... </k>
         <callData> CD </callData>
         <output>
            _ => #bls12point(BLS12G1Add
                    (   ( Bytes2Int(substrBytes(CD, 0, 64), BE, Unsigned)
                        , Bytes2Int(substrBytes(CD, 64, 128), BE, Unsigned)
                        )
                    ,   ( Bytes2Int(substrBytes(CD, 128, 192), BE, Unsigned)
                        , Bytes2Int(substrBytes(CD, 192, 256), BE, Unsigned)
                        )
                    ))
         </output>
      requires lengthBytes( CD ) ==Int 256
        andBool bls12ValidForAdd
            ( Bytes2Int(substrBytes(CD, 0, 64), BE, Unsigned)
            , Bytes2Int(substrBytes(CD, 64, 128), BE, Unsigned)
            , Bytes2Int(substrBytes(CD, 128, 192), BE, Unsigned)
            , Bytes2Int(substrBytes(CD, 192, 256), BE, Unsigned)
            )

    rule <k> BLS12G1ADD => #end EVMC_PRECOMPILE_FAILURE ... </k>
         <callData> CD </callData>
      requires lengthBytes( CD ) =/=Int 256
        orBool notBool bls12ValidForAdd
            ( Bytes2Int(substrBytes(CD, 0, 64), BE, Unsigned)
            , Bytes2Int(substrBytes(CD, 64, 128), BE, Unsigned)
            , Bytes2Int(substrBytes(CD, 128, 192), BE, Unsigned)
            , Bytes2Int(substrBytes(CD, 192, 256), BE, Unsigned)
            )

    syntax Bool ::= bls12ValidForAdd(Int, Int, Int, Int)  [function, total]
 // -----------------------------------------------------------------------
    rule bls12ValidForAdd(X0, Y0, X1, Y1)
        => true
            andBool isValidBLS12Coordinate(X0)
            andBool isValidBLS12Coordinate(Y0)
            andBool isValidBLS12Coordinate(X1)
            andBool isValidBLS12Coordinate(Y1)
            andBool BLS12G1OnCurve((X0, Y0))
            andBool BLS12G1OnCurve((X1, Y1))

    syntax PrecompiledOp ::= "BLS12G1MSM"
 // -------------------------------------
    // Note that the implementation of `g1_lincomb_fast` has the following comment:
    //
    //  * @remark While this function is significantly faster than g1_lincomb_naive(), we refrain from
    //  * using it in security-critical places (like verification) because the blst Pippenger code has not
    //  * been audited. In those critical places, we prefer using g1_lincomb_naive() which is much simpler.
    //
    // https://github.com/ethereum/c-kzg-4844/blob/cc33b779cd3a227f51b35ce519a83cf91d81ccea/src/common/lincomb.c#L54-L56

    rule <k> BLS12G1MSM => bls12G1Msm(CD) ... </k>
         <callData> CD </callData>

    rule <k> R:G1MsmResult => #end EVMC_SUCCESS ... </k>
         <output>
            _ => #bls12point(g1MsmResult.getPoint(R))
         </output>
      requires R =/=K g1MsmError
    rule <k> g1MsmError => #end EVMC_PRECOMPILE_FAILURE ... </k>

    syntax G1MsmResult ::= "g1MsmError" | g1MsmResult(G1Point)
 // ----------------------------------------------------------
    syntax G1MsmResult ::= bls12G1Msm(Bytes) [symbol(bls12G1Msm), function, total]
    syntax G1MsmResult ::= #bls12G1Msm(Bytes, List, List) [function, total]
    syntax G1MsmResult ::= #bls12G1MsmCheck(Bytes, List, List, Int, Int, Int) [function, total]
 // ----------------------------------------------------------------------------
    rule bls12G1Msm(B:Bytes) => g1MsmError requires lengthBytes(B) ==Int 0
    rule bls12G1Msm(B:Bytes) => #bls12G1Msm(B, .List, .List) requires lengthBytes(B) >Int 0

    rule #bls12G1Msm(B:Bytes, Ps:List, Ss:List) => g1MsmResult(BLS12G1Msm(... scalars: Ss, points: Ps))
        requires lengthBytes(B) ==Int 0
    rule #bls12G1Msm(B:Bytes, _:List, _:List) => g1MsmError
        requires 0 <Int lengthBytes(B) andBool lengthBytes(B) <Int 160
    rule #bls12G1Msm(B:Bytes, Ps:List, Ss:List)
        => #bls12G1MsmCheck
                ( substrBytes(B, 160, lengthBytes(B)), Ps, Ss
                , Bytes2Int(substrBytes(B, 0, 64), BE, Unsigned)
                , Bytes2Int(substrBytes(B, 64, 128), BE, Unsigned)
                , Bytes2Int(substrBytes(B, 128, 160), BE, Unsigned)
                )
        requires 160 <=Int lengthBytes(B)

    rule #bls12G1MsmCheck(B:Bytes, Ps:List, Ss:List, X:Int, Y:Int, N:Int)
        => #bls12G1Msm(B, Ps ListItem( ( X , Y ) ), Ss ListItem( N ))
      requires isValidBLS12Coordinate(X) andBool isValidBLS12Coordinate(Y)
        andBool isValidBLS12Scalar(N)
        andBool BLS12G1InSubgroup((X, Y))
    rule #bls12G1MsmCheck(_, _, _, _, _, _) => g1MsmError  [owise]

    syntax G1Point ::= "g1MsmResult.getPoint" "(" G1MsmResult ")" [function]
    rule g1MsmResult.getPoint(g1MsmResult(P)) => P


    syntax PrecompiledOp ::= "BLS12G2ADD"
 // -------------------------------------
    rule <k> BLS12G2ADD => #end EVMC_SUCCESS ... </k>
        <callData> CD </callData>
        <output>
            _ => #bls12point(BLS12G2Add
                    (   ( Bytes2Int(substrBytes(CD, 0, 64), BE, Unsigned)
                        x Bytes2Int(substrBytes(CD, 64, 128), BE, Unsigned)
                        , Bytes2Int(substrBytes(CD, 128, 192), BE, Unsigned)
                        x Bytes2Int(substrBytes(CD, 192, 256), BE, Unsigned)
                        )
                    ,   ( Bytes2Int(substrBytes(CD, 256, 320), BE, Unsigned)
                        x Bytes2Int(substrBytes(CD, 320, 384), BE, Unsigned)
                        , Bytes2Int(substrBytes(CD, 384, 448), BE, Unsigned)
                        x Bytes2Int(substrBytes(CD, 448, 512), BE, Unsigned)
                        )
                    ))
         </output>
      requires lengthBytes( CD ) ==Int 512
        andBool bls12ValidForAdd2
            ( Bytes2Int(substrBytes(CD, 0, 64), BE, Unsigned)
            , Bytes2Int(substrBytes(CD, 64, 128), BE, Unsigned)
            , Bytes2Int(substrBytes(CD, 128, 192), BE, Unsigned)
            , Bytes2Int(substrBytes(CD, 192, 256), BE, Unsigned)
            , Bytes2Int(substrBytes(CD, 256, 320), BE, Unsigned)
            , Bytes2Int(substrBytes(CD, 320, 384), BE, Unsigned)
            , Bytes2Int(substrBytes(CD, 384, 448), BE, Unsigned)
            , Bytes2Int(substrBytes(CD, 448, 512), BE, Unsigned)
            )

    rule <k> BLS12G2ADD => #end EVMC_PRECOMPILE_FAILURE ... </k>
         <callData> CD </callData>
      requires lengthBytes( CD ) =/=Int 512
        orBool notBool bls12ValidForAdd2
            ( Bytes2Int(substrBytes(CD, 0, 64), BE, Unsigned)
            , Bytes2Int(substrBytes(CD, 64, 128), BE, Unsigned)
            , Bytes2Int(substrBytes(CD, 128, 192), BE, Unsigned)
            , Bytes2Int(substrBytes(CD, 192, 256), BE, Unsigned)
            , Bytes2Int(substrBytes(CD, 256, 320), BE, Unsigned)
            , Bytes2Int(substrBytes(CD, 320, 384), BE, Unsigned)
            , Bytes2Int(substrBytes(CD, 384, 448), BE, Unsigned)
            , Bytes2Int(substrBytes(CD, 448, 512), BE, Unsigned)
            )

    syntax Bool ::= bls12ValidForAdd2(Int, Int, Int, Int, Int, Int, Int, Int)  [function, total]
 // --------------------------------------------------------------------------------------------
    rule bls12ValidForAdd2(PX0, PX1, PY0, PY1, QX0, QX1, QY0, QY1)
        => true
            andBool isValidBLS12Coordinate(PX0)
            andBool isValidBLS12Coordinate(PX1)
            andBool isValidBLS12Coordinate(PY0)
            andBool isValidBLS12Coordinate(PY1)
            andBool isValidBLS12Coordinate(QX0)
            andBool isValidBLS12Coordinate(QX1)
            andBool isValidBLS12Coordinate(QY0)
            andBool isValidBLS12Coordinate(QY1)
            andBool BLS12G2OnCurve((PX0 x PX1, PY0 x PY1))
            andBool BLS12G2OnCurve((QX0 x QX1, QY0 x QY1))

    syntax PrecompiledOp ::= "BLS12G2MSM"
 // -------------------------------------
    rule <k> BLS12G2MSM => bls12G2Msm(CD) ... </k>
         <callData> CD </callData>

    rule <k> R:G2MsmResult => #end EVMC_SUCCESS ... </k>
         <output>
            _ => #bls12point(g2MsmResult.getPoint(R))
         </output>
      requires R =/=K g2MsmError
    rule <k> g2MsmError => #end EVMC_PRECOMPILE_FAILURE ... </k>

    syntax G2MsmResult ::= "g2MsmError" | g2MsmResult(G2Point)
 // ----------------------------------------------------------
    syntax G2MsmResult ::= bls12G2Msm(Bytes) [symbol(bls12G2Msm), function, total]
    syntax G2MsmResult ::= #bls12G2Msm(Bytes, List, List) [function, total]
    syntax G2MsmResult ::= #bls12G2MsmCheck(Bytes, List, List, Int, Int, Int, Int, Int) [function, total]
 // ------------------------------------------------------------------------------------
    rule bls12G2Msm(B:Bytes) => g2MsmError requires lengthBytes(B) ==Int 0
    rule bls12G2Msm(B:Bytes) => #bls12G2Msm(B, .List, .List) requires lengthBytes(B) >Int 0

    rule #bls12G2Msm(B:Bytes, Ps:List, Ss:List) => g2MsmResult(BLS12G2Msm(... scalars: Ss, points: Ps))
        requires lengthBytes(B) ==Int 0
    rule #bls12G2Msm(B:Bytes, _:List, _:List) => g2MsmError
        requires 0 <Int lengthBytes(B) andBool lengthBytes(B) <Int 288
    rule #bls12G2Msm(B:Bytes, Ps:List, Ss:List)
        => #bls12G2MsmCheck
                ( substrBytes(B, 288, lengthBytes(B)), Ps, Ss
                , Bytes2Int(substrBytes(B, 0, 64), BE, Unsigned)
                , Bytes2Int(substrBytes(B, 64, 128), BE, Unsigned)
                , Bytes2Int(substrBytes(B, 128, 192), BE, Unsigned)
                , Bytes2Int(substrBytes(B, 192, 256), BE, Unsigned)
                , Bytes2Int(substrBytes(B, 256, 288), BE, Unsigned)
                )
        requires 288 <=Int lengthBytes(B)

    rule #bls12G2MsmCheck(B:Bytes, Ps:List, Ss:List, X0:Int, X1:Int, Y0:Int, Y1:Int, N:Int)
        => #bls12G2Msm(B, Ps ListItem( ( X0 x X1, Y0 x Y1 ) ), Ss ListItem( N ))
      requires isValidBLS12Coordinate(X0) andBool isValidBLS12Coordinate(X1)
        andBool isValidBLS12Coordinate(Y0) andBool isValidBLS12Coordinate(Y1)
        andBool isValidBLS12Scalar(N)
        andBool BLS12G2InSubgroup(( X0 x X1, Y0 x Y1 ))
    rule #bls12G2MsmCheck(_, _, _, _, _, _, _, _) => g2MsmError  [owise]

    syntax G2Point ::= "g2MsmResult.getPoint" "(" G2MsmResult ")" [function]
    rule g2MsmResult.getPoint(g2MsmResult(P)) => P


    syntax PrecompiledOp ::= "BLS12PAIRING_CHECK"
 // ---------------------------------------------
    rule <k> BLS12PAIRING_CHECK => bls12PairingCheck(CD, .List, .List) ... </k>
         <callData> CD </callData>

    rule <k> R:Bls12PairingResult => #end EVMC_SUCCESS ... </k>
         <output>
            _ => #if bls12PairingResult.get(R) #then Int2Bytes(32, 1, BE:Endianness) #else Int2Bytes(32, 0, BE:Endianness) #fi
         </output>
       requires notBool R ==K bls12PairingError
    rule <k> bls12PairingError => #end EVMC_PRECOMPILE_FAILURE ... </k>

    syntax Bls12PairingResult ::= "bls12PairingError" | bls12PairingResult(Bool)
 // --------------------------------------------------------------------------
    syntax Bls12PairingResult ::= bls12PairingCheck(Bytes, List, List) [symbol(bls12PairingCheck), function, total]
 // -------------------------------------------------------------------------------------------------------------
    rule bls12PairingCheck(B:Bytes, L1:List, L2:List) => bls12PairingResult(BLS12PairingCheck(L1, L2))
        requires lengthBytes(B) ==Int 0
          andBool validBls12G1PairingPoints(L1)
          andBool validBls12G2PairingPoints(L2)
          andBool size(L1) ==Int size(L2)
          andBool size(L1) >Int 0
    rule bls12PairingCheck(B:Bytes, L1:List, L2:List)
        => bls12PairingCheck
            ( substrBytes(B, 384, lengthBytes(B))
            , L1 ListItem(
                ( Bytes2Int(substrBytes(B, 0, 64), BE, Unsigned)
                , Bytes2Int(substrBytes(B, 64, 128), BE, Unsigned)
                )
              )
            , L2 ListItem(
                ( Bytes2Int(substrBytes(B, 128, 192), BE, Unsigned)
                x Bytes2Int(substrBytes(B, 192, 256), BE, Unsigned)
                , Bytes2Int(substrBytes(B, 256, 320), BE, Unsigned)
                x Bytes2Int(substrBytes(B, 320, 384), BE, Unsigned)
                )
              )
            )
      requires lengthBytes(B) >=Int 384
    rule bls12PairingCheck(_:Bytes, _:List, _:List) => bls12PairingError  [owise]

    syntax Bool ::= validBls12G1PairingPoints(List)  [function, total]
    syntax Bool ::= validBls12G1PairingPoint(G1Point)  [function, total]
// ------------------------------------------------------------------
    rule validBls12G1PairingPoints(.List) => true
    rule validBls12G1PairingPoints(ListItem(P:G1Point) L:List) => validBls12G1PairingPoints(L)
      requires validBls12G1PairingPoint(P)
    rule validBls12G1PairingPoints(_) => false  [owise]

    rule validBls12G1PairingPoint((X, Y) #as P:G1Point)
        => isValidBLS12Coordinate(X)
          andBool isValidBLS12Coordinate(Y)
          andBool BLS12G1InSubgroup(P)

    syntax Bool ::= validBls12G2PairingPoints(List)  [function, total]
    syntax Bool ::= validBls12G2PairingPoint(G2Point)  [function, total]
// ------------------------------------------------------------------
    rule validBls12G2PairingPoints(.List) => true
    rule validBls12G2PairingPoints(ListItem(P:G2Point) L:List) => validBls12G2PairingPoints(L)
      requires validBls12G2PairingPoint(P)
    rule validBls12G2PairingPoints(_) => false  [owise]

    rule validBls12G2PairingPoint((X0 x X1, Y0 x Y1) #as P:G2Point)
        => isValidBLS12Coordinate(X0)
          andBool isValidBLS12Coordinate(X1)
          andBool isValidBLS12Coordinate(Y0)
          andBool isValidBLS12Coordinate(Y1)
          andBool BLS12G2InSubgroup(P)

    syntax Bool ::= "bls12PairingResult.get" "(" Bls12PairingResult ")" [function]
    rule bls12PairingResult.get(bls12PairingResult(P)) => P


    syntax PrecompiledOp ::= "BLS12MAPFPTOG1"
 // -----------------------------------------
    rule <k> BLS12MAPFPTOG1 => #end EVMC_SUCCESS ... </k>
         <callData> CD </callData>
         <output>
            _ => #bls12point(BLS12MapFpToG1(Bytes2Int(substrBytes(CD, 0, 64), BE, Unsigned)))
         </output>
      requires lengthBytes( CD ) ==Int 64
        andBool isValidBLS12Fp(Bytes2Int(substrBytes(CD, 0, 64), BE, Unsigned))

    rule <k> BLS12MAPFPTOG1 => #end EVMC_PRECOMPILE_FAILURE ... </k>
         <callData> CD </callData>
      requires lengthBytes( CD ) =/=Int 64
        orBool notBool isValidBLS12Fp(Bytes2Int(substrBytes(CD, 0, 64), BE, Unsigned))


    syntax PrecompiledOp ::= "BLS12MAPFP2TOG2"
 // ------------------------------------------
    rule <k> BLS12MAPFP2TOG2 => #end EVMC_SUCCESS ... </k>
         <callData> CD </callData>
         <output>
            _ => #bls12point(BLS12MapFp2ToG2
                    ( Bytes2Int(substrBytes(CD, 0, 64), BE, Unsigned)
                    , Bytes2Int(substrBytes(CD, 64, 128), BE, Unsigned)
                    ))
         </output>
      requires lengthBytes( CD ) ==Int 128
        andBool isValidBLS12Fp(Bytes2Int(substrBytes(CD, 0, 64), BE, Unsigned))
        andBool isValidBLS12Fp(Bytes2Int(substrBytes(CD, 64, 128), BE, Unsigned))

    rule <k> BLS12MAPFP2TOG2 => #end EVMC_PRECOMPILE_FAILURE ... </k>
         <callData> CD </callData>
      requires lengthBytes( CD ) =/=Int 128
        orBool notBool isValidBLS12Fp(Bytes2Int(substrBytes(CD, 0, 64), BE, Unsigned))
        orBool notBool isValidBLS12Fp(Bytes2Int(substrBytes(CD, 64, 128), BE, Unsigned))

```

Ethereum Gas Calculation
========================

Overall Gas
-----------

-   `#gas` calculates how much gas this operation costs, and takes into account the memory consumed.
-   `#deductGas` is used to check that there won't be a gas underflow (throwing `EVMC_OUT_OF_GAS` if so), and deducts the gas if not.
-   `#deductMemory` checks that access to memory stay within sensible bounds (and deducts the correct amount of gas for it), throwing `EVMC_INVALID_MEMORY_ACCESS` if bad access happens.

```k
    syntax InternalOp ::= "#gas" "[" OpCode "," OpCode "]"
 // ------------------------------------------------------
    rule <k> #gas [ OP , AOP ]
          => #memory [ OP , AOP ]
          ~> #gas [ AOP ]
          ~> #access [ OP , AOP, #isAccess(ACCT, AOP) ]
         ...
        </k>
        <id> ACCT </id>

    rule <k> #gas [ OP ] => #gasExec(SCHED, OP) ~> #deductGas ... </k>
         <schedule> SCHED </schedule>

    rule <k> #memory [ OP , AOP ] => #memory(AOP, MU) ~> #deductMemory ... </k>
         <memoryUsed> MU </memoryUsed>
      requires #usesMemory(OP)

   rule <k> #memory [ _ , _ ] => .K ... </k> [owise]

    syntax InternalOp ::= "#gas"    "[" OpCode "]" | "#deductGas" | "#deductMemoryGas"
                        | "#memory" "[" OpCode "," OpCode "]" | "#deductMemory"
 // ---------------------------------------------------------------------------
    rule <k> MU':Int ~> #deductMemory => (Cmem(SCHED, MU') -Int Cmem(SCHED, MU)) ~> #deductMemoryGas ... </k>
         <memoryUsed> MU => MU' </memoryUsed> <schedule> SCHED </schedule>

    rule <k> _G:Gas ~> (#deductMemoryGas => #deductGas)   ... </k> //Required for verification
    rule <k>  G:Gas ~> #deductGas => #end EVMC_OUT_OF_GAS ... </k> <gas> GAVAIL                  </gas> requires GAVAIL <Gas G
    rule <k>  G:Gas ~> #deductGas => .K                   ... </k> <gas> GAVAIL => GAVAIL -Gas G </gas> requires G <=Gas GAVAIL

    syntax Bool ::= #inStorage     ( Map   , Account , Int ) [symbol(#inStorage), function, total]
                  | #inStorageAux1 ( KItem ,           Int ) [symbol(#inStorageAux1), function, total]
                  | #inStorageAux2 ( Set   ,           Int ) [symbol(#inStorageAux2), function, total]
 // --------------------------------------------------------------------------------------------------
    rule #inStorage(TS, ACCT, KEY) => #inStorageAux1(TS[ACCT], KEY) requires ACCT in_keys(TS)
    rule #inStorage(_, _, _)       => false                         [owise]

    rule #inStorageAux1(KEYS:Set, KEY) => #inStorageAux2(KEYS, KEY)
    rule #inStorageAux1(_, _)          => false                     [owise]

    rule #inStorageAux2(KEYS, KEY) => true  requires KEY in KEYS
    rule #inStorageAux2(_, _)      => false [owise]
```

Memory Consumption
------------------

Memory consumed is tracked to determine the appropriate amount of gas to charge for each operation.
In the YellowPaper, each opcode is defined to consume zero gas unless specified otherwise next to the semantics of the opcode (appendix H).

-   `#memory` computes the new memory size given the old size and next operator (with its arguments).
-   `#memoryUsageUpdate` is the function `M` in appendix H of the YellowPaper which helps track the memory used.

```k
    syntax Int ::= #memory ( OpCode , Int ) [symbol(#memory), function, total]
 // --------------------------------------------------------------------------
    rule #memory ( MLOAD INDEX        , MU ) => #memoryUsageUpdate(MU, MInt2Unsigned(INDEX), 32)
    rule #memory ( MSTORE INDEX _     , MU ) => #memoryUsageUpdate(MU, MInt2Unsigned(INDEX), 32)
    rule #memory ( MSTORE8 INDEX _    , MU ) => #memoryUsageUpdate(MU, MInt2Unsigned(INDEX), 1)
    rule #memory ( MCOPY DST SRC WIDTH, MU ) => #memoryUsageUpdate(MU, MInt2Unsigned(uMaxMInt(DST, SRC)), MInt2Unsigned(WIDTH))

    rule #memory ( SHA3 START WIDTH   , MU ) => #memoryUsageUpdate(MU, MInt2Unsigned(START), MInt2Unsigned(WIDTH))
    rule #memory ( LOG(_) START WIDTH , MU ) => #memoryUsageUpdate(MU, MInt2Unsigned(START), MInt2Unsigned(WIDTH))

    rule #memory ( CODECOPY START _ WIDTH       , MU ) => #memoryUsageUpdate(MU, MInt2Unsigned(START), MInt2Unsigned(WIDTH))
    rule #memory ( EXTCODECOPY _ START _ WIDTH  , MU ) => #memoryUsageUpdate(MU, MInt2Unsigned(START), MInt2Unsigned(WIDTH))
    rule #memory ( CALLDATACOPY START _ WIDTH   , MU ) => #memoryUsageUpdate(MU, MInt2Unsigned(START), MInt2Unsigned(WIDTH))
    rule #memory ( RETURNDATACOPY START _ WIDTH , MU ) => #memoryUsageUpdate(MU, MInt2Unsigned(START), MInt2Unsigned(WIDTH))

    rule #memory ( CREATE  _ START WIDTH   , MU ) => #memoryUsageUpdate(MU, MInt2Unsigned(START), MInt2Unsigned(WIDTH))
    rule #memory ( CREATE2 _ START WIDTH _ , MU ) => #memoryUsageUpdate(MU, MInt2Unsigned(START), MInt2Unsigned(WIDTH))
    rule #memory ( RETURN START WIDTH      , MU ) => #memoryUsageUpdate(MU, MInt2Unsigned(START), MInt2Unsigned(WIDTH))
    rule #memory ( REVERT START WIDTH      , MU ) => #memoryUsageUpdate(MU, MInt2Unsigned(START), MInt2Unsigned(WIDTH))

    rule #memory ( _COP:CallOp     _ _ _ ARGSTART ARGWIDTH RETSTART RETWIDTH , MU ) => #memoryUsageUpdate(#memoryUsageUpdate(MU, MInt2Unsigned(ARGSTART), MInt2Unsigned(ARGWIDTH)), MInt2Unsigned(RETSTART), MInt2Unsigned(RETWIDTH))
    rule #memory ( _CSOP:CallSixOp _ _   ARGSTART ARGWIDTH RETSTART RETWIDTH , MU ) => #memoryUsageUpdate(#memoryUsageUpdate(MU, MInt2Unsigned(ARGSTART), MInt2Unsigned(ARGWIDTH)), MInt2Unsigned(RETSTART), MInt2Unsigned(RETWIDTH))

    rule #memory ( _ , MU ) => MU [owise]

    syntax Bool ::= #usesMemory ( OpCode ) [symbol(#usesMemory), function, total]
 // -----------------------------------------------------------------------------
    rule #usesMemory(_:LogOp)        => true
    rule #usesMemory(_:CallOp)       => true
    rule #usesMemory(_:CallSixOp)    => true
    rule #usesMemory(MLOAD)          => true
    rule #usesMemory(MSTORE)         => true
    rule #usesMemory(MSTORE8)        => true
    rule #usesMemory(SHA3)           => true
    rule #usesMemory(CODECOPY)       => true
    rule #usesMemory(EXTCODECOPY)    => true
    rule #usesMemory(CALLDATACOPY)   => true
    rule #usesMemory(RETURNDATACOPY) => true
    rule #usesMemory(CREATE)         => true
    rule #usesMemory(CREATE2)        => true
    rule #usesMemory(RETURN)         => true
    rule #usesMemory(REVERT)         => true
    rule #usesMemory(MCOPY)          => true
    rule #usesMemory(_)              => false [owise]

    syntax Int ::= #memoryUsageUpdate ( Int , Int , Int ) [symbol(#memoryUsageUpdate), function, total]
 // ---------------------------------------------------------------------------------------------------
    rule #memoryUsageUpdate(MU,     _, WIDTH) => MU                                       requires notBool 0 <Int WIDTH [concrete]
    rule #memoryUsageUpdate(MU, START, WIDTH) => maxInt(MU, (START +Int WIDTH) up/Int 32) requires         0 <Int WIDTH [concrete]
```

Access List Gas
---------------

```k
    syntax Bool ::= #usesAccessList ( OpCode ) [symbol(#usesAccessList), function, total]
 // -------------------------------------------------------------------------------------
    rule #usesAccessList(OP)     => true  requires isAddr1Op(OP)
    rule #usesAccessList(OP)     => true  requires isAddr2Op(OP)
    rule #usesAccessList(SLOAD)  => true
    rule #usesAccessList(SSTORE) => true
    rule #usesAccessList(_)      => false [owise]

    syntax InternalOp ::= "#access" "[" OpCode "," OpCode "," Bool "]"
 // ---------------------------------------------------------
    rule <k> #access [ OP , AOP, ACCESS ] => #gasAccess(SCHED, AOP, ACCESS) ~> #deductGas ... </k>
         <schedule> SCHED </schedule>
      requires Ghasaccesslist << SCHED >> andBool #usesAccessList(OP)

    rule <k> #access [ _ , _ , _ ] => .K ... </k> <schedule> _ </schedule> [owise]

    syntax Bool ::= #isAccess ( MInt{256} , OpCode ) [function, total]
 // ------------------------------------------------------------------
    rule #isAccess(_, EXTCODESIZE ACCT) => AccessedAccount(EvmWord(ACCT))
    rule #isAccess(_, EXTCODECOPY ACCT _ _ _) => AccessedAccount(EvmWord(ACCT))
    rule #isAccess(_, EXTCODEHASH ACCT) => AccessedAccount(EvmWord(ACCT))
    rule #isAccess(_, BALANCE ACCT) => AccessedAccount(EvmWord(ACCT))
    rule #isAccess(_, SELFDESTRUCT ACCT) => AccessedAccount(EvmWord(ACCT))
    rule #isAccess(ACCT, SSTORE INDEX _) => AccessedStorage(EvmWord(ACCT), EvmWord(INDEX))
    rule #isAccess(_, _) => false [owise]

    syntax InternalOp ::= #gasAccess ( Schedule, OpCode, Bool ) [symbol(#gasAccess)]
 // --------------------------------------------------------------------------
    rule <k> #gasAccess(SCHED, EXTCODESIZE _ACCT, ACCESS)       => Caddraccess(SCHED, ACCESS)                                ... </k>
    rule <k> #gasAccess(SCHED, EXTCODECOPY _ACCT _ _ _, ACCESS) => Caddraccess(SCHED, ACCESS)                                ... </k>
    rule <k> #gasAccess(SCHED, EXTCODEHASH _ACCT, ACCESS)       => Caddraccess(SCHED, ACCESS)                                ... </k>
    rule <k> #gasAccess(SCHED, BALANCE _ACCT, ACCESS)           => Caddraccess(SCHED, ACCESS)                                ... </k>
    rule <k> #gasAccess(SCHED, SELFDESTRUCT _ACCT, ACCESS)      => #if ACCESS #then 0 #else Gcoldaccountaccess < SCHED > #fi ... </k>
    rule <k> #gasAccess(_    , SLOAD _, _ACCESS)                => 0                                                         ... </k>
    rule <k> #gasAccess(SCHED, SSTORE _INDEX _, ACCESS)         => #if ACCESS #then 0 #else Gcoldsload < SCHED > #fi         ... </k>
    rule <k> #gasAccess(_    , _, _ACCESS)                      => 0                                                         ... </k> [owise]

```

Execution Gas
-------------

The intrinsic gas calculation mirrors the style of the YellowPaper (appendix H).

-   `#gasExec` loads all the relevant surrounding state and uses that to compute the intrinsic execution gas of each opcode.

-   Gas cost for `TSTORE` is the same as a warm `SSTORE` of a dirty slot (i.e. original value is not new value, original is not current value, currently 100 gas).
-   Gas cost of `TLOAD` is the same as a hot `SLOAD` (value has been read before, currently 100 gas).
-   Gas cost cannot be on par with memory access due to transient storage’s interactions with reverts.
```k
    syntax InternalOp ::= #gasExec ( Schedule , OpCode ) [symbol(#gasExec)]
 // -----------------------------------------------------------------------
    rule <k> #gasExec(SCHED, TLOAD _   ) => Gwarmstorageread < SCHED > ... </k>
    rule <k> #gasExec(SCHED, TSTORE _ _) => Gwarmstoragedirtystore < SCHED > ... </k>

    rule <k> #gasExec(SCHED, SSTORE INDEX NEW) => Csstore(SCHED, MInt2Unsigned(NEW), MInt2Unsigned(unwrapEvmWord(GetAccountStorage(EvmWord(ACCT), EvmWord(INDEX)))), MInt2Unsigned(unwrapEvmWord(GetAccountOrigStorage(EvmWord(ACCT), EvmWord(INDEX))))) ... </k>
         <id> ACCT </id>
         <gas> GAVAIL </gas>
      requires notBool Ghassstorestipend << SCHED >>
        orBool notBool GAVAIL <=Gas Gcallstipend < SCHED >

    rule <k> #gasExec(SCHED, SSTORE _ _ ) => #end EVMC_OUT_OF_GAS ... </k>
         <gas> GAVAIL </gas>
      requires Ghassstorestipend << SCHED >>
       andBool GAVAIL <=Gas Gcallstipend < SCHED >

    rule <k> #gasExec(SCHED, EXP _ W1) => Gexp < SCHED > ... </k>                                                                        requires MInt2Unsigned(W1) <=Int 0
    rule <k> #gasExec(SCHED, EXP _ W1) => Gexp < SCHED > +Int (Gexpbyte < SCHED > *Int (1 +Int (log256Int(MInt2Unsigned(W1))))) ... </k> requires 0 <Int MInt2Unsigned(W1) [preserves-definedness]

    rule <k> #gasExec(SCHED, CALLDATACOPY    _ _ WIDTH) => Gverylow < SCHED > +Int (Gcopy < SCHED > *Int (MInt2Unsigned(WIDTH) up/Int 32)) ... </k>
    rule <k> #gasExec(SCHED, RETURNDATACOPY  _ _ WIDTH) => Gverylow < SCHED > +Int (Gcopy < SCHED > *Int (MInt2Unsigned(WIDTH) up/Int 32)) ... </k>
    rule <k> #gasExec(SCHED, CODECOPY        _ _ WIDTH) => Gverylow < SCHED > +Int (Gcopy < SCHED > *Int (MInt2Unsigned(WIDTH) up/Int 32)) ... </k>
    rule <k> #gasExec(SCHED, MCOPY           _ _ WIDTH) => Gverylow < SCHED > +Int (Gcopy < SCHED > *Int (MInt2Unsigned(WIDTH) up/Int 32)) ... </k>

    rule <k> #gasExec(SCHED, LOG(N) _ WIDTH) => (Glog < SCHED > +Int (Glogdata < SCHED > *Int MInt2Unsigned(WIDTH)) +Int (N *Int Glogtopic < SCHED >)) ... </k>

    syntax Exp ::= #handleCallGas(Schedule, acctNonExistent: BExp, cap: Gas, avail: Gas, value: Int, acct:Int, AccountInfo)  [strict(2)]
 // ------------------------------------------------------------------------------------------------------------------------------------
    rule #handleCallGas(SCHED, ISEMPTY:Bool, GCAP, GAVAIL, VALUE, ACCTTO, ACCTINFO)
          => #let TGT_ACCT = MInt2Unsigned(unwrapEvmWord(delegation(ACCTINFO))) #in
               (Ccallgas(SCHED, ISEMPTY, GCAP, GAVAIL, VALUE, isWarm(ACCTINFO), TGT_ACCT, ACCTTO ==Int TGT_ACCT) ~> #allocateCallGas
                ~> Ccall(SCHED, ISEMPTY, GCAP, GAVAIL, VALUE, isWarm(ACCTINFO), TGT_ACCT, ACCTTO ==Int TGT_ACCT))

    rule <k> #gasExec(SCHED, CALL GCAP ACCTTO VALUE _ _ _ _)
          => #handleCallGas(SCHED, #accountNonexistent(ACCTTO), MInt2Unsigned(GCAP), GAVAIL, MInt2Unsigned(VALUE), MInt2Unsigned(ACCTTO), GetAccountInfoAndWarmIt(EvmWord(ACCTTO)))
         ...
         </k>
         <gas> GAVAIL </gas>

    rule <k> #gasExec(SCHED, CALLCODE GCAP ACCTTO VALUE _ _ _ _)
          => #handleCallGas(SCHED, #accountNonexistent(ACCTID), MInt2Unsigned(GCAP), GAVAIL, MInt2Unsigned(VALUE), MInt2Unsigned(ACCTTO), GetAccountInfoAndWarmIt(EvmWord(ACCTTO)))
         ...
         </k>
         <id> ACCTID </id>
         <gas> GAVAIL </gas>

    rule <k> #gasExec(SCHED, DELEGATECALL GCAP ACCTTO _ _ _ _)
          => #handleCallGas(SCHED, #accountNonexistent(ACCTID), MInt2Unsigned(GCAP), GAVAIL, 0, MInt2Unsigned(ACCTTO), GetAccountInfoAndWarmIt(EvmWord(ACCTTO)))
         ...
         </k>
         <id> ACCTID </id>
         <gas> GAVAIL </gas>

    rule <k> #gasExec(SCHED, STATICCALL GCAP ACCTTO _ _ _ _)
          => #handleCallGas(SCHED, #accountNonexistent(ACCTTO), MInt2Unsigned(GCAP), GAVAIL, 0, MInt2Unsigned(ACCTTO), GetAccountInfoAndWarmIt(EvmWord(ACCTTO)))
         ...
         </k>
         <gas> GAVAIL </gas>

    rule <k> #gasExec(SCHED, SELFDESTRUCT ACCTTO) => Cselfdestruct(SCHED, #accountNonexistent(ACCTTO), MInt2Unsigned(unwrapEvmWord(GetAccountBalance(EvmWord(ACCT))))) ... </k>
         <id> ACCT </id>

    rule <k> #gasExec(SCHED, CREATE _ _ WIDTH)
          => Gcreate < SCHED > +Int Cinitcode(SCHED, MInt2Unsigned(WIDTH)) ~> #deductGas
          ~> #allocateCreateGas ~> 0
         ...
         </k>

    rule <k> #gasExec(SCHED, CREATE2 _ _ WIDTH _)
          => Gcreate < SCHED > +Int Gsha3word < SCHED > *Int (MInt2Unsigned(WIDTH) up/Int 32) +Int Cinitcode(SCHED, MInt2Unsigned(WIDTH)) ~> #deductGas
          ~> #allocateCreateGas ~> 0
         ...
         </k>

    rule <k> #gasExec(SCHED, SHA3 _ WIDTH) => Gsha3 < SCHED > +Int (Gsha3word < SCHED > *Int (MInt2Unsigned(WIDTH) up/Int 32)) ... </k>

    rule <k> #gasExec(SCHED, JUMPDEST)    => Gjumpdest < SCHED >                                           ... </k>
    rule <k> #gasExec(SCHED, SLOAD INDEX) => Csload(SCHED, AccessedStorage(EvmWord(ACCT), EvmWord(INDEX))) ... </k> <id> ACCT </id>

    // Wzero
    rule <k> #gasExec(SCHED, STOP)       => Gzero < SCHED > ... </k>
    rule <k> #gasExec(SCHED, RETURN _ _) => Gzero < SCHED > ... </k>
    rule <k> #gasExec(SCHED, REVERT _ _) => Gzero < SCHED > ... </k>

    // Wbase
    rule <k> #gasExec(SCHED, ADDRESS)        => Gbase < SCHED > ... </k>
    rule <k> #gasExec(SCHED, ORIGIN)         => Gbase < SCHED > ... </k>
    rule <k> #gasExec(SCHED, CALLER)         => Gbase < SCHED > ... </k>
    rule <k> #gasExec(SCHED, CALLVALUE)      => Gbase < SCHED > ... </k>
    rule <k> #gasExec(SCHED, CALLDATASIZE)   => Gbase < SCHED > ... </k>
    rule <k> #gasExec(SCHED, RETURNDATASIZE) => Gbase < SCHED > ... </k>
    rule <k> #gasExec(SCHED, CODESIZE)       => Gbase < SCHED > ... </k>
    rule <k> #gasExec(SCHED, GASPRICE)       => Gbase < SCHED > ... </k>
    rule <k> #gasExec(SCHED, COINBASE)       => Gbase < SCHED > ... </k>
    rule <k> #gasExec(SCHED, TIMESTAMP)      => Gbase < SCHED > ... </k>
    rule <k> #gasExec(SCHED, NUMBER)         => Gbase < SCHED > ... </k>
    rule <k> #gasExec(SCHED, DIFFICULTY)     => Gbase < SCHED > ... </k>
    rule <k> #gasExec(SCHED, PREVRANDAO)     => Gbase < SCHED > ... </k>
    rule <k> #gasExec(SCHED, GASLIMIT)       => Gbase < SCHED > ... </k>
    rule <k> #gasExec(SCHED, BASEFEE)        => Gbase < SCHED > ... </k>
    rule <k> #gasExec(SCHED, BLOBBASEFEE)    => Gbase < SCHED > ... </k>
    rule <k> #gasExec(SCHED, POP _)          => Gbase < SCHED > ... </k>
    rule <k> #gasExec(SCHED, PC)             => Gbase < SCHED > ... </k>
    rule <k> #gasExec(SCHED, PUSHZERO)       => Gbase < SCHED > ... </k>
    rule <k> #gasExec(SCHED, MSIZE)          => Gbase < SCHED > ... </k>
    rule <k> #gasExec(SCHED, GAS)            => Gbase < SCHED > ... </k>
    rule <k> #gasExec(SCHED, CHAINID)        => Gbase < SCHED > ... </k>

    // Wverylow
    rule <k> #gasExec(SCHED, ADD _ _)        => Gverylow < SCHED > ... </k>
    rule <k> #gasExec(SCHED, SUB _ _)        => Gverylow < SCHED > ... </k>
    rule <k> #gasExec(SCHED, NOT _)          => Gverylow < SCHED > ... </k>
    rule <k> #gasExec(SCHED, LT _ _)         => Gverylow < SCHED > ... </k>
    rule <k> #gasExec(SCHED, GT _ _)         => Gverylow < SCHED > ... </k>
    rule <k> #gasExec(SCHED, SLT _ _)        => Gverylow < SCHED > ... </k>
    rule <k> #gasExec(SCHED, SGT _ _)        => Gverylow < SCHED > ... </k>
    rule <k> #gasExec(SCHED, EQ _ _)         => Gverylow < SCHED > ... </k>
    rule <k> #gasExec(SCHED, ISZERO _)       => Gverylow < SCHED > ... </k>
    rule <k> #gasExec(SCHED, AND _ _)        => Gverylow < SCHED > ... </k>
    rule <k> #gasExec(SCHED, EVMOR _ _)      => Gverylow < SCHED > ... </k>
    rule <k> #gasExec(SCHED, XOR _ _)        => Gverylow < SCHED > ... </k>
    rule <k> #gasExec(SCHED, BYTE _ _)       => Gverylow < SCHED > ... </k>
    rule <k> #gasExec(SCHED, SHL _ _)        => Gverylow < SCHED > ... </k>
    rule <k> #gasExec(SCHED, SHR _ _)        => Gverylow < SCHED > ... </k>
    rule <k> #gasExec(SCHED, SAR _ _)        => Gverylow < SCHED > ... </k>
    rule <k> #gasExec(SCHED, CALLDATALOAD _) => Gverylow < SCHED > ... </k>
    rule <k> #gasExec(SCHED, MLOAD _)        => Gverylow < SCHED > ... </k>
    rule <k> #gasExec(SCHED, MSTORE _ _)     => Gverylow < SCHED > ... </k>
    rule <k> #gasExec(SCHED, MSTORE8 _ _)    => Gverylow < SCHED > ... </k>
    rule <k> #gasExec(SCHED, PUSH(_))        => Gverylow < SCHED > ... </k>
    rule <k> #gasExec(SCHED, DUP(_) _)       => Gverylow < SCHED > ... </k>
    rule <k> #gasExec(SCHED, SWAP(_) _)      => Gverylow < SCHED > ... </k>
    rule <k> #gasExec(SCHED, BLOBHASH _)     => Gverylow < SCHED > ... </k>

    // Wlow
    rule <k> #gasExec(SCHED, MUL _ _)        => Glow < SCHED > ... </k>
    rule <k> #gasExec(SCHED, DIV _ _)        => Glow < SCHED > ... </k>
    rule <k> #gasExec(SCHED, SDIV _ _)       => Glow < SCHED > ... </k>
    rule <k> #gasExec(SCHED, MOD _ _)        => Glow < SCHED > ... </k>
    rule <k> #gasExec(SCHED, SMOD _ _)       => Glow < SCHED > ... </k>
    rule <k> #gasExec(SCHED, SIGNEXTEND _ _) => Glow < SCHED > ... </k>
    rule <k> #gasExec(SCHED, SELFBALANCE)    => Glow < SCHED > ... </k>

    // Wmid
    rule <k> #gasExec(SCHED, ADDMOD _ _ _) => Gmid < SCHED > ... </k>
    rule <k> #gasExec(SCHED, MULMOD _ _ _) => Gmid < SCHED > ... </k>
    rule <k> #gasExec(SCHED, JUMP _) => Gmid < SCHED > ... </k>

    // Whigh
    rule <k> #gasExec(SCHED, JUMPI _ _) => Ghigh < SCHED > ... </k>

    rule <k> #gasExec(SCHED, EXTCODECOPY _ _ _ WIDTH) => Cextcodecopy(SCHED, MInt2Unsigned(WIDTH)) ... </k>
    rule <k> #gasExec(SCHED, EXTCODESIZE _)           => Cextcodesize(SCHED)                       ... </k>
    rule <k> #gasExec(SCHED, BALANCE _)               => Cbalance(SCHED)                           ... </k>
    rule <k> #gasExec(SCHED, EXTCODEHASH _)           => Cextcodehash(SCHED)                       ... </k>
    rule <k> #gasExec(SCHED, BLOCKHASH _)             => Gblockhash < SCHED >                      ... </k>

    // Precompiled
    rule <k> #gasExec(_, ECREC)  => 3000 ... </k>
    rule <k> #gasExec(_, SHA256) =>  60 +Int  12 *Int (lengthBytes(CD) up/Int 32) ... </k> <callData> CD </callData>

    rule <k> #gasExec(_, RIP160) => 600 +Int 120 *Int (lengthBytes(CD) up/Int 32) ... </k> <callData> CD </callData>
    rule <k> #gasExec(_, ID)     =>  15 +Int   3 *Int (lengthBytes(CD) up/Int 32) ... </k> <callData> CD </callData>

    rule <k> #gasExec(SCHED, MODEXP) => Cmodexp(SCHED, CD, #asWord(#range(CD, 0, 32) ), #asWord(#range(CD, 32, 32)), #asWord(#range(CD, 64, 32))) ... </k>
         <callData> CD </callData>

    rule <k> #gasExec(SCHED, ECADD)     => Gecadd < SCHED>  ... </k>
    rule <k> #gasExec(SCHED, ECMUL)     => Gecmul < SCHED > ... </k>
   rule <k> #gasExec(SCHED, ECPAIRING) => Gecpairconst < SCHED > +Int (lengthBytes(CD) /Int 192) *Int Gecpaircoeff < SCHED > ... </k> <callData> CD </callData>

    rule <k> #gasExec(SCHED, BLAKE2F)   => Gfround < SCHED > *Int #asWord(#range(CD, 0, 4) ) ... </k> <callData> CD </callData>
    rule <k> #gasExec(SCHED, KZGPOINTEVAL)  => Gpointeval < SCHED > ... </k>
    rule <k> #gasExec(SCHED, BLS12G1ADD)    => Gbls12g1add < SCHED > ... </k>
    rule <k> #gasExec(SCHED, BLS12G1MSM)    => #let N = lengthBytes(CD) /Int 160 #in N *Int Gbls12g1mul < SCHED > *Int Cbls12g1MsmDiscount(SCHED, N) /Int 1000 ... </k> <callData> CD </callData>
    rule <k> #gasExec(SCHED, BLS12G2ADD)    => Gbls12g2add < SCHED > ... </k>
    rule <k> #gasExec(SCHED, BLS12G2MSM)    => #let N = lengthBytes(CD) /Int 288 #in N *Int Gbls12g2mul < SCHED > *Int Cbls12g2MsmDiscount(SCHED, N) /Int 1000 ... </k> <callData> CD </callData>
    rule <k> #gasExec(SCHED, BLS12PAIRING_CHECK)    => #let N = lengthBytes(CD) /Int 384 #in N *Int Gbls12PairingCheckMul < SCHED > +Int Gbls12PairingCheckAdd < SCHED > ... </k> <callData> CD </callData>
    rule <k> #gasExec(SCHED, BLS12MAPFPTOG1) => Gbls12mapfptog1 < SCHED > ... </k>
    rule <k> #gasExec(SCHED, BLS12MAPFP2TOG2) => Gbls12mapfp2tog2 < SCHED > ... </k>
    syntax InternalOp ::= "#allocateCallGas"
 // ----------------------------------------
    rule <k> GCALL:Gas ~> #allocateCallGas => .K ... </k>
         <callGas> _ => GCALL </callGas>

    syntax InternalOp ::= "#allocateCreateGas"
 // ------------------------------------------
    rule <schedule> SCHED </schedule>
         <k> #allocateCreateGas => .K ... </k>
         <gas>     GAVAIL => #if Gstaticcalldepth << SCHED >> #then 0      #else GAVAIL /Gas 64      #fi </gas>
         <callGas> _      => #if Gstaticcalldepth << SCHED >> #then GAVAIL #else #allBut64th(GAVAIL) #fi </callGas>
      [preserves-definedness]
```

There are several helpers for calculating gas (most of them also specified in the YellowPaper).

```k
    syntax Exp     ::= Int | Gas
    syntax KResult ::= Int
    syntax Exp ::= Ccall         ( Schedule , BExp , Gas , Gas , Int , Bool, Int, Bool) [symbol(Ccall), strict(2)]
                 | Ccallgas      ( Schedule , BExp , Gas , Gas , Int , Bool, Int, Bool) [symbol(Ccallgas), strict(2)]
                 | Cselfdestruct ( Schedule , BExp , Int )                    [symbol(Cselfdestruct), strict(2)]
 // ------------------------------------------------------------------------------------------------------------
    rule <k> Ccall(SCHED, ISEMPTY:Bool, GCAP, GAVAIL, VALUE, ISWARM, TGT_ACCT, SELF_DLGT)
          =>      Cextra(SCHED, ISEMPTY, VALUE, ISWARM, #isDelegated(TGT_ACCT), #isWarmDelegatee(TGT_ACCT, SELF_DLGT))
             +Gas Cgascap(SCHED, GCAP, GAVAIL, Cextra(SCHED, ISEMPTY, VALUE, ISWARM, #isDelegated(TGT_ACCT), #isWarmDelegatee(TGT_ACCT, SELF_DLGT))) ... </k>

    rule <k> Ccallgas(SCHED, ISEMPTY:Bool, GCAP, GAVAIL, VALUE, ISWARM, TGT_ACCT, SELF_DLGT)
          => Cgascap(SCHED, GCAP, GAVAIL, Cextra(SCHED, ISEMPTY, VALUE, ISWARM, #isDelegated(TGT_ACCT), #isWarmDelegatee(TGT_ACCT, SELF_DLGT))) +Gas #if VALUE ==Int 0 #then 0 #else Gcallstipend < SCHED > #fi ... </k>

    rule <k> Cselfdestruct(SCHED, ISEMPTY:Bool, BAL)
          => Gselfdestruct < SCHED > +Int Cnew(SCHED, ISEMPTY andBool Gselfdestructnewaccount << SCHED >>, BAL) ... </k>

    syntax Bool ::= #isWarmDelegatee(Int, Bool) [macro]
 // ---------------------------------------------------
    rule #isWarmDelegatee(TGT_ACCT, SELF_DLGT)
      => #isDelegated(TGT_ACCT) andThenBool (SELF_DLGT orElseBool AccessedAccount(EvmWord(Int2MInt(TGT_ACCT)::MInt{256})))

    syntax Bool ::= #isDelegated(Int) [macro]
 // -----------------------------------------
    rule #isDelegated(TGT_ACCT) => TGT_ACCT >Int 0

    syntax BExp    ::= Bool
    syntax KResult ::= Bool
    syntax BExp ::= #accountNonexistent ( MInt{256} ) [symbol(#accountNonexistent)]
 // -------------------------------------------------------------------------------
    rule <k> #accountNonexistent(ACCT) => IsAccountEmpty(EvmWord(ACCT)) andBool Gemptyisnonexistent << SCHED >> ... </k>
         <schedule> SCHED </schedule>
      requires AccountExists(EvmWord(ACCT))

   rule <k> #accountNonexistent(_) => true ... </k> [owise]
```

EVM Program Representations
===========================

EVM programs are represented algebraically in K, but programs can load and manipulate program data directly.
The opcodes `CODECOPY` and `EXTCODECOPY` rely on the assembled form of the programs being present.
The opcode `CREATE` relies on being able to interpret EVM data as a program.

This is a program representation dependence, which we might want to avoid.
Perhaps the only program representation dependence we should have is the hash of the program; doing so achieves:

-   Program representation independence (different analysis tools on the language don't have to ensure they have a common representation of programs, just a common interpretation of the data-files holding programs).
-   Programming language independence (we wouldn't even have to commit to a particular language or interpretation of the data-file).
-   Only depending on the hash allows us to know that we have *exactly* the correct data-file (program), and nothing more.

Disassembler
------------

After interpreting the strings representing programs as a `WordStack`, it should be changed into an `OpCodes` for use by the EVM semantics.

-   `#dasmOpCode` interprets a `Int` as an `OpCode`.

```k
    syntax OpCode ::= #dasmOpCode ( MInt{256} , Schedule ) [symbol(#dasmOpCode), function, memo, total]
 // ---------------------------------------------------------------------------------------------------
    rule #dasmOpCode(   0p256,     _ ) => STOP
    rule #dasmOpCode(   1p256,     _ ) => ADD
    rule #dasmOpCode(   2p256,     _ ) => MUL
    rule #dasmOpCode(   3p256,     _ ) => SUB
    rule #dasmOpCode(   4p256,     _ ) => DIV
    rule #dasmOpCode(   5p256,     _ ) => SDIV
    rule #dasmOpCode(   6p256,     _ ) => MOD
    rule #dasmOpCode(   7p256,     _ ) => SMOD
    rule #dasmOpCode(   8p256,     _ ) => ADDMOD
    rule #dasmOpCode(   9p256,     _ ) => MULMOD
    rule #dasmOpCode(  10p256,     _ ) => EXP
    rule #dasmOpCode(  11p256,     _ ) => SIGNEXTEND
    rule #dasmOpCode(  16p256,     _ ) => LT
    rule #dasmOpCode(  17p256,     _ ) => GT
    rule #dasmOpCode(  18p256,     _ ) => SLT
    rule #dasmOpCode(  19p256,     _ ) => SGT
    rule #dasmOpCode(  20p256,     _ ) => EQ
    rule #dasmOpCode(  21p256,     _ ) => ISZERO
    rule #dasmOpCode(  22p256,     _ ) => AND
    rule #dasmOpCode(  23p256,     _ ) => EVMOR
    rule #dasmOpCode(  24p256,     _ ) => XOR
    rule #dasmOpCode(  25p256,     _ ) => NOT
    rule #dasmOpCode(  26p256,     _ ) => BYTE
    rule #dasmOpCode(  27p256, SCHED ) => SHL requires Ghasshift << SCHED >>
    rule #dasmOpCode(  28p256, SCHED ) => SHR requires Ghasshift << SCHED >>
    rule #dasmOpCode(  29p256, SCHED ) => SAR requires Ghasshift << SCHED >>
    rule #dasmOpCode(  32p256,     _ ) => SHA3
    rule #dasmOpCode(  48p256,     _ ) => ADDRESS
    rule #dasmOpCode(  49p256,     _ ) => BALANCE
    rule #dasmOpCode(  50p256,     _ ) => ORIGIN
    rule #dasmOpCode(  51p256,     _ ) => CALLER
    rule #dasmOpCode(  52p256,     _ ) => CALLVALUE
    rule #dasmOpCode(  53p256,     _ ) => CALLDATALOAD
    rule #dasmOpCode(  54p256,     _ ) => CALLDATASIZE
    rule #dasmOpCode(  55p256,     _ ) => CALLDATACOPY
    rule #dasmOpCode(  56p256,     _ ) => CODESIZE
    rule #dasmOpCode(  57p256,     _ ) => CODECOPY
    rule #dasmOpCode(  58p256,     _ ) => GASPRICE
    rule #dasmOpCode(  59p256,     _ ) => EXTCODESIZE
    rule #dasmOpCode(  60p256,     _ ) => EXTCODECOPY
    rule #dasmOpCode(  61p256, SCHED ) => RETURNDATASIZE requires Ghasreturndata  << SCHED >>
    rule #dasmOpCode(  62p256, SCHED ) => RETURNDATACOPY requires Ghasreturndata  << SCHED >>
    rule #dasmOpCode(  63p256, SCHED ) => EXTCODEHASH    requires Ghasextcodehash << SCHED >>
    rule #dasmOpCode(  64p256,     _ ) => BLOCKHASH
    rule #dasmOpCode(  65p256,     _ ) => COINBASE
    rule #dasmOpCode(  66p256,     _ ) => TIMESTAMP
    rule #dasmOpCode(  67p256,     _ ) => NUMBER
    rule #dasmOpCode(  68p256, SCHED ) => PREVRANDAO  requires         Ghasprevrandao << SCHED >>
    rule #dasmOpCode(  68p256, SCHED ) => DIFFICULTY  requires notBool Ghasprevrandao << SCHED >>
    rule #dasmOpCode(  69p256,     _ ) => GASLIMIT
    rule #dasmOpCode(  70p256, SCHED ) => CHAINID     requires Ghaschainid     << SCHED >>
    rule #dasmOpCode(  71p256, SCHED ) => SELFBALANCE requires Ghasselfbalance << SCHED >>
    rule #dasmOpCode(  72p256, SCHED ) => BASEFEE     requires Ghasbasefee     << SCHED >>
    rule #dasmOpCode(  73p256, SCHED ) => BLOBHASH    requires Ghasblobhash    << SCHED >>
    rule #dasmOpCode(  74p256, SCHED ) => BLOBBASEFEE requires Ghasblobbasefee << SCHED >>
    rule #dasmOpCode(  80p256,     _ ) => POP
    rule #dasmOpCode(  81p256,     _ ) => MLOAD
    rule #dasmOpCode(  82p256,     _ ) => MSTORE
    rule #dasmOpCode(  83p256,     _ ) => MSTORE8
    rule #dasmOpCode(  84p256,     _ ) => SLOAD
    rule #dasmOpCode(  85p256,     _ ) => SSTORE
    rule #dasmOpCode(  86p256,     _ ) => JUMP
    rule #dasmOpCode(  87p256,     _ ) => JUMPI
    rule #dasmOpCode(  88p256,     _ ) => PC
    rule #dasmOpCode(  89p256,     _ ) => MSIZE
    rule #dasmOpCode(  90p256,     _ ) => GAS
    rule #dasmOpCode(  91p256,     _ ) => JUMPDEST
    rule #dasmOpCode(  92p256, SCHED ) => TLOAD    requires Ghastransient << SCHED >>
    rule #dasmOpCode(  93p256, SCHED ) => TSTORE   requires Ghastransient << SCHED >>
    rule #dasmOpCode(  94p256, SCHED ) => MCOPY    requires Ghasmcopy     << SCHED >>
    rule #dasmOpCode(  95p256, SCHED ) => PUSHZERO requires Ghaspushzero  << SCHED >>
    rule #dasmOpCode(  96p256,     _ ) => PUSH(1)
    rule #dasmOpCode(  97p256,     _ ) => PUSH(2)
    rule #dasmOpCode(  98p256,     _ ) => PUSH(3)
    rule #dasmOpCode(  99p256,     _ ) => PUSH(4)
    rule #dasmOpCode( 100p256,     _ ) => PUSH(5)
    rule #dasmOpCode( 101p256,     _ ) => PUSH(6)
    rule #dasmOpCode( 102p256,     _ ) => PUSH(7)
    rule #dasmOpCode( 103p256,     _ ) => PUSH(8)
    rule #dasmOpCode( 104p256,     _ ) => PUSH(9)
    rule #dasmOpCode( 105p256,     _ ) => PUSH(10)
    rule #dasmOpCode( 106p256,     _ ) => PUSH(11)
    rule #dasmOpCode( 107p256,     _ ) => PUSH(12)
    rule #dasmOpCode( 108p256,     _ ) => PUSH(13)
    rule #dasmOpCode( 109p256,     _ ) => PUSH(14)
    rule #dasmOpCode( 110p256,     _ ) => PUSH(15)
    rule #dasmOpCode( 111p256,     _ ) => PUSH(16)
    rule #dasmOpCode( 112p256,     _ ) => PUSH(17)
    rule #dasmOpCode( 113p256,     _ ) => PUSH(18)
    rule #dasmOpCode( 114p256,     _ ) => PUSH(19)
    rule #dasmOpCode( 115p256,     _ ) => PUSH(20)
    rule #dasmOpCode( 116p256,     _ ) => PUSH(21)
    rule #dasmOpCode( 117p256,     _ ) => PUSH(22)
    rule #dasmOpCode( 118p256,     _ ) => PUSH(23)
    rule #dasmOpCode( 119p256,     _ ) => PUSH(24)
    rule #dasmOpCode( 120p256,     _ ) => PUSH(25)
    rule #dasmOpCode( 121p256,     _ ) => PUSH(26)
    rule #dasmOpCode( 122p256,     _ ) => PUSH(27)
    rule #dasmOpCode( 123p256,     _ ) => PUSH(28)
    rule #dasmOpCode( 124p256,     _ ) => PUSH(29)
    rule #dasmOpCode( 125p256,     _ ) => PUSH(30)
    rule #dasmOpCode( 126p256,     _ ) => PUSH(31)
    rule #dasmOpCode( 127p256,     _ ) => PUSH(32)
    rule #dasmOpCode( 128p256,     _ ) => DUP(1)
    rule #dasmOpCode( 129p256,     _ ) => DUP(2)
    rule #dasmOpCode( 130p256,     _ ) => DUP(3)
    rule #dasmOpCode( 131p256,     _ ) => DUP(4)
    rule #dasmOpCode( 132p256,     _ ) => DUP(5)
    rule #dasmOpCode( 133p256,     _ ) => DUP(6)
    rule #dasmOpCode( 134p256,     _ ) => DUP(7)
    rule #dasmOpCode( 135p256,     _ ) => DUP(8)
    rule #dasmOpCode( 136p256,     _ ) => DUP(9)
    rule #dasmOpCode( 137p256,     _ ) => DUP(10)
    rule #dasmOpCode( 138p256,     _ ) => DUP(11)
    rule #dasmOpCode( 139p256,     _ ) => DUP(12)
    rule #dasmOpCode( 140p256,     _ ) => DUP(13)
    rule #dasmOpCode( 141p256,     _ ) => DUP(14)
    rule #dasmOpCode( 142p256,     _ ) => DUP(15)
    rule #dasmOpCode( 143p256,     _ ) => DUP(16)
    rule #dasmOpCode( 144p256,     _ ) => SWAP(1)
    rule #dasmOpCode( 145p256,     _ ) => SWAP(2)
    rule #dasmOpCode( 146p256,     _ ) => SWAP(3)
    rule #dasmOpCode( 147p256,     _ ) => SWAP(4)
    rule #dasmOpCode( 148p256,     _ ) => SWAP(5)
    rule #dasmOpCode( 149p256,     _ ) => SWAP(6)
    rule #dasmOpCode( 150p256,     _ ) => SWAP(7)
    rule #dasmOpCode( 151p256,     _ ) => SWAP(8)
    rule #dasmOpCode( 152p256,     _ ) => SWAP(9)
    rule #dasmOpCode( 153p256,     _ ) => SWAP(10)
    rule #dasmOpCode( 154p256,     _ ) => SWAP(11)
    rule #dasmOpCode( 155p256,     _ ) => SWAP(12)
    rule #dasmOpCode( 156p256,     _ ) => SWAP(13)
    rule #dasmOpCode( 157p256,     _ ) => SWAP(14)
    rule #dasmOpCode( 158p256,     _ ) => SWAP(15)
    rule #dasmOpCode( 159p256,     _ ) => SWAP(16)
    rule #dasmOpCode( 160p256,     _ ) => LOG(0)
    rule #dasmOpCode( 161p256,     _ ) => LOG(1)
    rule #dasmOpCode( 162p256,     _ ) => LOG(2)
    rule #dasmOpCode( 163p256,     _ ) => LOG(3)
    rule #dasmOpCode( 164p256,     _ ) => LOG(4)
    rule #dasmOpCode( 240p256,     _ ) => CREATE
    rule #dasmOpCode( 241p256,     _ ) => CALL
    rule #dasmOpCode( 242p256,     _ ) => CALLCODE
    rule #dasmOpCode( 243p256,     _ ) => RETURN
    rule #dasmOpCode( 244p256, SCHED ) => DELEGATECALL requires SCHED =/=K FRONTIER
    rule #dasmOpCode( 245p256, SCHED ) => CREATE2      requires Ghascreate2    << SCHED >>
    rule #dasmOpCode( 250p256, SCHED ) => STATICCALL   requires Ghasstaticcall << SCHED >>
    rule #dasmOpCode( 253p256, SCHED ) => REVERT       requires Ghasrevert     << SCHED >>
    rule #dasmOpCode( 254p256,     _ ) => INVALID
    rule #dasmOpCode( 255p256,     _ ) => SELFDESTRUCT
    rule #dasmOpCode(       W,     _ ) => UNDEFINED(MInt2Unsigned(W)) [owise]

endmodule
```
