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
requires "ulm.k"

module EVM
    imports STRING
    imports EVM-DATA
    imports NETWORK
    imports GAS
    imports ULM
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

            <callState>
              <program>   .Bytes </program>
              <jumpDests> .Bytes </jumpDests>

              // \mu_*
              <wordStack>   .List  </wordStack>           // \mu_s
              <localMem>    .Bytes </localMem>            // \mu_m
              <pc>          0      </pc>                  // \mu_pc
              <gas>         $GAS:Int </gas>                 // \mau_g
              <memoryUsed>  0      </memoryUsed>          // \mu_i
              <callGas>     0:Gas  </callGas>

              <static>    $STATIC:Bool </static>
            </callState>

            // Immutable during a single transaction
            // -------------------------------------
          </evm>
        </ethereum>

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

    syntax MaybeOpCode ::= "#lookupOpCode" "(" Bytes "," Int "," Schedule ")" [function, total]
 // -------------------------------------------------------------------------------------------
    rule #lookupOpCode(BA, I, SCHED) => #dasmOpCode(BA[I], SCHED) requires 0 <=Int I andBool I <Int lengthBytes(BA)
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
    syntax Bool ::= #changesState ( OpCode , List ) [symbol(#changesState), function]
 // ---------------------------------------------------------------------------------
```

```k
    rule #changesState(CALL         , ListItem(_) ListItem(_) ListItem(VALUE) _) => true  requires VALUE =/=Int 0
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

    syntax InternalOp ::= UnStackOp   Int
                        | BinStackOp  Int Int
                        | TernStackOp Int Int Int
                        | QuadStackOp Int Int Int Int
 // -------------------------------------------------
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
    syntax InternalOp ::= CallSixOp Int Int     Int Int Int Int
                        | CallOp    Int Int Int Int Int Int Int
 // -----------------------------------------------------------
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
         <wordStack> WS => WS [ 0 <- #addr({WS [ 0 ]}:>Int) ] </wordStack>
      requires isAddr1Op(OP)

    rule <k> #addr [ OP:OpCode ] => .K ... </k>
         <wordStack> WS => WS [ 1 <- #addr({WS [ 1 ]}:>Int) ] </wordStack>
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
         <pc> PCOUNT => PCOUNT +Int #widthOp(OP) </pc>

    syntax Int ::= #widthOp ( OpCode ) [symbol(#widthOp), function, total]
 // ----------------------------------------------------------------------
    rule #widthOp(PUSH(N)) => 1 +Int N
    rule #widthOp(_)       => 1        [owise]
```

### Block processing

-   `#startBlock` is used to signal that we are about to start mining a block and block initialization should take place (before transactions are executed).
-   `#finalizeBlock` is used to signal that block finalization procedures should take place (after transactions have executed).
-   `#rewardOmmers(_)` pays out the reward to uncle blocks so that blocks are orphaned less often in Ethereum.

```k
    syntax Bytes ::= #bloomFilter(List)      [symbol(#bloomFilter), function]
                   | #bloomFilter(List, Int) [symbol(#bloomFilterAux), function]
 // ----------------------------------------------------------------------------
    rule #bloomFilter(L) => #bloomFilter(L, 0)

    rule #bloomFilter(.List, B) => #padToWidth(256, #asByteStack(B))
    rule #bloomFilter(ListItem({ ACCT | TOPICS | _ }) L, B) => #bloomFilter(ListItem(#padToWidth(20, #asByteStack(ACCT))) listAsBytes(TOPICS) L, B)

    syntax List ::= listAsBytes(List) [symbol(listAsBytes), function]
 // -----------------------------------------------------------------
    rule listAsBytes(.List) => .List
    rule listAsBytes(ListItem(TOPIC) L) => ListItem(#padToWidth(32, #asByteStack(TOPIC))) listAsBytes(L)

    rule #bloomFilter(ListItem(WS:Bytes) L, B) => #bloomFilter(L, B |Int M3:2048(WS))
```

- `M3:2048` computes the 2048-bit hash of a log entry in which exactly 3 bits are set. This is used to compute the Bloom filter of a log entry.

```k
    syntax Int ::= "M3:2048" "(" Bytes ")" [function]
 // -------------------------------------------------
    rule M3:2048(WS) => setBloomFilterBits(#parseByteStack(Keccak256(WS)))

    syntax Int ::= setBloomFilterBits(Bytes) [symbol(setBloomFilterBits), function]
 // -------------------------------------------------------------------------------
    rule setBloomFilterBits(HASH) => (1 <<Int getBloomFilterBit(HASH, 0)) |Int (1 <<Int getBloomFilterBit(HASH, 2)) |Int (1 <<Int getBloomFilterBit(HASH, 4))

    syntax Int ::= getBloomFilterBit(Bytes, Int) [symbol(getBloomFilterBit), function]
 // ----------------------------------------------------------------------------------
    rule getBloomFilterBit(X, I) => #asInteger(#range(X, I, 2)) %Int 2048
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
    rule <k> W0:Int ~> #push => .K ... </k> <wordStack> WS => pushList(W0, WS) </wordStack>
    rule <k> #setStack WS    => .K ... </k> <wordStack> _  => WS      </wordStack>
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
    rule <k> PUSHZERO => 0 ~> #push ... </k>

    rule <k> PUSH(N) => #asWord(#range(PGM, PCOUNT +Int 1, N)) ~> #push ... </k>
         <pc> PCOUNT </pc>
         <program> PGM </program>
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
    rule <k> MSTORE INDEX VALUE => .K ... </k>
         <localMem> LM => LM [ INDEX := #padToWidth(32, #asByteStack(VALUE)) ] </localMem>

    rule <k> MSTORE8 INDEX VALUE => .K ... </k>
         <localMem> LM => #write(LM, INDEX, (VALUE modInt 256)) </localMem>

    syntax TernStackOp ::= "MCOPY"
 // ------------------------------
     rule <k> MCOPY DST SRC LEN => .K ... </k>
          <localMem> LM => LM [ DST := #range(LM, SRC, LEN) ] </localMem>
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
    syntax NullStackOp ::= "PC" | "GAS" | "GASPRICE" | "GASLIMIT" | "BASEFEE" | "BLOBBASEFEE"
 // -----------------------------------------------------------------------------------------
    rule <k> PC          => PCOUNT          ~> #push ... </k> <pc> PCOUNT </pc>
    rule <k> GAS         => gas2Int(GAVAIL) ~> #push ... </k> <gas> GAVAIL </gas>
    rule <k> GASPRICE    => GasPrice()      ~> #push ... </k>
    rule <k> GASLIMIT    => GasLimit()      ~> #push ... </k>
    rule <k> BASEFEE     => BaseFee()       ~> #push ... </k>
    rule <k> BLOBBASEFEE => BlobBaseFee()   ~> #push ... </k>

    syntax NullStackOp ::= "COINBASE" | "TIMESTAMP" | "NUMBER" | "DIFFICULTY" | "PREVRANDAO"
 // ----------------------------------------------------------------------------------------
    rule <k> COINBASE   => Coinbase()        ~> #push ... </k>
    rule <k> TIMESTAMP  => BlockTimestamp()  ~> #push ... </k>
    rule <k> NUMBER     => BlockNumber()     ~> #push ... </k>
    rule <k> DIFFICULTY => BlockDifficulty() ~> #push ... </k>
    rule <k> PREVRANDAO => PrevRandao()      ~> #push ... </k>

    syntax NullStackOp ::= "ADDRESS" | "ORIGIN" | "CALLER" | "CALLVALUE" | "CHAINID" | "SELFBALANCE"
 // ------------------------------------------------------------------------------------------------
    rule <k> ADDRESS     => Address()   ~> #push ... </k>
    rule <k> ORIGIN      => Origin()    ~> #push ... </k>
    rule <k> CALLER      => Caller()    ~> #push ... </k>
    rule <k> CALLVALUE   => CallValue() ~> #push ... </k>
    rule <k> CHAINID     => ChainId()   ~> #push ... </k>
    rule <k> SELFBALANCE => GetAccountBalance(Address()) ~> #push ... </k>

    syntax NullStackOp ::= "MSIZE" | "CODESIZE"
 // -------------------------------------------
    rule <k> MSIZE    => 32 *Word MU         ~> #push ... </k> <memoryUsed> MU </memoryUsed>
    rule <k> CODESIZE => lengthBytes(PGM) ~> #push ... </k> <program> PGM </program>

    syntax TernStackOp ::= "CODECOPY"
 // ---------------------------------
    rule <k> CODECOPY MEMSTART PGMSTART WIDTH => .K ... </k>
         <program> PGM </program>
         <localMem> LM =>  LM [ MEMSTART := #range(PGM, PGMSTART, WIDTH) ] </localMem>

    syntax UnStackOp ::= "BLOCKHASH"
 // --------------------------------
```

The blockhash is calculated here using the "shortcut" formula used for running tests.

```k
    rule <k> BLOCKHASH N => BlockHash(N) ~> #push ... </k>
```

```k
    syntax UnStackOp ::= "BLOBHASH"
 // -------------------------------

    rule <k> BLOBHASH INDEX => 0 ~> #push ... </k>
       requires INDEX >=Int BlobHashesSize()

    rule <k> BLOBHASH INDEX => BlobHash(INDEX) ~> #push ... </k>
       requires INDEX <Int BlobHashesSize()
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
      requires DEST <Int lengthBytes(DESTS) andBool DESTS[DEST] ==Int 1

    rule <k> JUMP _ => #end EVMC_BAD_JUMP_DESTINATION ... </k> [owise]

    syntax BinStackOp ::= "JUMPI"
 // -----------------------------
    rule [jumpi.false]: <k> JUMPI _DEST I => .K        ... </k> requires I  ==Int 0
    rule [jumpi.true]:  <k> JUMPI  DEST I => JUMP DEST ... </k> requires I =/=Int 0

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
    rule <k> CALLDATASIZE => lengthBytes(CallData()) ~> #push ... </k>

    syntax UnStackOp ::= "CALLDATALOAD"
 // -----------------------------------
    rule <k> CALLDATALOAD DATASTART => #asWord(#range(CallData(), DATASTART, 32)) ~> #push ... </k>

    syntax TernStackOp ::= "CALLDATACOPY"
 // -------------------------------------
    rule <k> CALLDATACOPY MEMSTART DATASTART DATAWIDTH => .K ... </k>
         <localMem> LM => LM [ MEMSTART := #range(CallData(), DATASTART, DATAWIDTH) ] </localMem>
```

### Return Data

These operators query about the current return data buffer.

```k
    syntax NullStackOp ::= "RETURNDATASIZE"
 // ---------------------------------------
    rule <k> RETURNDATASIZE => lengthBytes(RD) ~> #push ... </k>
         <output> RD </output>

    syntax TernStackOp ::= "RETURNDATACOPY"
 // ---------------------------------------
    rule <k> RETURNDATACOPY MEMSTART DATASTART DATAWIDTH => .K ... </k>
         <localMem> LM => LM [ MEMSTART := #range(RD, DATASTART, DATAWIDTH) ] </localMem>
         <output> RD </output>
      requires DATASTART +Int DATAWIDTH <=Int lengthBytes(RD)

    rule <k> RETURNDATACOPY _MEMSTART DATASTART DATAWIDTH => #end EVMC_INVALID_MEMORY_ACCESS ... </k>
         <output> RD </output>
      requires DATASTART +Int DATAWIDTH >Int lengthBytes(RD)
```

### Log Operations

```k
    syntax BinStackOp ::= LogOp
    syntax LogOp ::= LOG ( Int ) [symbol(LOG)]
 // ------------------------------------------
    rule <k> LOG(0) MEMSTART MEMWIDTH => Log0(#range(LM, MEMSTART, MEMWIDTH)) ...</k>
         <localMem> LM </localMem>
    rule <k> LOG(1) MEMSTART MEMWIDTH => Log1(T1, #range(LM, MEMSTART, MEMWIDTH)) ...</k>
         <wordStack> ListItem(T1) WS => WS </wordStack>
         <localMem> LM </localMem>
    rule <k> LOG(2) MEMSTART MEMWIDTH => Log2(T1, T2, #range(LM, MEMSTART, MEMWIDTH)) ...</k>
         <wordStack> ListItem(T1) ListItem(T2) WS => WS </wordStack>
         <localMem> LM </localMem>
    rule <k> LOG(3) MEMSTART MEMWIDTH => Log3(T1, T2, T3, #range(LM, MEMSTART, MEMWIDTH)) ...</k>
         <wordStack> ListItem(T1) ListItem(T2) ListItem(T3) WS => WS </wordStack>
         <localMem> LM </localMem>
    rule <k> LOG(4) MEMSTART MEMWIDTH => Log4(T1, T2, T3, T4, #range(LM, MEMSTART, MEMWIDTH)) ...</k>
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
    rule <k> BALANCE ACCT => GetAccountBalance(ACCT) ~> #push ... </k>

    syntax UnStackOp ::= "EXTCODESIZE"
 // ----------------------------------
    rule <k> EXTCODESIZE ACCT => lengthBytes(GetAccountCode(ACCT)) ~> #push ... </k>

    syntax UnStackOp ::= "EXTCODEHASH"
 // ----------------------------------
    rule <k> EXTCODEHASH ACCT => keccak(GetAccountCode(ACCT)) ~> #push ... </k>
      requires notBool IsAccountEmpty(ACCT)

    rule <k> EXTCODEHASH ACCT => AccessAccount(ACCT) ~> 0 ~> #push ... </k> [owise]

    syntax QuadStackOp ::= "EXTCODECOPY"
 // ------------------------------------
    rule <k> EXTCODECOPY ACCT MEMSTART PGMSTART WIDTH => .K ... </k>
         <localMem> LM => LM [ MEMSTART := #range(GetAccountCode(ACCT), PGMSTART, WIDTH) ] </localMem>
```

### Account Storage Operations

These rules reach into the network state and load/store from account storage:

```k
    syntax UnStackOp ::= "SLOAD"
 // ----------------------------
    rule [sload]:
         <k> SLOAD INDEX => GetAccountStorage(INDEX) ~> #push ... </k>

    syntax BinStackOp ::= "SSTORE"
 // ------------------------------
    rule [sstore]:
         <k> SSTORE INDEX NEW => SetAccountStorage(INDEX, NEW) ... </k>
      [preserves-definedness]

    syntax UnStackOp ::= "TLOAD"
 // ----------------------------
    rule [tload]:
         <k> TLOAD INDEX => GetAccountTransientStorage(INDEX) ~> #push ... </k>

    syntax BinStackOp ::= "TSTORE"
 // ------------------------------
    rule [tstore]:
         <k> TSTORE INDEX NEW => SetAccountTransientStorage(INDEX, NEW) ... </k>
      [preserves-definedness]
```

### Call Operations

The various `CALL*` (and other inter-contract control flow) operations will be desugared into these `InternalOp`s.

-   `#return` is a placeholder for the calling program, specifying where to place the returned data in memory.

```k
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
         <pc>           _ => 0      </pc>
         <memoryUsed>   _ => 0      </memoryUsed>
         <output>       _ => .Bytes </output>
         <wordStack>    _ => .List  </wordStack>
         <localMem>     _ => .Bytes </localMem>

    syntax KItem ::= "#loadProgram" Bytes [symbol(loadProgram)]
 // -----------------------------------------------------------
    rule [program.load]:
         <k> #loadProgram BYTES => .K ... </k>
         <program> _ => BYTES </program>
         <jumpDests> _ => #computeValidJumpDests(BYTES) </jumpDests>

    syntax Bytes ::= #computeValidJumpDests(Bytes)             [symbol(computeValidJumpDests),    function, memo, total]
                   | #computeValidJumpDests(Bytes, Int, Bytes) [symbol(computeValidJumpDestsAux), function             ]
 // --------------------------------------------------------------------------------------------------------------------
    rule #computeValidJumpDests(PGM) => #computeValidJumpDests(PGM, 0, padRightBytes(.Bytes, lengthBytes(PGM), 0))

    syntax Bytes ::= #computeValidJumpDestsWithinBound(Bytes, Int, Bytes) [symbol(computeValidJumpDestsWithinBound), function]
 // --------------------------------------------------------------------------------------------------------------------------
    rule #computeValidJumpDests(PGM, I, RESULT) => RESULT requires I >=Int lengthBytes(PGM)
    rule #computeValidJumpDests(PGM, I, RESULT) => #computeValidJumpDestsWithinBound(PGM, I, RESULT) requires I <Int lengthBytes(PGM)

    rule #computeValidJumpDestsWithinBound(PGM, I, RESULT) => #computeValidJumpDests(PGM, I +Int 1, RESULT[I <- 1]) requires PGM [ I ] ==Int 91
    rule #computeValidJumpDestsWithinBound(PGM, I, RESULT) => #computeValidJumpDests(PGM, I +Int #widthOpCode(PGM [ I ]), RESULT) requires notBool PGM [ I ] ==Int 91
```

```k
    syntax Int ::= #widthOpCode(Int) [symbol(#widthOpCode), function]
 // -----------------------------------------------------------------
    rule #widthOpCode(W) => W -Int 94 requires W >=Int 96 andBool W <=Int 127
    rule #widthOpCode(_) => 1 [owise]

    syntax KItem ::= "#return" Int Int MessageResult
 // ------------------------------------------------
    rule [return.revert]:
         <k> #return RETSTART RETWIDTH MessageResult(... gas: GAVAIL, status: STATUS, data: OUT) => 0 ~> #push ~> #refund GAVAIL ~> #setLocalMem RETSTART RETWIDTH OUT ...</k>
         <output> _ => OUT </output>
      requires STATUS =/=Int EVMC_SUCCESS

    rule [return.success]:
         <k> #return RETSTART RETWIDTH MessageResult(... gas: GAVAIL, status: STATUS, data: OUT) => 1 ~> #push ~> #refund GAVAIL ~> #setLocalMem RETSTART RETWIDTH OUT ...</k>
         <output> _ => OUT </output>
      requires STATUS ==Int EVMC_SUCCESS

    syntax InternalOp ::= "#refund" Gas
                        | "#setLocalMem" Int Int Bytes
 // --------------------------------------------------
    rule [refund]: <k> #refund G:Int => .K ... </k> <gas> GAVAIL => GAVAIL +Int G </gas>


    rule <k> #setLocalMem START WIDTH WS => .K ... </k>
         <localMem> LM => LM [ START := #range(WS, 0, minInt(WIDTH, lengthBytes(WS))) ] </localMem>
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
          => #return RETSTART RETWIDTH Call(GCALL, ACCTTO, VALUE, #range(LM, ARGSTART, ARGWIDTH))
         ...
         </k>
         <callGas> GCALL </callGas>
         <localMem> LM </localMem>

    syntax CallOp ::= "CALLCODE"
 // ----------------------------
    rule [callcode]:
         <k> CALLCODE _GCAP ACCTTO VALUE ARGSTART ARGWIDTH RETSTART RETWIDTH
          => #return RETSTART RETWIDTH CallCode(GCALL, ACCTTO, VALUE, #range(LM, ARGSTART, ARGWIDTH))
         ...
         </k>
         <callGas> GCALL </callGas>
         <localMem> LM </localMem>

    syntax CallSixOp ::= "DELEGATECALL"
 // -----------------------------------
    rule [delegatecall]:
         <k> DELEGATECALL _GCAP ACCTTO ARGSTART ARGWIDTH RETSTART RETWIDTH
          => #return RETSTART RETWIDTH DelegateCall(GCALL, ACCTTO, #range(LM, ARGSTART, ARGWIDTH))
         ...
         </k>
         <callGas> GCALL </callGas>
         <localMem> LM </localMem>

    syntax CallSixOp ::= "STATICCALL"
 // ---------------------------------
    rule [staticcall]:
         <k> STATICCALL _GCAP ACCTTO ARGSTART ARGWIDTH RETSTART RETWIDTH
          => #return RETSTART RETWIDTH StaticCall(GCALL, ACCTTO, #range(LM, ARGSTART, ARGWIDTH))
         ...
         </k>
         <callGas> GCALL </callGas>
         <localMem> LM </localMem>
```

### Account Creation/Deletion

-   `#create____` transfers the endowment to the new account and triggers the execution of the initialization code.
-   `#codeDeposit_` checks the result of initialization code and whether the code deposit can be paid, indicating an error if not.
-   `#isValidCode_` checks if the code returned by the execution of the initialization code begins with a reserved byte. [EIP-3541]
-   `#hasValidInitCode` checks the length of the transaction data in a create transaction. [EIP-3860]

```k
    syntax Bool ::= #hasValidInitCode ( Int , Schedule ) [symbol(#hasValidInitCode), function]
 // ------------------------------------------------------------------------------------------
    rule #hasValidInitCode(INITCODELEN, SCHED) => notBool Ghasmaxinitcodesize << SCHED >> orBool INITCODELEN <=Int maxInitCodeSize < SCHED >

    syntax KItem ::= "#codeDeposit" MessageResult
    rule <k> #codeDeposit(MessageResult(... gas: GAVAIL, status: STATUS, data:OUT)) => #refund GAVAIL ~> 0 ~> #push ...</k>
         <output> _ => OUT </output>
         <schedule> SCHED </schedule>
      requires STATUS =/=Int EVMC_SUCCESS andBool SCHED =/=K FRONTIER

       rule <k> #codeDeposit(MessageResult(... gas: GAVAIL, status: STATUS, target: ACCT)) => #refund GAVAIL ~> ACCT ~> #push ...</k>
          <output> _ => .Bytes </output>
          <schedule> FRONTIER </schedule>
      requires STATUS =/=Int EVMC_SUCCESS andBool STATUS =/=Int EVMC_REVERT

    rule <k> #codeDeposit(MessageResult(... gas: GAVAIL, status: STATUS, target: ACCT)) => #refund GAVAIL ~> ACCT ~> #push ...</k>
         <output> _ => .Bytes </output>
      requires STATUS ==Int EVMC_SUCCESS
```

`CREATE` will attempt to `#create` the account using the initialization code and cleans up the result with `#codeDeposit`.

```k
    syntax TernStackOp ::= "CREATE"
 // -------------------------------
    rule [create-valid]:
         <k> CREATE VALUE MEMSTART MEMWIDTH
          => #codeDeposit Create(VALUE, #range(LM, MEMSTART, MEMWIDTH), GCALL)
         ...
         </k>
         <callGas> GCALL </callGas>
         <localMem> LM </localMem>
         <schedule> SCHED </schedule>
      requires #hasValidInitCode(MEMWIDTH, SCHED)
      [preserves-definedness]

    rule [create-invalid]:
         <k> CREATE _ _ _ => #end EVMC_OUT_OF_GAS ... </k> [owise]
```

`CREATE2` will attempt to `#create` the account, but with the new scheme for choosing the account address.

```k
    syntax QuadStackOp ::= "CREATE2"
 // --------------------------------
    rule [create2-valid]:
         <k> CREATE2 VALUE MEMSTART MEMWIDTH SALT
          => #codeDeposit Create2(VALUE, #range(LM, MEMSTART, MEMWIDTH), Int2Bytes(32, SALT, BE), GCALL)
         ...
         </k>
         <localMem> LM </localMem>
         <callGas> GCALL </callGas>
         <schedule> SCHED </schedule>
      requires #hasValidInitCode(MEMWIDTH, SCHED)

    rule [create2-invalid]:
         <k> CREATE2 _ _ _ _ => #end EVMC_OUT_OF_GAS ... </k> [owise]
```

`SELFDESTRUCT` marks the current account for deletion and transfers funds out of the current account.
Self destructing to yourself, unlike a regular transfer, destroys the balance in the account, irreparably losing it.

```k
    syntax UnStackOp ::= "SELFDESTRUCT"
 // -----------------------------------
    rule <k> SELFDESTRUCT ACCTTO => SelfDestruct(ACCTTO) ~> #end EVMC_SUCCESS ... </k>
         <output> _ => .Bytes </output>
      requires Address() =/=Int ACCTTO

    rule <k> SELFDESTRUCT ACCT => SelfDestruct(ACCT) ~> #end EVMC_SUCCESS ... </k>
         <output> _ => .Bytes </output>
      requires ACCT ==Int Address()
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
         <output> _ => #let DATA = CallData() #in #ecrec(#range(DATA, 0, 32), #range(DATA, 32, 32), #range(DATA, 64, 32), #range(DATA, 96, 32)) </output>

    syntax Bytes ::= #ecrec ( Bytes , Bytes , Bytes , Bytes ) [symbol(#ecrec),    function, total, smtlib(ecrec)]
                   | #ecrec ( Account )                       [symbol(#ecrecAux), function, total               ]
 // -------------------------------------------------------------------------------------------------------------
    rule [ecrec]: #ecrec(HASH, SIGV, SIGR, SIGS) => #ecrec(#sender(HASH, #asWord(SIGV), SIGR, SIGS)) [concrete]

    rule #ecrec(.Account) => .Bytes
    rule #ecrec(N:Int)    => #padToWidth(32, #asByteStack(N))

    syntax PrecompiledOp ::= "SHA256"
 // ---------------------------------
    rule <k> SHA256 => #end EVMC_SUCCESS ... </k>
         <output> _ => #parseHexBytes(Sha256(CallData())) </output>

    syntax PrecompiledOp ::= "RIP160"
 // ---------------------------------
    rule <k> RIP160 => #end EVMC_SUCCESS ... </k>
         <output> _ => #padToWidth(32, #parseHexBytes(RipEmd160(CallData()))) </output>

    syntax PrecompiledOp ::= "ID"
 // -----------------------------
    rule <k> ID => #end EVMC_SUCCESS ... </k>
         <output> _ => CallData() </output>

    syntax PrecompiledOp ::= "MODEXP"
 // ---------------------------------
    rule <k> MODEXP => #end EVMC_SUCCESS ... </k>
         <output> _ => #let DATA = CallData() #in #modexp1(#asWord(#range(DATA, 0, 32)), #asWord(#range(DATA, 32, 32)), #asWord(#range(DATA, 64, 32)), #range(DATA, 96, maxInt(0, lengthBytes(DATA) -Int 96))) </output>

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
    rule <k> ECADD => #let DATA = CallData() #in #ecadd((#asWord(#range(DATA, 0, 32)), #asWord(#range(DATA, 32, 32))), (#asWord(#range(DATA, 64, 32)), #asWord(#range(DATA, 96, 32)))) ... </k>

    syntax InternalOp ::= #ecadd(G1Point, G1Point) [symbol(#ecadd)]
 // ---------------------------------------------------------------
    rule <k> #ecadd(P1, P2) => #end EVMC_PRECOMPILE_FAILURE ... </k>
      requires notBool isValidPoint(P1) orBool notBool isValidPoint(P2)
    rule <k> #ecadd(P1, P2) => #end EVMC_SUCCESS ... </k> <output> _ => #point(BN128Add(P1, P2)) </output>
      requires isValidPoint(P1) andBool isValidPoint(P2)

    syntax PrecompiledOp ::= "ECMUL"
 // --------------------------------
    rule <k> ECMUL => #let DATA = CallData() #in #ecmul((#asWord(#range(DATA, 0, 32)), #asWord(#range(DATA, 32, 32))), #asWord(#range(DATA, 64, 32))) ... </k>

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
    rule <k> ECPAIRING => #ecpairing(.List, .List, 0, CallData(), lengthBytes(CallData())) ... </k>
      requires lengthBytes(CallData()) modInt 192 ==Int 0
    rule <k> ECPAIRING => #end EVMC_PRECOMPILE_FAILURE ... </k>
      requires lengthBytes(CallData()) modInt 192 =/=Int 0

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
         <output> _ => #parseByteStack( Blake2Compress( CallData() ) ) </output>
      requires lengthBytes( CallData() ) ==Int 213
       andBool CallData()[212] <=Int 1

    rule <k> BLAKE2F => #end EVMC_PRECOMPILE_FAILURE ... </k>
      requires lengthBytes( CallData() ) ==Int 213
       andBool CallData()[212] >Int 1

    rule <k> BLAKE2F => #end EVMC_PRECOMPILE_FAILURE ... </k>
      requires lengthBytes( CallData() ) =/=Int 213

    syntax PrecompiledOp ::= "KZGPOINTEVAL"
 // ---------------------------------------
    // FIELD_ELEMENTS_PER_BLOB = 4096
    rule <k> KZGPOINTEVAL => #end EVMC_SUCCESS ... </k>
         <output> _ => Int2Bytes(32, 4096, BE) +Bytes Int2Bytes(32, blsModulus, BE) </output>
      requires lengthBytes( CallData() ) ==Int 192
       andBool #kzg2vh(substrBytes(CallData(), 96, 144)) ==K substrBytes(CallData(), 0, 32)
       andBool Bytes2Int(substrBytes(CallData(), 32, 64), BE, Unsigned) <Int blsModulus
       andBool Bytes2Int(substrBytes(CallData(), 64, 96), BE, Unsigned) <Int blsModulus
       andBool verifyKZGProof(substrBytes(CallData(), 96, 144), substrBytes(CallData(), 32, 64), substrBytes(CallData(), 64, 96), substrBytes(CallData(), 144, 192))

    rule <k> KZGPOINTEVAL => #end EVMC_PRECOMPILE_FAILURE ... </k>
      requires lengthBytes( CallData() ) =/=Int 192
       orBool #kzg2vh(substrBytes(CallData(), 96, 144)) =/=K substrBytes(CallData(), 0, 32)
       orBool Bytes2Int(substrBytes(CallData(), 32, 64), BE, Unsigned) >=Int blsModulus
       orBool Bytes2Int(substrBytes(CallData(), 64, 96), BE, Unsigned) >=Int blsModulus
       orBool notBool verifyKZGProof(substrBytes(CallData(), 96, 144), substrBytes(CallData(), 32, 64), substrBytes(CallData(), 64, 96), substrBytes(CallData(), 144, 192))

    syntax Bytes ::= #kzg2vh ( Bytes ) [symbol(#kzg2vh), function, total]
 // ---------------------------------------------------------------------
    // VERSIONED_HASH_VERSION_KZG = 0x01
    rule #kzg2vh ( C ) => Sha256raw(C)[0 <- 1]
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
          ~> #access [ OP , AOP, #isAccess(AOP) ]
         ...
        </k>

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
    rule <k>  G:Int ~> #deductGas => #end EVMC_OUT_OF_GAS ... </k> <gas> GAVAIL:Int                  </gas> requires GAVAIL <Int G
    rule <k>  G:Int ~> #deductGas => .K                    ... </k> <gas> GAVAIL:Int => GAVAIL -Int G </gas> requires G <=Int GAVAIL

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
    rule #memory ( MLOAD INDEX        , MU ) => #memoryUsageUpdate(MU, INDEX, 32)
    rule #memory ( MSTORE INDEX _     , MU ) => #memoryUsageUpdate(MU, INDEX, 32)
    rule #memory ( MSTORE8 INDEX _    , MU ) => #memoryUsageUpdate(MU, INDEX, 1)
    rule #memory ( MCOPY DST SRC WIDTH, MU ) => #memoryUsageUpdate(MU, maxInt(DST, SRC), WIDTH)

    rule #memory ( SHA3 START WIDTH   , MU ) => #memoryUsageUpdate(MU, START, WIDTH)
    rule #memory ( LOG(_) START WIDTH , MU ) => #memoryUsageUpdate(MU, START, WIDTH)

    rule #memory ( CODECOPY START _ WIDTH       , MU ) => #memoryUsageUpdate(MU, START, WIDTH)
    rule #memory ( EXTCODECOPY _ START _ WIDTH  , MU ) => #memoryUsageUpdate(MU, START, WIDTH)
    rule #memory ( CALLDATACOPY START _ WIDTH   , MU ) => #memoryUsageUpdate(MU, START, WIDTH)
    rule #memory ( RETURNDATACOPY START _ WIDTH , MU ) => #memoryUsageUpdate(MU, START, WIDTH)

    rule #memory ( CREATE  _ START WIDTH   , MU ) => #memoryUsageUpdate(MU, START, WIDTH)
    rule #memory ( CREATE2 _ START WIDTH _ , MU ) => #memoryUsageUpdate(MU, START, WIDTH)
    rule #memory ( RETURN START WIDTH      , MU ) => #memoryUsageUpdate(MU, START, WIDTH)
    rule #memory ( REVERT START WIDTH      , MU ) => #memoryUsageUpdate(MU, START, WIDTH)

    rule #memory ( _COP:CallOp     _ _ _ ARGSTART ARGWIDTH RETSTART RETWIDTH , MU ) => #memoryUsageUpdate(#memoryUsageUpdate(MU, ARGSTART, ARGWIDTH), RETSTART, RETWIDTH)
    rule #memory ( _CSOP:CallSixOp _ _   ARGSTART ARGWIDTH RETSTART RETWIDTH , MU ) => #memoryUsageUpdate(#memoryUsageUpdate(MU, ARGSTART, ARGWIDTH), RETSTART, RETWIDTH)

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

    syntax Bool ::= #isAccess ( OpCode ) [function, total]
 // ------------------------------------------------------
    rule #isAccess(EXTCODESIZE ACCT) => AccessedAccount(ACCT)
    rule #isAccess(EXTCODECOPY ACCT _ _ _) => AccessedAccount(ACCT)
    rule #isAccess(EXTCODEHASH ACCT) => AccessedAccount(ACCT)
    rule #isAccess(BALANCE ACCT) => AccessedAccount(ACCT)
    rule #isAccess(SELFDESTRUCT ACCT) => AccessedAccount(ACCT)
    rule #isAccess(SSTORE INDEX _) => AccessedStorage(INDEX)
    rule #isAccess(_) => false [owise]

    syntax InternalOp ::= #gasAccess ( Schedule, OpCode, Bool ) [symbol(#gasAccess)]
 // --------------------------------------------------------------------------
    rule <k> #gasAccess(SCHED, EXTCODESIZE ACCT, ACCESS)       => Caddraccess(SCHED, ACCESS)                                ... </k>
    rule <k> #gasAccess(SCHED, EXTCODECOPY ACCT _ _ _, ACCESS) => Caddraccess(SCHED, ACCESS)                                ... </k>
    rule <k> #gasAccess(SCHED, EXTCODEHASH ACCT, ACCESS)       => Caddraccess(SCHED, ACCESS)                                ... </k>
    rule <k> #gasAccess(SCHED, BALANCE ACCT, ACCESS)           => Caddraccess(SCHED, ACCESS)                                ... </k>
    rule <k> #gasAccess(SCHED, SELFDESTRUCT ACCT, ACCESS)      => #if ACCESS #then 0 #else Gcoldaccountaccess < SCHED > #fi ... </k>
    rule <k> #gasAccess(_    , SLOAD _, ACCESS)                => 0                                                         ... </k>
    rule <k> #gasAccess(SCHED, SSTORE INDEX _, ACCESS)         => #if ACCESS #then 0 #else Gcoldsload < SCHED > #fi         ... </k>
    rule <k> #gasAccess(_    , _, ACCESS)                      => 0                                                         ... </k> [owise]

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

    rule <k> #gasExec(SCHED, SSTORE INDEX NEW) => Csstore(SCHED, NEW, GetAccountStorage(INDEX), GetAccountOrigStorage(INDEX)) ... </k>
         <gas> GAVAIL </gas>
      requires notBool Ghassstorestipend << SCHED >>
        orBool notBool GAVAIL <=Gas Gcallstipend < SCHED >

    rule <k> #gasExec(SCHED, SSTORE _ _ ) => #end EVMC_OUT_OF_GAS ... </k>
         <gas> GAVAIL </gas>
      requires Ghassstorestipend << SCHED >>
       andBool GAVAIL <=Gas Gcallstipend < SCHED >

    rule <k> #gasExec(SCHED, EXP _ W1) => Gexp < SCHED > ... </k>                                                         requires W1 <=Int 0
    rule <k> #gasExec(SCHED, EXP _ W1) => Gexp < SCHED > +Int (Gexpbyte < SCHED > *Int (1 +Int (log256Int(W1)))) ... </k> requires 0 <Int W1 [preserves-definedness]

    rule <k> #gasExec(SCHED, CALLDATACOPY    _ _ WIDTH) => Gverylow < SCHED > +Int (Gcopy < SCHED > *Int (WIDTH up/Int 32)) ... </k>
    rule <k> #gasExec(SCHED, RETURNDATACOPY  _ _ WIDTH) => Gverylow < SCHED > +Int (Gcopy < SCHED > *Int (WIDTH up/Int 32)) ... </k>
    rule <k> #gasExec(SCHED, CODECOPY        _ _ WIDTH) => Gverylow < SCHED > +Int (Gcopy < SCHED > *Int (WIDTH up/Int 32)) ... </k>
    rule <k> #gasExec(SCHED, MCOPY           _ _ WIDTH) => Gverylow < SCHED > +Int (Gcopy < SCHED > *Int (WIDTH up/Int 32)) ... </k>

    rule <k> #gasExec(SCHED, LOG(N) _ WIDTH) => (Glog < SCHED > +Int (Glogdata < SCHED > *Int WIDTH) +Int (N *Int Glogtopic < SCHED >)) ... </k>

    rule <k> #gasExec(SCHED, CALL GCAP ACCTTO VALUE _ _ _ _)
          => Ccallgas(SCHED, #accountNonexistent(ACCTTO), GCAP, GAVAIL, VALUE, AccessedAccount(ACCTTO)) ~> #allocateCallGas
          ~> Ccall(SCHED, #accountNonexistent(ACCTTO), GCAP, GAVAIL, VALUE, AccessedAccount(ACCTTO))
         ...
         </k>
         <gas> GAVAIL </gas>

    rule <k> #gasExec(SCHED, CALLCODE GCAP ACCTTO VALUE _ _ _ _)
          => Ccallgas(SCHED, #accountNonexistent(Address()), GCAP, GAVAIL, VALUE, AccessedAccount(ACCTTO)) ~> #allocateCallGas
          ~> Ccall(SCHED, #accountNonexistent(Address()), GCAP, GAVAIL, VALUE, AccessedAccount(ACCTTO))
         ...
         </k>
         <gas> GAVAIL </gas>

    rule <k> #gasExec(SCHED, DELEGATECALL GCAP ACCTTO _ _ _ _)
          => Ccallgas(SCHED, #accountNonexistent(Address()), GCAP, GAVAIL, 0, AccessedAccount(ACCTTO)) ~> #allocateCallGas
          ~> Ccall(SCHED, #accountNonexistent(Address()), GCAP, GAVAIL, 0, AccessedAccount(ACCTTO))
         ...
         </k>
         <gas> GAVAIL </gas>

    rule <k> #gasExec(SCHED, STATICCALL GCAP ACCTTO _ _ _ _)
          => Ccallgas(SCHED, #accountNonexistent(ACCTTO), GCAP, GAVAIL, 0, AccessedAccount(ACCTTO)) ~> #allocateCallGas
          ~> Ccall(SCHED, #accountNonexistent(ACCTTO), GCAP, GAVAIL, 0, AccessedAccount(ACCTTO))
         ...
         </k>
         <gas> GAVAIL </gas>

    rule <k> #gasExec(SCHED, SELFDESTRUCT ACCTTO) => Cselfdestruct(SCHED, #accountNonexistent(ACCTTO), GetAccountBalance(Address())) ... </k>

    rule <k> #gasExec(SCHED, CREATE _ _ WIDTH)
          => Gcreate < SCHED > +Int Cinitcode(SCHED, WIDTH) ~> #deductGas
          ~> #allocateCreateGas ~> 0
         ...
         </k>

    rule <k> #gasExec(SCHED, CREATE2 _ _ WIDTH _)
          => Gcreate < SCHED > +Int Gsha3word < SCHED > *Int (WIDTH up/Int 32) +Int Cinitcode(SCHED, WIDTH) ~> #deductGas
          ~> #allocateCreateGas ~> 0
         ...
         </k>

    rule <k> #gasExec(SCHED, SHA3 _ WIDTH) => Gsha3 < SCHED > +Int (Gsha3word < SCHED > *Int (WIDTH up/Int 32)) ... </k>

    rule <k> #gasExec(SCHED, JUMPDEST)    => Gjumpdest < SCHED >                        ... </k>
    rule <k> #gasExec(SCHED, SLOAD INDEX) => Csload(SCHED, AccessedStorage(INDEX)) ... </k>

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

    rule <k> #gasExec(SCHED, EXTCODECOPY _ _ _ WIDTH) => Cextcodecopy(SCHED, WIDTH) ... </k>
    rule <k> #gasExec(SCHED, EXTCODESIZE _)           => Cextcodesize(SCHED)        ... </k>
    rule <k> #gasExec(SCHED, BALANCE _)               => Cbalance(SCHED)            ... </k>
    rule <k> #gasExec(SCHED, EXTCODEHASH _)           => Cextcodehash(SCHED)        ... </k>
    rule <k> #gasExec(SCHED, BLOCKHASH _)             => Gblockhash < SCHED >       ... </k>

    // Precompiled
    rule <k> #gasExec(_, ECREC)  => 3000 ... </k>
    rule <k> #gasExec(_, SHA256) =>  60 +Int  12 *Int (lengthBytes(CallData()) up/Int 32) ... </k>
    rule <k> #gasExec(_, RIP160) => 600 +Int 120 *Int (lengthBytes(CallData()) up/Int 32) ... </k>
    rule <k> #gasExec(_, ID)     =>  15 +Int   3 *Int (lengthBytes(CallData()) up/Int 32) ... </k>

    rule <k> #gasExec(SCHED, MODEXP) => #let DATA = CallData() #in Cmodexp(SCHED, DATA, #asWord(#range(DATA, 0, 32) ), #asWord(#range(DATA, 32, 32)), #asWord(#range(DATA, 64, 32))) ... </k>

    rule <k> #gasExec(SCHED, ECADD)     => Gecadd < SCHED>  ... </k>
    rule <k> #gasExec(SCHED, ECMUL)     => Gecmul < SCHED > ... </k>
    rule <k> #gasExec(SCHED, ECPAIRING) => Gecpairconst < SCHED > +Int (lengthBytes(CallData()) /Int 192) *Int Gecpaircoeff < SCHED > ... </k>
    rule <k> #gasExec(SCHED, BLAKE2F)   => Gfround < SCHED > *Int #asWord(#range(CallData(), 0, 4) ) ... </k>
    rule <k> #gasExec(SCHED, KZGPOINTEVAL)  => Gpointeval < SCHED > ... </k>

    syntax InternalOp ::= "#allocateCallGas"
 // ----------------------------------------
    rule <k> GCALL:Gas ~> #allocateCallGas => .K ... </k>
         <callGas> _ => GCALL </callGas>

    syntax InternalOp ::= "#allocateCreateGas"
 // ------------------------------------------
    rule <schedule> SCHED </schedule>
         <k> #allocateCreateGas => .K ... </k>
         <gas>     GAVAIL => #if Gstaticcalldepth << SCHED >> #then 0      #else GAVAIL /Int 64      #fi </gas>
         <callGas> _      => #if Gstaticcalldepth << SCHED >> #then GAVAIL #else #allBut64th(GAVAIL) #fi </callGas>
      [preserves-definedness]
```

There are several helpers for calculating gas (most of them also specified in the YellowPaper).

```k
    syntax Exp     ::= Int | Gas
    syntax KResult ::= Int
    syntax Exp ::= Ccall         ( Schedule , BExp , Gas , Gas , Int , Bool ) [symbol(Ccall), strict(2)]
                 | Ccallgas      ( Schedule , BExp , Gas , Gas , Int , Bool ) [symbol(Ccallgas), strict(2)]
                 | Cselfdestruct ( Schedule , BExp , Int )                    [symbol(Cselfdestruct), strict(2)]
 // ------------------------------------------------------------------------------------------------------------
    rule <k> Ccall(SCHED, ISEMPTY:Bool, GCAP, GAVAIL, VALUE, ISWARM)
          => Cextra(SCHED, ISEMPTY, VALUE, ISWARM) +Gas Cgascap(SCHED, GCAP, GAVAIL, Cextra(SCHED, ISEMPTY, VALUE, ISWARM)) ... </k>

    rule <k> Ccallgas(SCHED, ISEMPTY:Bool, GCAP, GAVAIL, VALUE, ISWARM)
          => Cgascap(SCHED, GCAP, GAVAIL, Cextra(SCHED, ISEMPTY, VALUE, ISWARM)) +Gas #if VALUE ==Int 0 #then 0 #else Gcallstipend < SCHED > #fi ... </k>

    rule <k> Cselfdestruct(SCHED, ISEMPTY:Bool, BAL)
          => Gselfdestruct < SCHED > +Int Cnew(SCHED, ISEMPTY andBool Gselfdestructnewaccount << SCHED >>, BAL) ... </k>

    syntax BExp    ::= Bool
    syntax KResult ::= Bool
    syntax BExp ::= #accountNonexistent ( Int ) [symbol(#accountNonexistent)]
 // -------------------------------------------------------------------------
    rule <k> #accountNonexistent(ACCT) => IsAccountEmpty(ACCT) andBool Gemptyisnonexistent << SCHED >> ... </k>
         <schedule> SCHED </schedule>
      requires AccountExists(ACCT)

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
    syntax OpCode ::= #dasmOpCode ( Int , Schedule ) [symbol(#dasmOpCode), function, memo, total]
 // ---------------------------------------------------------------------------------------------
    rule #dasmOpCode(   0,     _ ) => STOP
    rule #dasmOpCode(   1,     _ ) => ADD
    rule #dasmOpCode(   2,     _ ) => MUL
    rule #dasmOpCode(   3,     _ ) => SUB
    rule #dasmOpCode(   4,     _ ) => DIV
    rule #dasmOpCode(   5,     _ ) => SDIV
    rule #dasmOpCode(   6,     _ ) => MOD
    rule #dasmOpCode(   7,     _ ) => SMOD
    rule #dasmOpCode(   8,     _ ) => ADDMOD
    rule #dasmOpCode(   9,     _ ) => MULMOD
    rule #dasmOpCode(  10,     _ ) => EXP
    rule #dasmOpCode(  11,     _ ) => SIGNEXTEND
    rule #dasmOpCode(  16,     _ ) => LT
    rule #dasmOpCode(  17,     _ ) => GT
    rule #dasmOpCode(  18,     _ ) => SLT
    rule #dasmOpCode(  19,     _ ) => SGT
    rule #dasmOpCode(  20,     _ ) => EQ
    rule #dasmOpCode(  21,     _ ) => ISZERO
    rule #dasmOpCode(  22,     _ ) => AND
    rule #dasmOpCode(  23,     _ ) => EVMOR
    rule #dasmOpCode(  24,     _ ) => XOR
    rule #dasmOpCode(  25,     _ ) => NOT
    rule #dasmOpCode(  26,     _ ) => BYTE
    rule #dasmOpCode(  27, SCHED ) => SHL requires Ghasshift << SCHED >>
    rule #dasmOpCode(  28, SCHED ) => SHR requires Ghasshift << SCHED >>
    rule #dasmOpCode(  29, SCHED ) => SAR requires Ghasshift << SCHED >>
    rule #dasmOpCode(  32,     _ ) => SHA3
    rule #dasmOpCode(  48,     _ ) => ADDRESS
    rule #dasmOpCode(  49,     _ ) => BALANCE
    rule #dasmOpCode(  50,     _ ) => ORIGIN
    rule #dasmOpCode(  51,     _ ) => CALLER
    rule #dasmOpCode(  52,     _ ) => CALLVALUE
    rule #dasmOpCode(  53,     _ ) => CALLDATALOAD
    rule #dasmOpCode(  54,     _ ) => CALLDATASIZE
    rule #dasmOpCode(  55,     _ ) => CALLDATACOPY
    rule #dasmOpCode(  56,     _ ) => CODESIZE
    rule #dasmOpCode(  57,     _ ) => CODECOPY
    rule #dasmOpCode(  58,     _ ) => GASPRICE
    rule #dasmOpCode(  59,     _ ) => EXTCODESIZE
    rule #dasmOpCode(  60,     _ ) => EXTCODECOPY
    rule #dasmOpCode(  61, SCHED ) => RETURNDATASIZE requires Ghasreturndata  << SCHED >>
    rule #dasmOpCode(  62, SCHED ) => RETURNDATACOPY requires Ghasreturndata  << SCHED >>
    rule #dasmOpCode(  63, SCHED ) => EXTCODEHASH    requires Ghasextcodehash << SCHED >>
    rule #dasmOpCode(  64,     _ ) => BLOCKHASH
    rule #dasmOpCode(  65,     _ ) => COINBASE
    rule #dasmOpCode(  66,     _ ) => TIMESTAMP
    rule #dasmOpCode(  67,     _ ) => NUMBER
    rule #dasmOpCode(  68, SCHED ) => PREVRANDAO  requires         Ghasprevrandao << SCHED >>
    rule #dasmOpCode(  68, SCHED ) => DIFFICULTY  requires notBool Ghasprevrandao << SCHED >>
    rule #dasmOpCode(  69,     _ ) => GASLIMIT
    rule #dasmOpCode(  70, SCHED ) => CHAINID     requires Ghaschainid     << SCHED >>
    rule #dasmOpCode(  71, SCHED ) => SELFBALANCE requires Ghasselfbalance << SCHED >>
    rule #dasmOpCode(  72, SCHED ) => BASEFEE     requires Ghasbasefee     << SCHED >>
    rule #dasmOpCode(  73, SCHED ) => BLOBHASH    requires Ghasblobhash    << SCHED >>
    rule #dasmOpCode(  74, SCHED ) => BLOBBASEFEE requires Ghasblobbasefee << SCHED >>
    rule #dasmOpCode(  80,     _ ) => POP
    rule #dasmOpCode(  81,     _ ) => MLOAD
    rule #dasmOpCode(  82,     _ ) => MSTORE
    rule #dasmOpCode(  83,     _ ) => MSTORE8
    rule #dasmOpCode(  84,     _ ) => SLOAD
    rule #dasmOpCode(  85,     _ ) => SSTORE
    rule #dasmOpCode(  86,     _ ) => JUMP
    rule #dasmOpCode(  87,     _ ) => JUMPI
    rule #dasmOpCode(  88,     _ ) => PC
    rule #dasmOpCode(  89,     _ ) => MSIZE
    rule #dasmOpCode(  90,     _ ) => GAS
    rule #dasmOpCode(  91,     _ ) => JUMPDEST
    rule #dasmOpCode(  92, SCHED ) => TLOAD    requires Ghastransient << SCHED >>
    rule #dasmOpCode(  93, SCHED ) => TSTORE   requires Ghastransient << SCHED >>
    rule #dasmOpCode(  94, SCHED ) => MCOPY    requires Ghasmcopy     << SCHED >>
    rule #dasmOpCode(  95, SCHED ) => PUSHZERO requires Ghaspushzero  << SCHED >>
    rule #dasmOpCode(  96,     _ ) => PUSH(1)
    rule #dasmOpCode(  97,     _ ) => PUSH(2)
    rule #dasmOpCode(  98,     _ ) => PUSH(3)
    rule #dasmOpCode(  99,     _ ) => PUSH(4)
    rule #dasmOpCode( 100,     _ ) => PUSH(5)
    rule #dasmOpCode( 101,     _ ) => PUSH(6)
    rule #dasmOpCode( 102,     _ ) => PUSH(7)
    rule #dasmOpCode( 103,     _ ) => PUSH(8)
    rule #dasmOpCode( 104,     _ ) => PUSH(9)
    rule #dasmOpCode( 105,     _ ) => PUSH(10)
    rule #dasmOpCode( 106,     _ ) => PUSH(11)
    rule #dasmOpCode( 107,     _ ) => PUSH(12)
    rule #dasmOpCode( 108,     _ ) => PUSH(13)
    rule #dasmOpCode( 109,     _ ) => PUSH(14)
    rule #dasmOpCode( 110,     _ ) => PUSH(15)
    rule #dasmOpCode( 111,     _ ) => PUSH(16)
    rule #dasmOpCode( 112,     _ ) => PUSH(17)
    rule #dasmOpCode( 113,     _ ) => PUSH(18)
    rule #dasmOpCode( 114,     _ ) => PUSH(19)
    rule #dasmOpCode( 115,     _ ) => PUSH(20)
    rule #dasmOpCode( 116,     _ ) => PUSH(21)
    rule #dasmOpCode( 117,     _ ) => PUSH(22)
    rule #dasmOpCode( 118,     _ ) => PUSH(23)
    rule #dasmOpCode( 119,     _ ) => PUSH(24)
    rule #dasmOpCode( 120,     _ ) => PUSH(25)
    rule #dasmOpCode( 121,     _ ) => PUSH(26)
    rule #dasmOpCode( 122,     _ ) => PUSH(27)
    rule #dasmOpCode( 123,     _ ) => PUSH(28)
    rule #dasmOpCode( 124,     _ ) => PUSH(29)
    rule #dasmOpCode( 125,     _ ) => PUSH(30)
    rule #dasmOpCode( 126,     _ ) => PUSH(31)
    rule #dasmOpCode( 127,     _ ) => PUSH(32)
    rule #dasmOpCode( 128,     _ ) => DUP(1)
    rule #dasmOpCode( 129,     _ ) => DUP(2)
    rule #dasmOpCode( 130,     _ ) => DUP(3)
    rule #dasmOpCode( 131,     _ ) => DUP(4)
    rule #dasmOpCode( 132,     _ ) => DUP(5)
    rule #dasmOpCode( 133,     _ ) => DUP(6)
    rule #dasmOpCode( 134,     _ ) => DUP(7)
    rule #dasmOpCode( 135,     _ ) => DUP(8)
    rule #dasmOpCode( 136,     _ ) => DUP(9)
    rule #dasmOpCode( 137,     _ ) => DUP(10)
    rule #dasmOpCode( 138,     _ ) => DUP(11)
    rule #dasmOpCode( 139,     _ ) => DUP(12)
    rule #dasmOpCode( 140,     _ ) => DUP(13)
    rule #dasmOpCode( 141,     _ ) => DUP(14)
    rule #dasmOpCode( 142,     _ ) => DUP(15)
    rule #dasmOpCode( 143,     _ ) => DUP(16)
    rule #dasmOpCode( 144,     _ ) => SWAP(1)
    rule #dasmOpCode( 145,     _ ) => SWAP(2)
    rule #dasmOpCode( 146,     _ ) => SWAP(3)
    rule #dasmOpCode( 147,     _ ) => SWAP(4)
    rule #dasmOpCode( 148,     _ ) => SWAP(5)
    rule #dasmOpCode( 149,     _ ) => SWAP(6)
    rule #dasmOpCode( 150,     _ ) => SWAP(7)
    rule #dasmOpCode( 151,     _ ) => SWAP(8)
    rule #dasmOpCode( 152,     _ ) => SWAP(9)
    rule #dasmOpCode( 153,     _ ) => SWAP(10)
    rule #dasmOpCode( 154,     _ ) => SWAP(11)
    rule #dasmOpCode( 155,     _ ) => SWAP(12)
    rule #dasmOpCode( 156,     _ ) => SWAP(13)
    rule #dasmOpCode( 157,     _ ) => SWAP(14)
    rule #dasmOpCode( 158,     _ ) => SWAP(15)
    rule #dasmOpCode( 159,     _ ) => SWAP(16)
    rule #dasmOpCode( 160,     _ ) => LOG(0)
    rule #dasmOpCode( 161,     _ ) => LOG(1)
    rule #dasmOpCode( 162,     _ ) => LOG(2)
    rule #dasmOpCode( 163,     _ ) => LOG(3)
    rule #dasmOpCode( 164,     _ ) => LOG(4)
    rule #dasmOpCode( 240,     _ ) => CREATE
    rule #dasmOpCode( 241,     _ ) => CALL
    rule #dasmOpCode( 242,     _ ) => CALLCODE
    rule #dasmOpCode( 243,     _ ) => RETURN
    rule #dasmOpCode( 244, SCHED ) => DELEGATECALL requires SCHED =/=K FRONTIER
    rule #dasmOpCode( 245, SCHED ) => CREATE2      requires Ghascreate2    << SCHED >>
    rule #dasmOpCode( 250, SCHED ) => STATICCALL   requires Ghasstaticcall << SCHED >>
    rule #dasmOpCode( 253, SCHED ) => REVERT       requires Ghasrevert     << SCHED >>
    rule #dasmOpCode( 254,     _ ) => INVALID
    rule #dasmOpCode( 255,     _ ) => SELFDESTRUCT
    rule #dasmOpCode(   W,     _ ) => UNDEFINED(W) [owise]
endmodule
```
