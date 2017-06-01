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

```k
requires "data.k"

module EVM
    imports EVM-DATA

    configuration <evm>
                    <id> 0:Word </id>
                    <op> . </op>
                    <pc> 0:Word </pc>
                    <gas> 0:Word </gas>
                    <gasPrice> 0:Word </gasPrice>
                    <currentProgram> .Map </currentProgram>
                    <wordStack> .WordStack </wordStack>
                    <localMem> .Map </localMem>

                    <callStack> .CallStack </callStack>
                    <substate> .Map </substate>
                  </evm>
```

When the `op` cell becomes empty, it's time to load the next opcode. The gas
needed is calculated here.

```k
    rule <op> . => OP </op>
         <pc> PCOUNT => PCOUNT +Word 1 </pc>
         <gas> G => G -Word #gas(OP) </gas>
         <currentProgram> ... PCOUNT |-> OP ... </currentProgram>
      requires (G >=Word #gas(OP)) ==K bool2Word(true)
```

Depending on the sort of the opcode loaded, the correct number of arguments are
loaded off the `wordStack` (or the entire stack).

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

    syntax KItem :;= CallOp Word Word Word Word Word Word Word
                   | "DELEGATECALL" Word Word Word Word Word Word
 // -------------------------------------------------------------
    rule <op> DELEGATECALL => DELEGATECALL W0 W1 W2 W3 W4 W5    ... </op> <wordStack> W0 : W1 : W2 : W3 : W4 : W5 : WS      => WS </wordStack>
    rule <op> CO:CallOp    => CO           W0 W1 W2 W3 W4 W5 W6 ... </op> <wordStack> W0 : W1 : W2 : W3 : W4 : W5 : W6 : WS => WS </wordStack>
      requires CO =/=K DELEGATECALL

    syntax KItem ::= StackOp WordStack
 // ----------------------------------
    rule <op> SO:StackOp => SO WS ... </op> <wordStack> WS </wordStack>
```

The internal operators are provided here. These are just used by the other
operators for shuffling local execution state around on the EVM.

```k
    syntax InternalOp ::= "#push" | "#setStack" WordStack
 // -----------------------------------------------------
    rule <op> W0:Word ~> #push => . ... </op> <wordStack> WS => W0 : WS </wordStack>
    rule <op> #setStack WS     => . ... </op> <wordStack> _  => WS      </wordStack>

    syntax InternalOp ::= "#checkStackSize" | "#stackOverflow"
 // ----------------------------------------------------------
    rule <op> #checkStackSize => #stackSize(WS) ~> #checkStackSize ... </op> <wordStack> WS </wordStack>
    rule (I:Int ~> #checkStackSize) => .              requires I <Int  1024
    rule (I:Int ~> #checkStackSize) => #stackOverflow requires I >=Int 1024

    syntax Process ::= "{" AcctID "|" Word "|" Word "|" Word "|" WordStack "|" Map "}"
    syntax CallStack ::= ".CallStack" | Process CallStack

    syntax InternalOp ::= "#pushCallStack" | "#popCallStack"
 // --------------------------------------------------------
    rule <op> #pushCallStack => . </op>
         <callStack> CS => { ACCT | PCOUNT | GAVAIL | GPRICE | WS | LM } CS </callStack>
         <id>        ACCT   </id>
         <pc>        PCOUNT </pc>
         <gas>       GAVAIL </gas>
         <gasPrice>  GPRICE </gasPrice>
         <wordStack> WS     </wordStack>
         <localMem>  LM     </localMem>

    rule <op> #popCallStack => . </op>
         <callStack> { ACCT | PCOUNT | GAVAIL | GPRICE | WS | LM } CS => CS </callStack>
         <id>        _ => ACCT   </id>
         <pc>        _ => PCOUNT </pc>
         <gas>       _ => GAVAIL </gas>
         <gasPrice>  _ => GPRICE </gasPrice>
         <wordStack> _ => WS     </wordStack>
         <localMem>  _ => LM     </localMem>
```

EVM Opcodes
===========

Each subsection has a different class of opcode. Organization is based roughly
on what parts of the execution state are needed to compute the result of each
operator. This sometimes corresponds to the organization in the yellowpaper.

Implementations immediately follow declarations, so if an operator is declared
here but not implemented then it isn't implemented at all.

### Expressions

Expression calculations are simple and don't require anything but the arguments
from the `wordStack` to operate. The arguments are loaded automatically based on
subsort, so we can provide the definition of them locally here.

NOTE: We have to call the opcode `OR` by `EVMOR` instead, because K has trouble
parsing it/compiling the definition otherwise.

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

    syntax BinStackOp ::= "SLT" | "SGT" | "SDIV" | "SMOD" | "SIGNEXTEND" | "BYTE" | "SHA3"
 // --------------------------------------------------------------------------------------

    syntax TernStackOp ::= "ADDMOD" | "MULMOD"
 // ------------------------------------------
    rule <op> ADDMOD W0 W1 W2 => (W0 +Word W1) %Word W2 ~> #push ... </op>
    rule <op> MULMOD W0 W1 W2 => (W0 *Word W1) %Word W2 ~> #push ... </op>
```

### Stack Manipulations

Some operators don't calculate anything, they just push the stack around a bit.

```k
    syntax UnStackOp ::= "POP"
 // --------------------------
    rule <op> POP W => . ... </op>

    syntax StackOp ::= DUP ( Word ) | SWAP ( Word )
 // -----------------------------------------------
    rule <op> DUP(N)  WS:WordStack => #setStack ((WS [ N -Word 1 ]) : WS) ~> #checkStackSize    ... </op>
    rule <op> SWAP(N) (W0 : WS)    => #setStack ((WS [ N -Word 1 ]) : (WS [ N -Word 1 := W0 ])) ... </op>

    syntax PushOp ::= PUSH ( Word )
 // -------------------------------
    rule <op> PUSH(W) => W ~> #push ~> #checkStackSize ... </op>
```

### Control Flow

```k
    syntax NullStackOp ::= "INVALID" | "STOP" | "RETURN"
    syntax UnStackOp   ::= "SELFDESTRUCT"
 // -------------------------------------
```

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

### Local State

These operations are getters/setters of the local execution memory.

```k
    syntax UnStackOp  ::= "MLOAD"
    syntax BinStackOp ::= "MSTORE" | "MSTORE8"
 // ------------------------------------------
    rule <op> MLOAD INDEX        => VALUE ~> #push ... </op> <localMem> ... INDEX |-> VALUE ...  </localMem>
    rule <op> MSTORE INDEX VALUE => .              ... </op> <localMem> LM => LM [ INDEX <- VALUE ] </localMem>
```

These operators make queries about the current execution state (whether directly
about this state or past substates on the callstack).

```k
    syntax NullStackOp ::= "PC" | "MSIZE" | "CODESIZE" | "GAS" | "GASPRICE"
 // -----------------------------------------------------------------------
    rule <op> PC       => (PC -Int 1)      ~> #push ... </op> <pc> PCOUNT </pc>
    rule <op> MSIZE    => 32 *Int size(LM) ~> #push ... </op> <localMem> LM </localMem>
    rule <op> CODESIZE => size(PGM)        ~> #push ... </op> <program> PGM </program>
    rule <op> GAS      => GAVAIL           ~> #push ... </op> <gas> GAVAIL </gas>
    rule <op> GASPRICE => GPRICE           ~> #push ... </op> <gasPrice> GPRICE </gasPrice>

    syntax NullStackOp ::= "ADDRESS" | "ORIGIN" | "CALLER"
 // ------------------------------------------------------
    rule <op> ADDRESS => ACCTID     ~> #push ... </op> <id> ACCTID </id>
    rule <op> ORIGIN  => #origin CS ~> #push ... </op> <callStack> CS </callStack>
    rule <op> CALLER  => ACCT       ~> #push ... </op> <callStack> { ACCT | _ | _ | _ | _ | _ } CS </callStack>
    rule <op> CALLER  => ACCT       ~> #push ... </op> <id> ACCT </id> <callStack> .CallStack </callStack>

    syntax NullStackOp ::= "CALLVALUE" | "CALLDATASIZE" | "CALLDATALOAD"
 // --------------------------------------------------------------------

    syntax KItem ::= "#origin" CallStack
 // ------------------------------------
    rule <op> #origin ({ ACCT | _ | _ | _ | _ | _ } .CallStack) => ACCTID ~> #push ... </op>
    rule <op> #origin (P1:Process P2:Process CS:CallStack)      => #origin (P2 CS) ... </op>
```

### Global State

These operators make queries about the current block.

```k
    syntax NullStackOp ::= "COINBASE" | "TIMESTAMP" | "NUMBER" | "DIFFICULTY" | "GASLIMIT"
    syntax UnStackOp   ::= "BLOCKHASH" | "CALLDATALOAD" | "EXTCODESIZE" | "BALANCE"
 // -------------------------------------------------------------------------------
```

These operators affect the storage of the current account.

```k
    syntax UnStackOp  ::= "SLOAD"
    syntax BinStackOp ::= "SSTORE"
```

```k
    syntax TernStackOp ::= "CALLDATACOPY" | "CODECOPY" | "CREATE"
 // -------------------------------------------------------------

    syntax QuadStackOp ::= "EXTCODECOPY"
 // ------------------------------------
```

```k
    syntax CallOp ::= "CALL" | "CALLCODE" | "DELEGATECALL"
    syntax LogOp  ::= LOG ( Word )
 // --------------------------------------------
```

EVM Programs
------------

Lists of opcodes form programs. Deciding if an opcode is in a list will be
useful for modelling gas, and converting a program into a map of program-counter
to opcode is useful for execution.

```k
    syntax OpCodes ::= ".OpCodes"
                     | OpCode ";" OpCodes
 // -------------------------------------

    syntax Bool ::= OpCode "in" OpCodes
 // -----------------------------------
    rule OP in .OpCodes    => false
    rule OP in (OP ; OPS)  => true
    rule OP in (OP' ; OPS) => OP in OPS requires OP =/=K OP'

    syntax Map ::= #asMap ( OpCodes )       [function]
                 | #asMap ( Int , OpCodes ) [function]
 // --------------------------------------------------
    rule #asMap( OPS:OpCodes )         => #asMap(0, OPS)
    rule #asMap( N , .OpCodes )        => .Map
    rule #asMap( N , OP:OpCode ; OCS ) => (N |-> OP) #asMap(N +Int 1, OCS)
```

EVM Gas Cost
------------

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
    rule Gzero          => 0     [macro]
    rule Gbase          => 2     [macro]
    rule Gverylow       => 3     [macro]
    rule Glow           => 5     [macro]
    rule Gmid           => 8     [macro]
    rule Ghigh          => 10    [macro]
    rule Gextcode       => 700   [macro]
    rule Gbalance       => 400   [macro]
    rule Gsload         => 200   [macro]
    rule Gjumpdest      => 1     [macro]
    rule Gsset          => 20000 [macro]
    rule Gsreset        => 5000  [macro]
    rule Rsclear        => 15000 [macro]
    rule Rself-destruct => 24000 [macro]
    rule Gself-destruct => 5000  [macro]
    rule Gcreate        => 32000 [macro]
    rule Gcodedeposit   => 200   [macro]
    rule Gcall          => 700   [macro]
    rule Gcallvalue     => 9000  [macro]
    rule Gcallstipend   => 2300  [macro]
    rule Gnewaccount    => 25000 [macro]
    rule Gexp           => 10    [macro]
    rule Gexpbyte       => 10    [macro]
    rule Gmemory        => 3     [macro]
    rule Gtxcreate      => 32000 [macro]
    rule Gtxdatazero    => 4     [macro]
    rule Gtxdatanonzero => 68    [macro]
    rule Gtransaction   => 21000 [macro]
    rule Glog           => 375   [macro]
    rule Glogdata       => 8     [macro]
    rule Glogtopic      => 375   [macro]
    rule Gsha3          => 30    [macro]
    rule Gsha3word      => 6     [macro]
    rule Gcopy          => 3     [macro]
    rule Gblockhash     => 20    [macro]

    syntax OpCodes ::= "Wzero" | "Wbase" | "Wverylow" | "Wlow" | "Wmid" | "Whigh" | "Wextcode" | "Wcopy" | "Wcall"
 // --------------------------------------------------------------------------------------------------------------
    rule Wzero => STOP ; RETURN ; .OpCodes
    rule Wbase =>   ADDRESS ; ORIGIN ; CALLER ; CALLVALUE ; CALLDATASIZE
                  ; CODESIZE ; GASPRICE ; COINBASE ; TIMESTAMP ; NUMBER
                  ; DIFFICULTY ; GASLIMIT ; POP ; PC ; MSIZE ; GAS ; .OpCodes
    rule Wverylow =>   ADD ; SUB ; NOT ; LT ; GT ; SLT ; SGT ; EQ ; ISZERO ; AND ; EVMOR
                     ; XOR ; BYTE ; CALLDATALOAD ; MLOAD ; MSTORE ; MSTORE8 ; .OpCodes
    rule Wlow => MUL ; DIV ; SDIV ; MOD ; SMOD ; SIGNEXTEND ; .OpCodes
    rule Wmid => ADDMOD ; MULMOD ; JUMP ; JUMPI; .OpCodes
    rule Wextcode => EXTCODESIZE ; .OpCodes
    rule Wcopy => CALLDATACOPY ; CODECOPY ; .OpCodes
    rule Wcall => CALL ; CALLCODE ; DELEGATECALL ; .OpCodes
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
    rule #gas(PO:PushOp)    => Gverylow
    rule #gas(SO:StackOp)   => Gverylow
    rule #gas(OP)           => Glow                          requires OP in Wlow
    rule #gas(OP)           => Gmid                          requires OP in Wmid
    rule #gas(OP)           => Ghigh                         requires OP in Whigh
    rule #gas(OP)           => Gextcode                      requires OP in Wextcode
    rule #gas(BALANCE)      => Gbalance
    rule #gas(BLOCKHASH)    => Gblockhash
endmodule
```
