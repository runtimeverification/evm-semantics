---
title: K Model of EVM Execution Environment
geometry: margin=2.5cm
...


```k
requires "evm-data.k"
```

None of the rules defined here should be sensitive to other parts of the
configuration, they should be standalone.


Local Execution State
=====================

EVM execution maintains some local state (like a word stack, local memory,
program counter, etc...). We need to specify the syntax of all this local state
for storage.

Word Stack
----------

The `WordStack` is the size-limited (to 1024) stack of words that each local
execution of an EVM process has acess to.

```k
module EVM-STACK-SYNTAX
    imports EVM-WORD

    syntax WordStack ::= ".WordStack"       // empty stack
                       | Word ":" WordStack

    // Compute the size of the word-stack (for checking validity)
    syntax Word ::= "stackSize" "(" WordStack ")"
    syntax Int  ::= "MAX_STACK_SIZE"

    rule MAX_STACK_SIZE => 1024 [macro]

    rule stackSize( .WordStack ) => 0                     [structural]
    rule stackSize( W : WS )     => 1 +Word stackSize(WS) [structural]
```

We break up stack operations into groups by their arity so that we can pull out
the correct number of arguments for each operation.

```k
    syntax UnStackOp ::= "ISZERO" | "NOT" | "POP"
    syntax Word ::= UnStackOp Word

    syntax BinStackOp ::= "ADD" | "MUL" | "SUB" | "EXP" | "DIV"
                        | "MOD" | "SIGNEXTEND" | "SDIV" | "SMOD"
                        | "LT" | "GT" | "SLT" | "SGT" | "EQ"
                        | "AND" | "OR" | "XOR"
                        | "BYTE" | "SHA3"
    syntax Word ::= BinStackOp Word Word

    syntax TernStackOp ::= "ADDMOD" | "MULMOD"
    syntax Word ::= TernStackOp Word Word Word

    syntax StackOp ::= UnStackOp | BinStackOp | TernStackOp
endmodule
```

We assume that the operations will be placed at the top of the k-cell with the
correct number of arguments supplied. Here we define the relevant operations.

```k
module EVM-STACK-SEMANTICS
    imports EVM-STACK-SYNTAX

    rule ADD W0 W1 => W0 +Word W1 [structural]
    rule MUL W0 W1 => W0 *Word W1 [structural]
    rule SUB W0 W1 => W0 -Word W1 [structural]
    rule MUL W0 W1 => W0 *Word W1 [structural]
    rule DIV W0 W1 => W0 /Word W1 [structural]
    rule EXP W0 W1 => W0 ^Word W1 [structural]
    rule LT  W0 W1 => W0 <Word W1 [structural]
    rule GT  W0 W1 => W0 >Word W1 [structural]
    rule EQ  W0 W1 => W0 ==Word W1 [structural]
    // TODO: define rest of operations
endmodule
```

EVM Programs
------------

```k
module EVM-PROGRAM-SYNTAX
    imports EVM-STACK-SYNTAX

    syntax LocalOp ::= StackOp | "MLOAD" | "MSTORE"
                     // | "MLOAD8"

    syntax ProcessOp ::= "CALL"
                       | "RETURN" | "ACCEPTRETURN" Word Word Word
    syntax Word ::= "CALL" Word Word Word Word Word Word Word

    syntax ExnOp ::= "STACK_OVERFLOW" Int

    syntax OpCode ::= LocalOp
                    | ExnOp
                    | ProcessOp
                    | "#push"           // internal stack push operation
                    | "#checkStackSize" // internal stack-size check
                    | "PUSH" Word

    syntax Program ::= ".Program"
                     | OpCode ";" Program

    rule (I:Int ~> #checkStackSize) => .                requires I <Int  MAX_STACK_SIZE
    rule (I:Int ~> #checkStackSize) => STACK_OVERFLOW I requires I >=Int MAX_STACK_SIZE

    // turn EVM program sequence `;` into k-sequence `~>`
    rule OPCODE:OpCode ; P:Program => OPCODE ~> P
endmodule
```

Process State
-------------

EVM Processes are tuples of their associated `PID`, their `ProgramCounter`,
their `WordStack`, and their `LocalMem`.

```k
module EVM-PROCESS-SYNTAX
    imports EVM-STACK-SYNTAX

    syntax AcctID ::= Word
    syntax PID ::= Int "," AcctID   // <stack frame> , <account id>

    syntax LocalMem ::= Map

    syntax Process ::= "{" PID "|" Word "|" WordStack "|" LocalMem "}"

    rule (UOP:UnStackOp   => UOP W0)       ~> { SID , ACCT | PC | (W0 : WS)           => WS | LM }
    rule (BOP:BinStackOp  => BOP W0 W1)    ~> { SID , ACCT | PC | (W0 : W1 : WS)      => WS | LM }
    rule (TOP:TernStackOp => TOP W0 W1 W2) ~> { SID , ACCT | PC | (W0 : W1 : W2 : WS) => WS | LM }
endmodule
```

Call/Return
-----------

```k
module EVM-CALL-SYNTAX
    imports EVM-WORD

    syntax Word ::= "#gatherArgs" Word Word Word
                  | "#mkCall" Word Map
                  | "#recieveReturn" Word Word
endmodule
```
