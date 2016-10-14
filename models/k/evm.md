---
title: K Model of EVM Execution Environment
geometry: margin=2.5cm
...


Primitive Data
==============

Words
-----

Words are 256 bit integers. If you want to perform arithmetic on words, make
sure that you use the corresponding `opWord` operators (eg. `+Word`), which will
make sure the correct width is produced.

```k
module EVM-WORD
    syntax Word ::= Int
                  | "chop" "(" Int ")"
                  | "bool2Word" "(" Bool ")"  [strict]
                  | Word "+Word" Word
                  | Word "-Word" Word
                  | Word "*Word" Word
                  | Word "/Word" Word

    rule chop( I:Int ) => I                           requires I <Int (2 ^Int 256) andBool I >=Int 0
    rule chop( I:Int ) => chop( I +Int (2 ^Int 256) ) requires I <Int 0
    rule chop( I:Int ) => chop( I -Int (2 ^Int 256) ) requires I >=Int (2 ^Int 256)

    rule bool2Word(true)  => 1 [function]
    rule bool2Word(false) => 0 [function]

    rule W1:Int +Word W2:Int => chop( W1 +Int W2 )
    rule W1:Int -Word W2:Int => chop( W1 -Int W2 )
    rule W1:Int *Word W2:Int => chop( W1 *Int W2 )
    rule W1:Int /Word W2:Int => chop( W1 /Int W2 )
endmodule
```


Syntax
======

Execution Local
---------------

EVM execution maintains some local state (like a word stack, local memory,
program counter, etc...). We need to specify the syntax of all this local state
for storage.

```k
module EVM-LOCAL-STATE-SYNTAX
    imports EVM-WORD
```

### Word Stack

The `WordStack` is the size-limited (to 1024) stack of words that each local
execution of an EVM process has acess to.

```k
    syntax WordStack ::= ".WordStack"       // empty stack
                       | Word ":" WordStack

    // Compute the size of the word-stack (for checking validity)
    syntax Int ::= "MAX_STACK_SIZE"
                 | "stackSize" "(" WordStack ")"

    rule MAX_STACK_SIZE => 1024 [macro]

    rule stackSize( .WordStack ) => 0                    [structural]
    rule stackSize( W : WS )     => 1 +Int stackSize(WS) [structural]
```

### Local Memory

Each executing EVM process has a local memory as well. It is a word-address
array of words (thus is bounded to $2^256$ entries).

```k
    syntax WordList ::= List{Word,","}

    // helpers for cutting up/putting together local memories
    syntax LocalMem ::= WordList
                      | ".LocalMem"
                      | LocalMem "++" LocalMem
                      | "take" "(" Word "," LocalMem ")"    // keep only so many
                      | "drop" "(" Word "," LocalMem ")"    // remove the front of

    rule .LocalMem  => .WordList [macro]
    rule WL1 ++ WL2 => WL1 , WL2 [macro]

    rule take(0, LM)        => .WordList                                        [structural]
    rule take(N, .WordList) => 0 ++ take(N -Int 1, .WordList) requires N >Int 0 [structural]
    rule take(N, (W , LM))  => W ++ take(N -Int 1, LM)        requires N >Int 0 [structural]

    rule drop(0, LM)        => LM                                   [structural]
    rule drop(N, .WordList) => .WordList                            [structural]
    rule drop(N, (W , LM))  => drop(N -Int 1, LM) requires N >Int 0 [structural]

    // readers
    syntax Word ::= LocalMem "[" Word "]"               // a single element of memory
    syntax LocalMem ::= LocalMem "[" Word ":" Word "]"  // a range of memory

    rule (W:Word , LM:WordList) [ 0 ] => W                              [structural]
    rule LM:LocalMem [ W:Word ]       => drop(W, LM) [ 0 ]              [structural]
    rule LM:LocalMem [ W1 : W2 ]      => take(W2 -Int W1, drop(W1, LM)) [structural]

    // writers
    syntax LocalMem ::= LocalMem "[" Word ":=" Word "]"                 // update a single element
                      | LocalMem "[" Word ":" Word ":=" LocalMem "]"    // update a range of memory

    rule LM:LocalMem [ W1 := W2 ]       => (take(W1, LM) ++ (W2  ++ drop(W1 +Int 1, LM))) [structural]
    rule LM:LocalMem [ W1 : W2 := LM2 ] => (take(W1, LM) ++ (LM2 ++ drop(W2, LM)))        [structural]

endmodule // module LOCAL-STATE-SYNTAX
```

Program Syntax
--------------


EVM Programs are sequences of OPCODEs seperated by semicolons. Right now I've
manually put a `skip` OPCODE in there, as well as a `PUSH` opcode.

```k
module EVM-PROGRAM-SYNTAX
    imports EVM-WORD

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

    syntax LocalOp ::= StackOp
                     | "MLOAD" | "MSTORE" | "MSTORE8"   // memory operations

    syntax OpCode ::= LocalOp
                    | "#push"           // internal stack push operation
                    | "#checkStackSize" // internal stack-size check
                    | "PUSH" Word

    syntax Program ::= "skip"
                     | OpCode ";" Program
endmodule
```

Semantics
=========

Stack Operations
----------------

```k
module EVM-STACK-SEMANTICS
    imports EVM-PROGRAM-SYNTAX

    rule ADD W0 W1 => W0 +Word W1 [structural]
    rule MUL W0 W1 => W0 *Word W1 [structural]
    rule SUB W0 W1 => W0 -Word W1 [structural]
    rule MUL W0 W1 => W0 *Word W1 [structural]
    rule DIV W0 W1 => W0 /Word W1 [structural]
    //rule EXP W0 W1 => W0 ^Word W1 [structural]
    //rule MOD W0 W1 => W0 %Word W1 [structural]
    //rule LT  W0 W1 => bool2Word(W0 <Word W1) [structural]
    //rule GT  W0 W1 => bool2Word(W0 >Word W1) [structural]
    // TODO: define rest of operations need to be defined here
endmodule
```

Entire Program
--------------

```k
module EVM-PROGRAM
    imports EVM-LOCAL-STATE-SYNTAX
    imports EVM-PROGRAM-SYNTAX
    imports EVM-STACK-SEMANTICS

    configuration <T>
                    <k> $PGM:Program </k>
                    <wordStack> .WordStack </wordStack>
                    <localMem> .LocalMem </localMem>
                  </T>

    // Program in the k-cell, replace `;` with k-sequence `~>`
    rule OPCODE:OpCode ; P:Program => OPCODE ~> P

    // result is calculated, put back on stack
    rule <k> (W:Int ~> #push) => . ... </k>
         <wordStack> WS => W : WS </wordStack>

    // these operations load elements from stack for calculation
    // notice that they all either leave stack size alone or decrease it
    rule <k> UOP:UnStackOp => UOP W0 ~> #push ... </k>
         <wordStack> W0 : WS => WS </wordStack>
    rule <k> BOP:BinStackOp => BOP W0 W1 ~> #push ... </k>
         <wordStack> W0 : W1 : WS => WS </wordStack>
    rule <k> TOP:TernStackOp => TOP W0 W1 W2 ~> #push ... </k>
         <wordStack> W0 : W1 : W2 : WS => WS </wordStack>

    // this can push the stackSize past MAX_STACK_SIZE
    rule <k> PUSH W => #checkStackSize ... </k>
         <wordStack> WS => W : WS </wordStack>

    // TODO: Actually check stack size
    rule #checkStackSize => .
endmodule
```

