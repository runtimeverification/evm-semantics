---
title: K Model of EVM Execution Environment
geometry: margin=2.5cm
...


Primitives
==========

Words
-----

Words are 256 bits. Right now we are not making them only 256 bits wide.

```k
module WORD
    // TODO: Make Words only 256 bits wide
    syntax Word ::= Int
                  | "bool2Word" "(" Bool ")"  [strict]
    rule bool2Word(true)  => 1 [function]
    rule bool2Word(false) => 0 [function]
endmodule
```


Local Execution State
=====================

Word Stack
----------

The `WordStack` is the size-limited (to 1024) stack of words that each local
execution of an EVM process has acess to. Stack operations are defined over the
stack, and are applied with square braces.

```k
module WORD-STACK
    imports WORD

    syntax StackOp     ::= "ADD" | "MUL" | "SUB" | "EXP" | "DIV"            // arithmetic
                         | "MOD" | "ADDMOD" | "MULMOD"                      // modular arithmetic
                         | "SIGNEXTEND" | "SDIV" | "SMOD"                   // signed arithmetic
                         | "LT" | "GT" | "SLT" | "SGT" | "EQ" | "ISZERO"    // boolean operations
                         | "AND" | "OR" | "XOR" | "NOT"                     // bitwise operations
                         | "BYTE" | "SHA3"                                  // other
                         | "POP"                                            // stack operation

    syntax WordStack ::= ".WordStack"               // empty stack
                       | Word ":" WordStack
                       | StackOp "[" WordStack "]"  // apply a stack operation

    rule ADD [ V0 : V1 : VS ] => V0 +Int V1 : VS
    rule SUB [ V0 : V1 : VS ] => V0 -Int V1 : VS
    rule MUL [ V0 : V1 : VS ] => V0 *Int V1 : VS
    rule DIV [ V0 : V1 : VS ] => V0 /Int V1 : VS requires V1 =/=K 0
    rule DIV [ V0 : V1 : VS ] => 0          : VS requires V1 ==K 0
    rule EXP [ V0 : V1 : VS ] => V0 ^Int V1 : VS
    rule MOD [ V0 : V1 : VS ] => V0 %Int V1 : VS
    rule LT  [ V0 : V1 : VS ] => bool2Word(V0 <Int V1) : VS
    rule GT  [ V0 : V1 : VS ] => bool2Word(V0 >Int V1) : VS
    // TODO: define rest of operations need to be defined here

    // Compute the size of the word-stack (for checking validity)
    syntax Nat ::= "MAX_STACK_SIZE"
                 | "stackSize" "(" WordStack ")"

    rule MAX_STACK_SIZE => 1024 [macro]
    rule stackSize( .WordStack ) => 0
    rule stackSize( W : WS )     => 1 + stackSize(WS)
endmodule
```

Local Memory
------------

Each executing EVM process has a local memory as well. It is a word-address
array of words (thus is bounded to $2^256$ entries).

```k
module LOCAL-MEMORY
    imports WORD

    syntax WordList ::= List{Word,","}

    // helpers for cutting up local memories
    syntax LocalMem ::= WordList
                      | LocalMem "++" LocalMem
                      | "take" "(" Word "," LocalMem ")"    // keep only so many
                      | "drop" "(" Word "," LocalMem ")"    // remove the front of

    rule WL1 ++ WL2 => WL1 , WL2 [macro]

    rule take(0, LM)        => .WordList
    rule take(N, .WordList) => 0 ++ take(N -Int 1, .WordList) requires N >Int 0
    rule take(N, (W , LM))  => W ++ take(N -Int 1, LM)        requires N >Int 0

    rule drop(0, LM)        => LM
    rule drop(N, .WordList) => .WordList
    rule drop(N, (W , LM))  => drop(N -Int 1, LM) requires N >Int 0

    // readers
    syntax Word ::= LocalMem "[" Word "]"               // a single element of memory
    syntax LocalMem ::= LocalMem "[" Word ":" Word "]"  // a range of memory

    rule (W:Word , LM:WordList) [ 0 ] => W
    rule LM:LocalMem [ W:Word ]       => drop(W, LM) [ 0 ]
    rule LM:LocalMem [ W1 : W2 ]      => take(W2 -Int W1, drop(W1, LM))

    // writers
    syntax LocalMem ::= LocalMem "[" Word ":=" Word "]"                 // update a single element
                      | LocalMem "[" Word ":" Word ":=" LocalMem "]"    // update a range of memory

    rule LM:LocalMem [ W1 := W2 ]       => (take(W1, LM) ++ (W2  ++ drop(W1 +Int 1, LM)))
    rule LM:LocalMem [ W1 : W2 := LM2 ] => (take(W1, LM) ++ (LM2 ++ drop(W2, LM)))
endmodule
```


Configuration
=============

```k
module EVM-CONFIGURATION
    configuration <T>
                    <k> </k>

                    <callStack>
                        <stackSize> 0 </stackSize>
                        <stack> .List </stack>
                        <stackFrame multiplicity="*">
                            <frameID> .FrameID </frameID>
                            <programCounter> 0 </programCounter>
                            <wordStack> .WordStack </wordStack>
                            <localMem> .LocalMem </localMem>
                        </stackFrame>
                    </callStack>

                    <worldState>
                        <accountState multiplicity="*">
                            <address> .Address </address>
                            <storage> .Map </storage>
                        </accountState>
                    </worldState>
                  </T>

    // example rule
    rule <k> SO:StackOp => . ... </k>
         <stack> FID ... </stack>
         <stackFrame>
             <frameID> FID </frameID>
             <programCounter> PC => PC + 1 </programCounter>
             <wordStack> WS => SO [ WS ] </wordStack>
             ...
         </stackFrame>

    syntax LocalMem    ::= ".LocalMem"

    syntax Address     ::= Nat | ".Address"

    syntax FrameNumber ::= Nat
    syntax FrameID     ::= ".FrameID"
                         | FrameNumber "|" Address
endmodule
```
