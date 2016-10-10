---
title: K Model of EVM Execution Environment
geometry: margin=2.5cm
...


Word Stack
==========

```k
module WORD-STACK
    syntax StackOp     ::= "ADD" | "MUL" | "SUB" | "EXP" | "DIV" | "MOD" |
                           "SDIV" | "SMOD" "ADDMOD" | "MULMOD" | "SIGNEXTEND" |
                           "LT" | "GT" | "SLT" | "SGT" "EQ" | "ISZERO" | "AND" |
                           "OR" | "XOR" | "NOT" | "BYTE" | "SHA3" | "POP"

    syntax Word        ::= Int
                         | "bool2Int" "(" Bool ")"
    syntax WordStack   ::= ".WordStack"
                         | Word ":" WordStack
                         | StackOp "[" WordStack "]"

    rule ADD [ V0 : V1 : VS ] => V0 +Int V1 : VS
    rule SUB [ V0 : V1 : VS ] => V0 -Int V1 : VS
    rule MUL [ V0 : V1 : VS ] => V0 *Int V1 : VS
    rule DIV [ V0 : V1 : VS ] => V0 /Int V1 : VS requires V1 =/=K 0
    rule DIV [ V0 : V1 : VS ] => 0          : VS requires V1 ==K 0
    rule EXP [ V0 : V1 : VS ] => V0 ^Int V1 : VS
    rule MOD [ V0 : V1 : VS ] => V0 %Int V1 : VS
    rule LT  [ V0 : V1 : VS ] => bool2int(V0 <Int V1)
    rule GT  [ V0 : V1 : VS ] => bool2int(V0 >Int V1)
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


    syntax LocalMem    ::= ".LocalMem"

    syntax Address     ::= Nat | ".Address"

    syntax FrameNumber ::= Nat
    syntax FrameID     ::= ".FrameID"
                         | FrameNumber "|" Address
endmodule
```
