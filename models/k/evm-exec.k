// Word Stack
// ==========

module WORD-STACK
    syntax StackOp     ::= "ADD" | "MUL" | "SUB" | "EXP" | "DIV" | "MOD" |
                           "SDIV" | "SMOD" "ADDMOD" | "MULMOD" | "SIGNEXTEND" |
                           "LT" | "GT" | "SLT" | "SGT" "EQ" | "ISZERO" | "AND" |
                           "OR" | "XOR" | "NOT" | "BYTE" | "SHA3" | "POP"

    syntax Word        ::= Int
                         | "bool2Int" "(" Bool ")"
    rule bool2Int(true)  => 1
    rule bool2Int(false) => 0

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
    rule LT  [ V0 : V1 : VS ] => bool2int(V0 <Int V1) : VS
    rule GT  [ V0 : V1 : VS ] => bool2int(V0 >Int V1) : VS
endmodule
