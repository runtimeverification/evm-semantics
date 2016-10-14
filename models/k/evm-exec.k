// Primitives
// ==========

// Words
// -----

module WORD
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


// Local Execution State
// =====================

// Word Stack
// ----------

module WORD-STACK
    imports WORD

    syntax StackOp ::= "ADD" | "MUL" | "SUB" | "EXP" | "DIV"            // arithmetic
                     | "MOD" | "ADDMOD" | "MULMOD"                      // modular arithmetic
                     | "SIGNEXTEND" | "SDIV" | "SMOD"                   // signed arithmetic
                     | "LT" | "GT" | "SLT" | "SGT" | "EQ" | "ISZERO"    // boolean operations
                     | "AND" | "OR" | "XOR" | "NOT"                     // bitwise operations
                     | "BYTE" | "SHA3"                                  // other
                     | "POP"                                            // stack operation

    syntax WordStack ::= ".WordStack"                           // empty stack
                       | Word ":" WordStack
                       | StackOp "[" WordStack "]" [strict(2)]  // apply a stack operation

    rule ADD [ V0 : V1 : VS ] => V0 +Word V1 : VS                    [structural]
    rule SUB [ V0 : V1 : VS ] => V0 -Word V1 : VS                    [structural]
    rule MUL [ V0 : V1 : VS ] => V0 *Word V1 : VS                    [structural]
    rule DIV [ V0 : V1 : VS ] => V0 /Word V1 : VS requires V1 =/=K 0 [structural]
    rule DIV [ V0 : V1 : VS ] => 0           : VS requires V1 ==K 0  [structural]
    //rule EXP [ V0 : V1 : VS ] => V0 ^Word V1 : VS
    //rule MOD [ V0 : V1 : VS ] => V0 %Word V1 : VS
    //rule LT  [ V0 : V1 : VS ] => bool2Word(V0 <Word V1) : VS
    //rule GT  [ V0 : V1 : VS ] => bool2Word(V0 >Word V1) : VS
    // TODO: define rest of operations need to be defined here

    // Compute the size of the word-stack (for checking validity)
    syntax Int ::= "MAX_STACK_SIZE"
                 | "stackSize" "(" WordStack ")"

    rule MAX_STACK_SIZE => 1024 [macro]

    rule stackSize( .WordStack ) => 0                    [structural]
    rule stackSize( W : WS )     => 1 +Int stackSize(WS) [structural]
endmodule

// Local Memory
// ------------

module LOCAL-MEMORY
    imports WORD

    syntax WordList ::= List{Word,","}

    // helpers for cutting up/putting together local memories
    syntax LocalMem ::= WordList
                      | LocalMem "++" LocalMem
                      | "take" "(" Word "," LocalMem ")"    // keep only so many
                      | "drop" "(" Word "," LocalMem ")"    // remove the front of

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
endmodule

// Local State
// -----------

module EVM-LOCAL-STATE
    imports WORD-STACK
    imports LOCAL-MEMORY

    // Use "&&&" as separator between the WordStack and the LocalMem
    syntax LocalState ::= WordStack "&&&" LocalMem

    syntax LocalOp ::= StackOp
                     | "MLOAD" | "MSTORE" | "MSTORE8"   // memory operations

    syntax LocalState ::= LocalOp "[" LocalState "]"    [strict(2)]

    rule MLOAD  [ V0 : VS      &&& LM ] => LM[V0] : VS &&& LM           [structural]
    rule MSTORE [ V0 : V1 : VS &&& LM ] => VS          &&& LM[V0 := V1] [structural]

    rule SO:StackOp [ WS:WordStack &&& LM:LocalMem ] => SO [ WS ] &&& LM [structural]
endmodule


// EVM Execution
// =============

// EVM Programs
// ------------

module EVM-PROGRAM
    imports EVM-LOCAL-STATE

    configuration <T>
                    <k> $PGM:Program </k>
                    <localState> .WordStack &&& .WordList </localState>
                  </T>

    syntax OpCode ::= LocalOp
                    | "PUSH" Word

    syntax Program ::= "skip"
                     | OpCode ";" Program

    rule OPCODE:OpCode ; P:Program => OPCODE ~> P

    rule <k> PUSH W1 => . ... </k>
         <localState> (WS => W1 : WS) &&& LM </localState>

    rule <k> LO:LocalOp => . ... </k>
         <localState> LS => LO [ LS ] </localState>

    rule <localState> SO:StackOp [ WS:WordStack &&& LM:LocalMem ] => SO [ WS ] &&& LM </localState>
endmodule
