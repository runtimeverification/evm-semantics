// Primitive Data
// ==============

// Words
// -----

module EVM-WORD
    syntax Word ::= Int
                  | "chop" "(" Int ")"       [strict]
                  | "bool2Word" "(" Bool ")" [strict]
                  | Word "+Word" Word        [strict]
                  | Word "-Word" Word        [strict]
                  | Word "*Word" Word        [strict]
                  | Word "/Word" Word        [strict]
                  | Word "^Word" Word        [strict]

    syntax KResult ::= Int

    rule chop( I:Int ) => I                           requires I <Int (2 ^Int 256) andBool I >=Int 0
    rule chop( I:Int ) => chop( I +Int (2 ^Int 256) ) requires I <Int 0
    rule chop( I:Int ) => chop( I -Int (2 ^Int 256) ) requires I >=Int (2 ^Int 256)

    rule bool2Word(true)  => 1
    rule bool2Word(false) => 0

    rule W1:Int +Word W2:Int => chop( W1 +Int W2 )
    rule W1:Int -Word W2:Int => chop( W1 -Int W2 )
    rule W1:Int *Word W2:Int => chop( W1 *Int W2 )
    rule W1:Int /Word W2:Int => chop( W1 /Int W2 )
    rule W1:Int ^Word W2:Int => chop( W1 ^Int W2 )
endmodule


// Local Execution State
// =====================

// Word Stack
// ----------

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

module EVM-STACK-SEMANTICS
    imports EVM-STACK-SYNTAX

    rule ADD W0 W1 => W0 +Word W1 [structural]
    rule MUL W0 W1 => W0 *Word W1 [structural]
    rule SUB W0 W1 => W0 -Word W1 [structural]
    rule MUL W0 W1 => W0 *Word W1 [structural]
    rule DIV W0 W1 => W0 /Word W1 [structural]
    rule EXP W0 W1 => W0 ^Word W1 [structural]
    //rule MOD W0 W1 => W0 %Word W1 [structural]
    //rule LT  W0 W1 => bool2Word(W0 <Word W1) [structural]
    //rule GT  W0 W1 => bool2Word(W0 >Word W1) [structural]
    // TODO: define rest of operations
endmodule

// Program Syntax
// --------------

module EVM-PROGRAM-SYNTAX
    imports EVM-STACK-SYNTAX

    syntax LocalOp ::= StackOp | "MLOAD" | "MSTORE"
                     // | "MLOAD8"

    syntax ExnOp ::= "STACK_OVERFLOW" Int

    syntax OpCode ::= LocalOp
                    | ExnOp
                    | "#push"           // internal stack push operation
                    | "#checkStackSize" // internal stack-size check
                    | "PUSH" Word

    syntax Program ::= "skip"
                     | OpCode ";" Program

    rule (I:Int ~> #checkStackSize) => .                requires I <Int MAX_STACK_SIZE
    rule (I:Int ~> #checkStackSize) => STACK_OVERFLOW I requires I >=Int  MAX_STACK_SIZE

    // turn EVM program sequence `;` into k-sequence `~>`
    rule OPCODE:OpCode ; P:Program => OPCODE ~> P
endmodule


// Semantics
// =========

// Configuration
// -------------

module EVM-CONFIGURATION
    imports EVM-PROGRAM-SYNTAX

    configuration <T>
                    <k> $PGM:Program </k>
                    <wordStack> .WordStack </wordStack>
                    <localMem> .Map </localMem>
                  </T>
endmodule

// Entire Program
// --------------

module EVM-PROGRAM
    imports EVM-CONFIGURATION
    imports EVM-STACK-SEMANTICS

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
    rule <k> PUSH W => stackSize(WS) ~> #checkStackSize ~> W ~> #push ... </k>
         <wordStack> WS </wordStack>

    // load/store elements in memory
    rule <k> MLOAD => . ... </k>
         <wordStack> W0 : WS => M : WS </wordStack>
         <localMem> ... W0 |-> M ... </localMem>

    rule <k> MLOAD => . ... </k>
         <wordStack> W0 : WS => 0 : WS </wordStack>
         <localMem> Rho:Map </localMem>
         requires notBool (W0 in keys(Rho))

    rule <k> MSTORE => . ... </k>
         <wordStack> W0 : W1 : WS => WS </wordStack>
         <localMem> ... W0 |-> (_ => W1) ... </localMem>

    rule <k> MSTORE => . ... </k>
         <wordStack> W0 : W1 : WS => WS </wordStack>
         <localMem> Rho:Map (.Map => W0 |-> W1) </localMem>
         requires notBool (W0 in keys(Rho))
endmodule
