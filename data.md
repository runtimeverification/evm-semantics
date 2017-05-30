EVM Words
=========

EVM uses bounded 256 bit integer words. Here we provide the arithmetic of these
words, as well as some data-structures over them.

Word Operations
---------------

To perform arithmetic on words, make sure that you use the corresponding
`<op>Word` operators (eg. `+Word`), which will make sure that the correct
rounding modes are used when performing the operations.

```k
module EVM-WORD

    syntax KResult ::= Int 
```

We need to do arithmetic modulo `2^256` and need to interperet words as
booleans. Here `chop` will move a number back into the correct range and `bool2Word` will interperet

```k
    syntax Word ::= Int
                  | "#symbolicWord"    [function]
                  | chop ( Word )      [function]
                  | bool2Word ( Bool ) [function]
 // ---------------------------------------------
    rule #symbolicWord    => ?X:Int
    rule chop( W:Int )    => W %Int (2 ^Int 256)
    rule bool2Word(true)  => 1
    rule bool2Word(false) => 0

    syntax Bool ::= word2Bool ( Word ) [function]
 // ---------------------------------------------
    rule word2Bool( 0 ) => false
    rule word2Bool( W ) => true  requires W =/=K 0

    syntax Word ::= Word "+Word" Word [function]
                  | Word "*Word" Word [function]
                  | Word "-Word" Word [function]
                  | Word "/Word" Word [function]
                  | Word "^Word" Word [function]
                  | Word "%Word" Word [function]
 // --------------------------------------------
    rule W0:Int +Word W1:Int => chop( W0 +Int W1 )
    rule W0:Int -Word W1:Int => chop( W0 -Int W1 )
    rule W0:Int *Word W1:Int => chop( W0 *Int W1 )
    rule W0:Int /Word W1:Int => chop( W0 /Int W1 )
    rule W0:Int ^Word W1:Int => chop( W0 ^Int W1 )
    rule W0:Int %Word 0      => 0 
    rule W0:Int %Word W1:Int => chop( W0 %Int W1 ) requires W1 =/=K 0

    syntax Word ::= Word "<Word"  Word [function]
                  | Word ">Word"  Word [function]
                  | Word "<=Word" Word [function]
                  | Word ">=Word" Word [function]
                  | Word "==Word" Word [function]
 // ---------------------------------------------
    rule W0:Int <Word  W1:Int => bool2Word(W0 <Int  W1)
    rule W0:Int >Word  W1:Int => bool2Word(W0 >Int  W1)
    rule W0:Int <=Word W1:Int => bool2Word(W0 <=Int W1)
    rule W0:Int >=Word W1:Int => bool2Word(W0 >=Int W1)
    rule W0:Int ==Word W1:Int => bool2Word(W0 ==Int W1)

    syntax Word ::= "~Word" Word        [function]
                  | Word "|Word" Word   [function]
                  | Word "&Word" Word   [function]
                  | Word "xorWord" Word [function]
 // ----------------------------------------------
    rule ~Word W:Int           => chop( W xorInt ((2 ^Int 256) -Int 1) )
    rule W0:Int |Word   W1:Int => chop( W0 |Int W1 )
    rule W0:Int &Word   W1:Int => chop( W0 &Int W1 )
    rule W0:Int xorWord W1:Int => chop( W0 xorInt W1 )
```

TODO: The following are unimplemented.

```k
    syntax Word ::= signextend ( Word , Word ) [function]
                  | sdiv ( Word , Word )       [function]
                  | smod ( Word , Word )       [function]
                  | slt ( Word , Word )        [function]
                  | sgt ( Word , Word )        [function]
                  | getbyte ( Word , Word )    [function]
                  | sha3 ( Word , Word )       [function]
 // -----------------------------------------------------
```

Word Stack
----------

EVM is a stack machine, and so needs a stack of words to operate on. The stack
and some standard operations over it are provided here. This stack also serves
as a cons-list, so we provide some standard cons-list manipulation tools.

TODO: Should all operations zero-pad the word-stack when there is an over-flow?
It's specified in the yellowpaper for `PUSH`, but not for `DUP` and `SWAP`.
`_[_]` and `_[_:=_]` should be set to whichever convention is used most often.

```k
    syntax WordStack ::= ".WordStack"
                       | Word ":" WordStack
 // ---------------------------------------

    syntax Word ::= WordStack "[" Word "]" [function]
 // -------------------------------------------------
    rule (W0 : WS)   [0] => W0
    rule (.WordStack)[N] => 0             requires N >Word 0
    rule (W0 : WS)   [N] => WS[N -Word 1] requires N >Word 0

    syntax WordStack ::= WordStack "[" Word ":=" Word "]" [function]
 // ----------------------------------------------------------------
    rule (W0 : WS)  [ 0 := W ] => W  : WS
    rule .WordStack [ N := W ] => 0  : (.WordStack [ N +Int 1 := W ]) requires N >Word 0
    rule (W0 : WS)  [ N := W ] => W0 : (WS [ N +Int 1 := W ])         requires N >Word 0

    syntax Word ::= #stackSize ( WordStack ) [function]
 // ---------------------------------------------------
    rule #stackSize ( .WordStack ) => 0
    rule #stackSize ( W : WS )     => 1 +Word #stackSize(WS)

    syntax WordStack ::= #take ( Word , WordStack ) [function]
                       | #drop ( Word , WordStack ) [function]
 // ----------------------------------------------------------
    rule #take(0, WS)            => .WordStack
    rule #take(N, .WordStack)    => 0 : #take(N -Word 1, .WordStack) requires N >Word 0
    rule #take(N, (W:Word : WS)) => W : #take(N -Word 1, WS)         requires N >Word 0

    rule #drop(0, WS)            => WS
    rule #drop(N, .WordStack)    => .WordStack
    rule #drop(N, (W:Word : WS)) => #drop(N -Word 1, WS) requires N >Word 0
```

Word Map
--------

Most of EVM data is held in finite maps. Here, finite maps from `Word` to `Word`
are provided. A common idiom is to assign a contiguous chunk of a map to a list
(stack) of words, or to read a contiguous chunk of a map as a list, so the
functionality for that is provided as well.

```k
    syntax WordMap ::= Map
                     | WordMap "[" Word ":=" WordStack "]" [function]
 // -----------------------------------------------------------------
    rule WM[N := .WordStack]   => WM
    rule WM[N := W0:Word : WS] => (WM[N <- W0])[N +Word 1 := WS]
    
    syntax Map ::= #asMap ( WordStack ) [function]
 // ----------------------------------------------
    rule #asMap(WS) => .Map [ 0 := WS ]

    syntax WordStack ::= #range ( WordMap , Word , Word ) [function]
 // ----------------------------------------------------------------
    rule #range(WM,         N, M) => .WordStack                           requires M ==Word 0
    rule #range(N |-> W WM, N, M) => W : #range(WM, N +Word 1, M -Word 1) requires M >Word 0
endmodule
```

EVM Opcodes
===========

NOTE: We have to call the opcode `OR` by `EVMOR` instead, because otherwise K
has trouble parsing it/compiling the definition.

Opcodes are broken into several different subsorts, to represent the different
ways they read data from the environment. Later in the semantics, this sort
information is used to load data from the execution context automatically,
allowing us to specify the simplification of the operators here.

```k
module EVM-OPCODE
    imports EVM-WORD

    syntax KItem ::= OpCode
                   | UnStackOp Word
                   | BinStackOp Word Word
                   | TernStackOp Word Word Word
                   | QuadStackOp Word Word Word Word
                   | CallOp Word Word Word Word Word Word Word
                   | "DELEGATECALL" Word Word Word Word Word Word
                   | StackOp WordStack
```

Internal operators are used for assisting in the definition of the actual
opcodes.

```k
    syntax InternalOp ::= "#push" | "#setStack" WordStack | "#checkStackSize" | "#stackOverflow"
 // --------------------------------------------------------------------------------------------
    rule (I:Int ~> #checkStackSize) => .              requires I <Int  1024
    rule (I:Int ~> #checkStackSize) => #stackOverflow requires I >=Int 1024
```

Operators that need a fixed/finite number of arguments from the stack are given
their own sorts to specify how many they need (up to `TernStackOp`).

```k
    syntax NullStackOp ::= "JUMPDEST" | "INVALID"
                         | "STOP" | "ADDRESS" | "ORIGIN" | "CALLER"
                         | "CALLVALUE" | "CALLDATASIZE" | "GASPRICE" | "CODESIZE"
                         | "COINBASE" | "TIMESTAMP" | "NUMBER" | "DIFFICULTY"
                         | "GASLIMIT" | "CALLVALUE" | "PC" | "MSIZE" | "GAS"
 // ------------------------------------------------------------------------

    syntax UnStackOp ::= "ISZERO" | "NOT" | "POP"
                       | "JUMP" | "MLOAD" | "CALLDATALOAD" | "EXTCODESIZE"
                       | "BALANCE" | "BLOCKHASH" | "SLOAD" | "SELFDESTRUCT"
 // -----------------------------------------------------------------------
    rule ISZERO 0 => bool2Word(true)  ~> #push
    rule ISZERO W => bool2Word(false) ~> #push requires W =/=K 0
    rule NOT    W => ~Word W          ~> #push
    rule POP    W => .

    syntax BinStackOp ::= "ADD" | "MUL" | "SUB" | "DIV" | "EXP"
                        | "MOD" | "AND" | "EVMOR" | "XOR"
                        | "LT" | "GT" | "EQ" | "JUMPI"
                        | "SLT" | "SGT" | "SDIV" | "SMOD" | "SIGNEXTEND"
                        | "BYTE" | "SHA3"
                        | "RETURN" | "SSTORE" | "MSTORE" | "MSTORE8"
 // ----------------------------------------------------------------
    rule ADD W0 W1 => W0 +Word W1 ~> #push
    rule MUL W0 W1 => W0 *Word W1 ~> #push
    rule SUB W0 W1 => W0 -Word W1 ~> #push
    rule DIV W0 W1 => W0 /Word W1 ~> #push
    rule EXP W0 W1 => W0 ^Word W1 ~> #push
    rule MOD W0 W1 => W0 %Word W1 ~> #push

    rule AND   W0 W1 => W0 &Word W1   ~> #push
    rule EVMOR W0 W1 => W0 |Word W1   ~> #push
    rule XOR   W0 W1 => W0 xorWord W1 ~> #push

    rule LT W0 W1 => W0 <Word W1  ~> #push
    rule GT W0 W1 => W0 >Word W1  ~> #push
    rule EQ W0 W1 => W0 ==Word W1 ~> #push

    rule JUMPI DEST 0 => .
    rule JUMPI DEST W => JUMP DEST requires W =/=K 0
```

TODO: The following need implemented (once the corresponding `WORD` operations
are implemented above).

```k
 // rule SDIV       W0 W1 => ???
 // rule SMOD       W0 W1 => ???
 // rule SIGNEXTEND W0 W1 => ???
 // rule BYTE       W0 W1 => ???
 // rule SHA3       W0 W1 => ???
 // rule SLT        W0 W1 => ???
 // rule SGT        W0 W1 => ???

    syntax TernStackOp ::= "ADDMOD" | "MULMOD" | "CALLDATACOPY" | "CODECOPY" | "CREATE"
 // -----------------------------------------------------------------------------------
    rule ADDMOD W0 W1 W2 => (W0 +Word W1) %Word W2 ~> #push
    rule MULMOD W0 W1 W2 => (W0 *Word W1) %Word W2 ~> #push

    syntax QuadStackOp ::= "EXTCODECOPY"
 // ------------------------------------
```

Some operators need the "entire" stack (or at least a large chunk of it).

```k
    syntax StackOp ::= DUP ( Word ) | SWAP ( Word )
 // -----------------------------------------------
    rule DUP(N)  WS:WordStack => #pushStack ((WS [ N -Word 1 ]) : WS)
    rule SWAP(N) (W0 : WS)    => #pushStack ((WS [ N -Word 1 ]) : (WS [ N -Word 1 := W0 ]))
```

TODO: `DELEGATECALL` is just binned in with `SpecialOp` because it doesn't take
the same number of arguments as the rest of the `CallOp`s.

```k
    syntax CallOp ::= "CALL" | "CALLCODE"
    syntax PushOp ::= PUSH ( Word )
    syntax LogOp  ::= LOG ( Word )
    syntax SpecialOp ::= CallOp | PushOp | LogOp | "DELEGATECALL"
 // -------------------------------------------------------------
    rule PUSH(W) => W ~> #push
```

Here, all the operators are subsorted into `OpCode`.

```k
    syntax OpCode ::= NullStackOp | UnStackOp | BinStackOp | TernStackOp
                    | QuadStackOp | StackOp | SpecialOp | InternalOp
 // ----------------------------------------------------------------
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
endmodule
```
