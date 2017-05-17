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

    syntax Word ::= Int
                  | "#symbolicWord"               [function]
                  | chop ( Int )                  [function]
                  | bool2Word ( Bool )            [function]
                  | Word "+Word" Word             [function]
                  | Word "*Word" Word             [function]
                  | Word "-Word" Word             [function]
                  | Word "/Word" Word             [function]
                  | Word "^Word" Word             [function]
                  | Word "%Word" Word             [function]
                  | signextend ( Word , Word )    [function] // needs implemented
                  | Word "<Word" Word             [function]
                  | Word ">Word" Word             [function]
                  | Word "==Word" Word            [function]
                  | bitwisenot ( Word )           [function] // needs implemented
                  | sdiv ( Word , Word )          [function] // needs implemented
                  | smod ( Word , Word )          [function] // needs implemented
                  | slt ( Word , Word )           [function] // needs implemented
                  | sgt ( Word , Word )           [function] // needs implemented
                  | bitwiseand ( Word , Word )    [function] // needs implemented
                  | bitwiseor ( Word , Word )     [function] // needs implemented
                  | bitwisexor ( Word , Word )    [function] // needs implemented
                  | getbyte ( Word , Word )       [function] // needs implemented
                  | sha3 ( Word , Word )          [function] // needs implemented
                  | addmod ( Word , Word , Word ) [function]
                  | mulmod ( Word , Word , Word ) [function]

    rule #symbolicWord => ?X:Int

    rule chop( I:Int ) => I                           requires I <Int (2 ^Int 256) andBool I >=Int 0
    rule chop( I:Int ) => chop( I +Int (2 ^Int 256) ) requires I <Int 0
    rule chop( I:Int ) => chop( I -Int (2 ^Int 256) ) requires I >=Int (2 ^Int 256)

    rule bool2Word(true)  => 1
    rule bool2Word(false) => 0

    rule W0:Int +Word W1:Int  => chop( W0 +Int W1 )
    rule W0:Int -Word W1:Int  => chop( W0 -Int W1 )
    rule W0:Int *Word W1:Int  => chop( W0 *Int W1 )
    rule W0:Int /Word W1:Int  => chop( W0 /Int W1 )
    rule W0:Int ^Word W1:Int  => chop( W0 ^Int W1 )
    rule W0:Int <Word W1:Int  => bool2Word( W0 <Int W1 )
    rule W0:Int >Word W1:Int  => bool2Word( W0 >Int W1 )
    rule W0:Int ==Word W1:Int => bool2Word( W0 ==Int W1)
    rule W0:Int %Word W1:Int  => chop( W0 %Int W1 )

    rule addmod(W0:Int, W1:Int, 0)      => 0
    rule addmod(W0:Int, W1:Int, W2:Int) => chop((W0 +Int W1) %Int W2) [owise]

    rule mulmod(W0:Int, W1:Int, 0)      => 0
    rule mulmod(W0:Int, W1:Int, W2:Int) => chop((W0 *Int W1) %Int W2) [owise]
```

Word Stack
----------

EVM is a stack machine, and so needs a stack of words to operate on. The stack
and some standard operations over it are provided here. Note that this stack
also serves as a cons-list, so we provide some standard cons-list manipulation
tools over it.

TODO: Should all operations zero-pad the word-stack when there is an over-flow?
It's specified in the yellowpaper for `PUSH`, but not for `DUP` and `SWAP`. The
way `_[_]` and `_[_:=_]` is implemented will do this.

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
 // ----------------------------------------------------------
    rule #take(0, WS)            => .WordStack
    rule #take(N, .WordStack)    => 0 : #take(N -Word 1, .WordStack) requires N >Word 0
    rule #take(N, (W:Word : WS)) => W : #take(N -Word 1, WS)         requires N >Word 0
```

Word Map
--------

Most of EVM data is held in finite maps. Here standard maps from `Word` to
`Word` are provided. A common idiom is to assign a contiguous chunk of a map to
a list (stack) of words, or to read a contiguous chunk of a map as a list, so
the functionality for that is provided as well.

```k
    syntax WordMap ::= Map
                     | WordMap "[" Word ":=" WordStack "]" [function]
 // -----------------------------------------------------------------
    rule WM[N := .WordStack]   => WM
    rule WM[N := W0:Word : WS] => (WM[N <- W0])[N +Word 1 := WS]
    
    syntax WordMap ::= #asMap ( WordStack ) [function]
 // --------------------------------------------------
    rule #asMap(WS) => .Map [ 0 := WS ]

    syntax WordStack ::= #range ( WordMap , Word , Word ) [function]
 // ----------------------------------------------------------------
    rule #range(WM,         N, M) => .WordStack                           requires M ==Word 0
    rule #range(N |-> W WM, N, M) => W : #range(WM, N +Word 1, M -Word 1) requires M >Word 0
endmodule
```

EVM OpCodes
===========

NOTE: We have to call the opcode `OR` by `EVMOR` instead, because otherwise K
has trouble parsing it/compiling the definition.

```k
module EVM-OPCODE
    imports EVM-WORD
    imports STRING

    syntax InternalOps ::= "#push" | "#setStack" WordStack | "#checkStackSize"
 // --------------------------------------------------------------------------
    rule (I:Int ~> #checkStackSize) => .              requires I <Int  1024
    rule (I:Int ~> #checkStackSize) => STACK_OVERFLOW requires I >=Int 1024

    syntax NullStackOp ::= "STACK_OVERFLOW"
                         | "PC" | "MSIZE" | "GAS"
                         | "STOP" | "ADDRESS" | "ORIGIN" | "CALLER"
                         | "CALLVALUE" | "CALLDATASIZE" | "GASPRICE" | "CODESIZE"
                         | "COINBASE" | "TIMESTAMP" | "NUMBER" | "DIFFICULTY" | "GASLIMIT"
 // --------------------------------------------------------------------------------------

    syntax UnStackOp ::= "ISZERO" | "NOT" | "POP"
                       | "JUMP" | "MLOAD"
                       | "CALLDATALOAD" | "EXTCODESIZE"
 // ---------------------------------------------------
    rule ISZERO 0 => bool2Word(true)  ~> #push
    rule ISZERO N => bool2Word(false) ~> #push requires N =/=K 0
    rule NOT    N => bitwisenot(N)    ~> #push
    rule POP    N => .

    syntax BinStackOp ::= "ADD" | "MUL" | "SUB" | "DIV" | "EXP"
                        | "MOD" | "SIGNEXTEND" | "SDIV" | "SMOD"
                        | "LT" | "GT" | "SLT" | "SGT" | "EQ"
                        | "AND" | "EVMOR" | "XOR"
                        | "BYTE" | "SHA3"
                        | "JUMPI" | "RETURN" | "MSTORE" | "MSTORE8"
 // ---------------------------------------------------------------
    rule ADD        W0 W1 => W0 +Word W1       ~> #push
    rule MUL        W0 W1 => W0 *Word W1       ~> #push
    rule SUB        W0 W1 => W0 -Word W1       ~> #push
    rule DIV        W0 W1 => W0 /Word W1       ~> #push
    rule EXP        W0 W1 => W0 ^Word W1       ~> #push
    rule MOD        W0 W1 => W0 %Word W1       ~> #push
    rule SIGNEXTEND W0 W1 => signextend(W0,W1) ~> #push
    rule SDIV       W0 W1 => sdiv(W0,W1)       ~> #push
    rule SMOD       W0 W1 => smod(W0,W1)       ~> #push
    rule LT         W0 W1 => W0 <Word W1       ~> #push
    rule GT         W0 W1 => W0 >Word W1       ~> #push
    rule SLT        W0 W1 => slt(W0,W1)        ~> #push
    rule SGT        W0 W1 => sgt(W0,W1)        ~> #push
    rule EQ         W0 W1 => W0 ==Word W1      ~> #push
    rule AND        W0 W1 => bitwiseand(W0,W1) ~> #push
    rule EVMOR      W0 W1 => bitwiseor(W0,W1)  ~> #push
    rule XOR        W0 W1 => bitwisexor(W0,W1) ~> #push
    rule BYTE       W0 W1 => getbyte(W0,W1)    ~> #push
    rule SHA3       W0 W1 => sha3(W0,W1)       ~> #push

    syntax TernStackOp ::= "ADDMOD" | "MULMOD"
 // ------------------------------------------
    rule ADDMOD W0 W1 W2 => addmod(W0,W1,W2) ~> #push
    rule MULMOD W0 W1 W2 => mulmod(W0,W1,W2) ~> #push

    syntax StackOp ::= DUP ( Word ) | SWAP ( Word )
 // -----------------------------------------------
    rule DUP(N)  WS:WordStack => #pushStack ((WS [ N -Word 1 ]) : WS)
    rule SWAP(N) (W0 : WS)    => #pushStack ((WS [ N -Word 1 ]) : (WS [ N -Word 1 := W0 ]))

    syntax CallOp ::= "CALL"
    syntax PushOp ::= PUSH ( Word )
    syntax LogOp  ::= LOG ( Word )
    syntax SpecialOp ::= CallOp | PushOp | LogOp | StackOp
 // ------------------------------------------------------
    rule PUSH(W) => W ~> #push
```

Here, all the operators that have not been binned/implemented are thrown (as
well as the subsorts).

```k
    syntax OpCode ::= NullStackOp | UnStackOp | BinStackOp | TernStackOp | SpecialOp | StackOp | InternalOps
                    | "BALANCE" | "BLOCKHASH" | "CALLCODE" | "CALLDATACOPY" | "CODECOPY" | "CREATE" | "EXTCODECOPY"
                    | "JUMPDEST" | "SLOAD" | "SSTORE" | "DELEGATECALL" | "INVALID" | "SELFDESTRUCT"
 // -----------------------------------------------------------------------------------------------
    syntax KItem ::= OpCode
                   | UnStackOp Word
                   | BinStackOp Word Word
                   | TernStackOp Word Word Word
                   | CallOp Word Word Word Word Word Word Word
                   | StackOp WordStack
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

