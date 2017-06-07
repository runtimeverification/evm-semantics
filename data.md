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
module EVM-DATA

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

TODO: Unimplemented.

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

    syntax Bool ::= Word "in" WordStack [function]
 // ----------------------------------------------
    rule W in .WordStack => false
    rule W in (W' : WS)  => (W ==K W') orElseBool (W in WS)
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
                 | #asMap ( Map       ) [function]
 // ----------------------------------------------
    rule #asMap(WS:WordStack) => .Map [ 0 := WS ]
    rule #asMap(M:Map)        => M

    syntax WordStack ::= #range ( WordMap , Word , Word ) [function]
 // ----------------------------------------------------------------
    rule #range(WM,         N, M) => .WordStack                           requires M ==Word 0
    rule #range(N |-> W WM, N, M) => W : #range(WM, N +Word 1, M -Word 1) requires M >Word 0
endmodule
```
