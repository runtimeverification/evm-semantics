Data-Structures over `Word`
===========================

EVM uses bounded 256 bit integer words, and sometimes also bytes (8 bit words).
Here we provide the arithmetic of these words, as well as some data-structures over them.
Both are implemented using K's `Int`.

```k
requires "word.md"

module EVM-TYPES
    imports STRING
    imports COLLECTIONS
    imports K-EQUAL
    imports JSON
    imports WORD
```

Utilities
---------

### Boolean Conversions

Primitives provide the basic conversion from K's sorts `Int` and `Bool` to EVM's words.

-   `bool2Word` interprets a `Bool` as a `Int`.
-   `word2Bool` interprets a `Int` as a `Bool`.

```k
    syntax Int ::= bool2Word ( Bool ) [symbol(bool2Word), function, total, injective, smtlib(bool2Word)]
 // ----------------------------------------------------------------------------------------------------
    rule bool2Word( true  ) => 1
    rule bool2Word( false ) => 0

    syntax Bool ::= word2Bool ( Int ) [symbol(word2Bool), function, total]
 // ----------------------------------------------------------------------
    rule word2Bool( W ) => false requires W  ==Int 0
    rule word2Bool( W ) => true  requires W =/=Int 0
```

-   `sgn` gives the twos-complement interpretation of the sign of a word.
-   `abs` gives the twos-complement interpretation of the magnitude of a word.

```k
    syntax Int ::= sgn ( Int ) [symbol(sgn), function, total]
                 | abs ( Int ) [symbol(abs), function, total]
 // ---------------------------------------------------------
    rule sgn(I) => -1 requires pow255 <=Int I andBool I <Int pow256
    rule sgn(I) =>  1 requires 0 <=Int I andBool I <Int pow255
    rule sgn(I) =>  0 requires I <Int 0 orBool pow256 <=Int I

    rule abs(I) => 0 -Word I requires sgn(I) ==Int -1
    rule abs(I) => I         requires sgn(I) ==Int  1
    rule abs(I) => 0         requires sgn(I) ==Int  0
```

Word Operations
---------------

### Low-Level

-   `up/Int` performs integer division but rounds up instead of down.

NOTE: Here, we choose to add `I2 -Int 1` to the numerator before doing the division to mimic the C++ implementation.
You could alternatively calculate `I1 modInt I2`, then add one to the normal integer division afterward depending on the result.

```k
    syntax Int ::= Int "up/Int" Int [function, total, smtlib(upDivInt)]
 // -------------------------------------------------------------------
    rule _I1 up/Int 0  => 0                                                  [concrete]
    rule _I1 up/Int I2 => 0                             requires I2 <=Int 0  [concrete]
    rule  I1 up/Int 1  => I1                                                 [concrete]
    rule  I1 up/Int I2 => (I1 +Int (I2 -Int 1)) /Int I2 requires 1  <Int  I2 [concrete]
```

-   `log256Int` returns the log base 256 (floored) of an integer.

```k
    syntax Int ::= log256Int ( Int ) [symbol(log256Int), function]
 // --------------------------------------------------------------
    rule log256Int(N) => log2Int(N) /Int 8
```

The corresponding `<op>Word` operations automatically perform the correct modulus for EVM words.
Warning: operands are assumed to be within the range of a 256 bit EVM word. Unbound integers may not return the correct result.

```k
    syntax Int ::= Int "+Word" Int [function, total]
                 | Int "*Word" Int [function, total]
                 | Int "-Word" Int [function, total]
                 | Int "/Word" Int [function, total]
                 | Int "%Word" Int [function, total]
 // ------------------------------------------------
    rule W0 +Word W1 => chop( W0 +Int W1 )
    rule W0 -Word W1 => chop( W0 -Int W1 )
    rule W0 *Word W1 => chop( W0 *Int W1 )
    rule  _ /Word W1 => 0            requires W1  ==Int 0
    rule W0 /Word W1 => W0 /Int W1   requires W1 =/=Int 0
    rule  _ %Word W1 => 0            requires W1  ==Int 0
    rule W0 %Word W1 => W0 modInt W1 requires W1 =/=Int 0
```

Care is needed for `^Word` to avoid big exponentiation.
The helper `powmod` is a totalization of the operator `_^%Int__` (which comes with K).
`_^%Int__` is not defined when the modulus (third argument) is zero, but `powmod` is.

```k
    syntax Int ::= Int "^Word" Int       [function, total]
                 | powmod(Int, Int, Int) [symbol(powmod), function, total]
 // ----------------------------------------------------------------------
    rule W0 ^Word W1 => powmod(W0, W1, pow256)

    rule [powmod.nonzero]: powmod(W0, W1, W2) => W0 ^%Int W1 W2  requires W2 =/=Int 0 [concrete]
    rule [powmod.zero]:    powmod( _,  _, W2) => 0               requires W2  ==Int 0 [concrete]
```

`/sWord` and `%sWord` give the signed interpretations of `/Word` and `%Word`.

```k
    syntax Int ::= Int "/sWord" Int [function]
                 | Int "%sWord" Int [function]
 // ------------------------------------------
    rule [divSWord.same]: W0 /sWord W1 =>          abs(W0) /Word abs(W1)  requires sgn(W0) *Int sgn(W1) ==Int  1
    rule [divSWord.diff]: W0 /sWord W1 => 0 -Word (abs(W0) /Word abs(W1)) requires sgn(W0) *Int sgn(W1) ==Int -1
    rule [modSWord.pos]:  W0 %sWord W1 =>          abs(W0) %Word abs(W1)  requires sgn(W0) ==Int  1
    rule [modSWord.neg]:  W0 %sWord W1 => 0 -Word (abs(W0) %Word abs(W1)) requires sgn(W0) ==Int -1
```

### Word Comparison

The `<op>Word` comparisons similarly lift K operators to EVM ones:

```k
    syntax Int ::= Int "<Word"  Int [function, total]
                 | Int ">Word"  Int [function, total]
                 | Int "<=Word" Int [function, total]
                 | Int ">=Word" Int [function, total]
                 | Int "==Word" Int [function, total]
 // -------------------------------------------------
    rule W0 <Word  W1 => bool2Word(W0 <Int  W1)
    rule W0 >Word  W1 => bool2Word(W0 >Int  W1)
    rule W0 <=Word W1 => bool2Word(W0 <=Int W1)
    rule W0 >=Word W1 => bool2Word(W0 >=Int W1)
    rule W0 ==Word W1 => bool2Word(W0 ==Int W1)
```

-   `s<Word` implements a less-than for `Word` (with signed interpretation).

```k
    syntax Int ::= Int "s<Word" Int [function, total]
 // -------------------------------------------------
    rule [s<Word.pp]: W0 s<Word W1 => W0 <Word W1           requires sgn(W0) ==K 1  andBool sgn(W1) ==K 1
    rule [s<Word.pn]: W0 s<Word W1 => bool2Word(false)      requires sgn(W0) ==K 1  andBool sgn(W1) ==K -1
    rule [s<Word.np]: W0 s<Word W1 => bool2Word(true)       requires sgn(W0) ==K -1 andBool sgn(W1) ==K 1
    rule [s<Word.nn]: W0 s<Word W1 => abs(W1) <Word abs(W0) requires sgn(W0) ==K -1 andBool sgn(W1) ==K -1
```

### Bitwise Operators

Bitwise logical operators are lifted from the integer versions.

```k
    syntax Int ::= "~Word" Int       [function, total]
                 | Int "|Word"   Int [function, total]
                 | Int "&Word"   Int [function, total]
                 | Int "xorWord" Int [function, total]
                 | Int "<<Word"  Int [function, total]
                 | Int ">>Word"  Int [function, total]
                 | Int ">>sWord" Int [function, total]
 // --------------------------------------------------
    rule ~Word W       => W xorInt maxUInt256
    rule W0 |Word   W1 => W0 |Int W1
    rule W0 &Word   W1 => W0 &Int W1
    rule W0 xorWord W1 => W0 xorInt W1
    rule W0 <<Word  W1 => chop( W0 <<Int W1 ) requires 0 <=Int W0 andBool 0 <=Int W1 andBool W1 <Int 256
    rule  _ <<Word  _  => 0 [owise]
    rule W0 >>Word  W1 => W0 >>Int W1 requires 0 <=Int W0 andBool 0 <=Int W1
    rule  _ >>Word   _ => 0 [owise]
    rule W0 >>sWord W1 => chop( (abs(W0) *Int sgn(W0)) >>Int W1 ) requires 0 <=Int W0 andBool 0 <=Int W1
    rule  _ >>sWord  _ => 0 [owise]
```

-   `bit` gets bit `N` (0 being MSB).
-   `byte` gets byte `N` (0 being the MSB).

```k
    syntax Int ::= bit  ( Int , Int ) [symbol(bit), function]
                 | byte ( Int , Int ) [symbol(byte), function]
 // ----------------------------------------------------------
    rule bit (N, _) => 0 requires notBool (N >=Int 0 andBool N <Int 256)
    rule byte(N, _) => 0 requires notBool (N >=Int 0 andBool N <Int  32)

    rule bit (N, W) => bitRangeInt(W , (255 -Int N)       , 1) requires N >=Int 0 andBool N <Int 256
    rule byte(N, W) => bitRangeInt(W , 8 *Int (31 -Int N) , 8) requires N >=Int 0 andBool N <Int  32
```

-   `#nBits` shifts in `N` ones from the right.
-   `#nBytes` shifts in `N` bytes of ones from the right.

```k
    syntax Int ::= #nBits  ( Int )  [symbol(#nBits), function]
                 | #nBytes ( Int )  [symbol(#nBytes), function]
 // -----------------------------------------------------------
    rule #nBits(N)  => (1 <<Int N) -Int 1 requires N >=Int 0
    rule #nBytes(N) => #nBits(8 *Int N)   requires N >=Int 0
```

-   `signextend(N, W)` sign-extends from byte `N` of `W` (0 being MSB).

```k
    syntax Int ::= signextend( Int , Int ) [symbol(signextend), function, total]
 // ----------------------------------------------------------------------------
    rule [signextend.invalid]:  signextend(N, W) => W requires N >=Int 32 orBool N <Int 0                                                                                                                      [concrete]
    rule [signextend.negative]: signextend(N, W) => chop( (#nBytes(31 -Int N) <<Byte (N +Int 1)) |Int W ) requires N <Int 32 andBool N >=Int 0 andBool         word2Bool(bit(256 -Int (8 *Int (N +Int 1)), W)) [concrete]
    rule [signextend.positive]: signextend(N, W) => chop( #nBytes(N +Int 1)                      &Int W ) requires N <Int 32 andBool N >=Int 0 andBool notBool word2Bool(bit(256 -Int (8 *Int (N +Int 1)), W)) [concrete]
```


A WordStack for EVM
-------------------

### As a cons-list

A cons-list is used for the EVM wordstack.

-   `.WordStack` serves as the empty worstack, and
-   `_:_` serves as the "cons" operator.

```k
    syntax WordStack ::= ".WordStack"      [smtlib(_dotWS)]
                       | Int ":" WordStack [smtlib(_WS_)]
 // -----------------------------------------------------
```

```k
    syntax Bytes ::= Int ":" Bytes [function]
 // -----------------------------------------
    rule I : BS => Int2Bytes(1, I, BE) +Bytes BS requires I <Int 256
```

-   `#take(N , WS)` takes the first `N` elements of a `WordStack`.
-   `#drop(N , WS)` drops the first `N` elements of a `WordStack`.

```k
    syntax WordStack ::= #take ( Int , WordStack ) [symbol(takeWordStack), function, total]
 // ---------------------------------------------------------------------------------------
 // Expected use cases are from 0-4
    rule [ws-take.0]: #take(0,                      _) => .WordStack
    rule [ws-take.1]: #take(1, W0 :                 _) => W0 : .WordStack
    rule [ws-take.2]: #take(2, W0 : W1 :            _) => W0 : W1 : .WordStack
    rule [ws-take.3]: #take(3, W0 : W1 : W2 :       _) => W0 : W1 : W2 : .WordStack
    rule [ws-take.4]: #take(4, W0 : W1 : W2 : W3 :  _) => W0 : W1 : W2 : W3 : .WordStack
 // For unexpected cases
    rule [ws-take.N]: #take(N,  _ :  _ :  _ :  _ : WS) => #take(N -Int 4, WS) requires 4 <Int N
 // For totality
    rule [ws-take.O]: #take(_, _) => .WordStack [owise]

    syntax WordStack ::= #drop ( Int , WordStack ) [symbol(dropWordStack), function, total]
 // ---------------------------------------------------------------------------------------
 // Expected use cases are from 0-4
    rule [ws-drop.0]: #drop(0,                     WS) => WS
    rule [ws-drop.1]: #drop(1, _ :                 WS) => WS
    rule [ws-drop.2]: #drop(2, _ : _ :             WS) => WS
    rule [ws-drop.3]: #drop(3, _ : _ : _ :         WS) => WS
    rule [ws-drop.4]: #drop(4, _ : _ : _ : _ :     WS) => WS
 // For unexpected cases
    rule [ws-drop.N]: #drop(N, _ : _ : _ : _ : _ : WS) => #drop(N -Int 4, WS) requires 4 <Int N
 // For totality
    rule [ws-drop.O]: #drop(_, _) => .WordStack [owise]
```

### Element Access

-   `WS [ N ]` accesses element `N` of `WS`.
-   `WS [ N := W ]` sets element `N` of `WS` to `W`.

```k
    syntax Int ::= WordStack "[" Int "]" [function, total]
 // ------------------------------------------------------
 // Expected use cases are from 0-31
    rule [ws-get-00]: (                                                            W : _):WordStack [  0 ] => W
    rule [ws-get-01]: (                                                        _ : W : _):WordStack [  1 ] => W
    rule [ws-get-02]: (                                                    _ : _ : W : _):WordStack [  2 ] => W
    rule [ws-get-03]: (                                                _ : _ : _ : W : _):WordStack [  3 ] => W
    rule [ws-get-04]: (                                            _ : _ : _ : _ : W : _):WordStack [  4 ] => W
    rule [ws-get-05]: (                                        _ : _ : _ : _ : _ : W : _):WordStack [  5 ] => W
    rule [ws-get-06]: (                                    _ : _ : _ : _ : _ : _ : W : _):WordStack [  6 ] => W
    rule [ws-get-07]: (                                _ : _ : _ : _ : _ : _ : _ : W : _):WordStack [  7 ] => W
    rule [ws-get-08]: (                            _ : _ : _ : _ : _ : _ : _ : _ : W : _):WordStack [  8 ] => W
    rule [ws-get-09]: (                        _ : _ : _ : _ : _ : _ : _ : _ : _ : W : _):WordStack [  9 ] => W
    rule [ws-get-10]: (                    _ : _ : _ : _ : _ : _ : _ : _ : _ : _ : W : _):WordStack [ 10 ] => W
    rule [ws-get-11]: (                _ : _ : _ : _ : _ : _ : _ : _ : _ : _ : _ : W : _):WordStack [ 11 ] => W
    rule [ws-get-12]: (            _ : _ : _ : _ : _ : _ : _ : _ : _ : _ : _ : _ : W : _):WordStack [ 12 ] => W
    rule [ws-get-13]: (        _ : _ : _ : _ : _ : _ : _ : _ : _ : _ : _ : _ : _ : W : _):WordStack [ 13 ] => W
    rule [ws-get-14]: (    _ : _ : _ : _ : _ : _ : _ : _ : _ : _ : _ : _ : _ : _ : W : _):WordStack [ 14 ] => W
    rule [ws-get-15]: (_ : _ : _ : _ : _ : _ : _ : _ : _ : _ : _ : _ : _ : _ : _ : W : _):WordStack [ 15 ] => W
    rule [ws-get-16]: (_ : _ : _ : _ : _ : _ : _ : _ : _ : _ : _ : _ : _ : _ : _ : _ :
                                                                                   W : _):WordStack [ 16 ] => W
    rule [ws-get-17]: (_ : _ : _ : _ : _ : _ : _ : _ : _ : _ : _ : _ : _ : _ : _ : _ :
                                                                               _ : W : _):WordStack [ 17 ] => W
    rule [ws-get-18]: (_ : _ : _ : _ : _ : _ : _ : _ : _ : _ : _ : _ : _ : _ : _ : _ :
                                                                           _ : _ : W : _):WordStack [ 18 ] => W
    rule [ws-get-19]: (_ : _ : _ : _ : _ : _ : _ : _ : _ : _ : _ : _ : _ : _ : _ : _ :
                                                                       _ : _ : _ : W : _):WordStack [ 19 ] => W
    rule [ws-get-20]: (_ : _ : _ : _ : _ : _ : _ : _ : _ : _ : _ : _ : _ : _ : _ : _ :
                                                                   _ : _ : _ : _ : W : _):WordStack [ 20 ] => W
    rule [ws-get-21]: (_ : _ : _ : _ : _ : _ : _ : _ : _ : _ : _ : _ : _ : _ : _ : _ :
                                                               _ : _ : _ : _ : _ : W : _):WordStack [ 21 ] => W
    rule [ws-get-22]: (_ : _ : _ : _ : _ : _ : _ : _ : _ : _ : _ : _ : _ : _ : _ : _ :
                                                           _ : _ : _ : _ : _ : _ : W : _):WordStack [ 22 ] => W
    rule [ws-get-23]: (_ : _ : _ : _ : _ : _ : _ : _ : _ : _ : _ : _ : _ : _ : _ : _ :
                                                       _ : _ : _ : _ : _ : _ : _ : W : _):WordStack [ 23 ] => W
    rule [ws-get-24]: (_ : _ : _ : _ : _ : _ : _ : _ : _ : _ : _ : _ : _ : _ : _ : _ :
                                                   _ : _ : _ : _ : _ : _ : _ : _ : W : _):WordStack [ 24 ] => W
    rule [ws-get-25]: (_ : _ : _ : _ : _ : _ : _ : _ : _ : _ : _ : _ : _ : _ : _ : _ :
                                               _ : _ : _ : _ : _ : _ : _ : _ : _ : W : _):WordStack [ 25 ] => W
    rule [ws-get-26]: (_ : _ : _ : _ : _ : _ : _ : _ : _ : _ : _ : _ : _ : _ : _ : _ :
                                           _ : _ : _ : _ : _ : _ : _ : _ : _ : _ : W : _):WordStack [ 26 ] => W
    rule [ws-get-27]: (_ : _ : _ : _ : _ : _ : _ : _ : _ : _ : _ : _ : _ : _ : _ : _ :
                                       _ : _ : _ : _ : _ : _ : _ : _ : _ : _ : _ : W : _):WordStack [ 27 ] => W
    rule [ws-get-28]: (_ : _ : _ : _ : _ : _ : _ : _ : _ : _ : _ : _ : _ : _ : _ : _ :
                                   _ : _ : _ : _ : _ : _ : _ : _ : _ : _ : _ : _ : W : _):WordStack [ 28 ] => W
    rule [ws-get-29]: (_ : _ : _ : _ : _ : _ : _ : _ : _ : _ : _ : _ : _ : _ : _ : _ :
                               _ : _ : _ : _ : _ : _ : _ : _ : _ : _ : _ : _ : _ : W : _):WordStack [ 29 ] => W
    rule [ws-get-30]: (_ : _ : _ : _ : _ : _ : _ : _ : _ : _ : _ : _ : _ : _ : _ : _ :
                           _ : _ : _ : _ : _ : _ : _ : _ : _ : _ : _ : _ : _ : _ : W : _):WordStack [ 30 ] => W
    rule [ws-get-31]: (_ : _ : _ : _ : _ : _ : _ : _ : _ : _ : _ : _ : _ : _ : _ : _ :
                       _ : _ : _ : _ : _ : _ : _ : _ : _ : _ : _ : _ : _ : _ : _ : W : _):WordStack [ 31 ] => W
 // For unexpected cases
    rule [ws-get-N]:  (_ : _ : _ : _ : _ : _ : _ : _ : _ : _ : _ : _ : _ : _ : _ : _ :
                       _ : _ : _ : _ : _ : _ : _ : _ : _ : _ : _ : _ : _ : _ : _ : _ : WS):WordStack [ N ] => WS:WordStack [ N -Int 32 ] requires 31 <Int N
 // For totality
    rule [ws-get-O]:  _:WordStack [ _:Int ] => 0 [owise]

    syntax WordStack ::= WordStack "[" Int ":=" Int "]" [function, total]
 // ---------------------------------------------------------------------
 // Expected use cases are from 0-31
    rule [ws-set-00]: (                                                                                            _ : WS):WordStack [  0 := V ] => ( V : WS ):WordStack
    rule [ws-set-01]: (                                                                                     W0 :   _ : WS):WordStack [  1 := V ] => ( W0 :  V : WS):WordStack
    rule [ws-set-02]: (                                                                               W0 :  W1 :   _ : WS):WordStack [  2 := V ] => ( W0 :  W1 :  V : WS):WordStack
    rule [ws-set-03]: (                                                                         W0 :  W1 :  W2 :   _ : WS):WordStack [  3 := V ] => ( W0 :  W1 :  W2 :  V : WS):WordStack
    rule [ws-set-04]: (                                                                   W0 :  W1 :  W2 :  W3 :   _ : WS):WordStack [  4 := V ] => ( W0 :  W1 :  W2 :  W3 :  V : WS):WordStack
    rule [ws-set-05]: (                                                             W0 :  W1 :  W2 :  W3 :  W4 :   _ : WS):WordStack [  5 := V ] => ( W0 :  W1 :  W2 :  W3 :  W4 :  V : WS):WordStack
    rule [ws-set-06]: (                                                       W0 :  W1 :  W2 :  W3 :  W4 :  W5 :   _ : WS):WordStack [  6 := V ] => ( W0 :  W1 :  W2 :  W3 :  W4 :  W5 :  V : WS):WordStack
    rule [ws-set-07]: (                                                 W0 :  W1 :  W2 :  W3 :  W4 :  W5 :  W6 :   _ : WS):WordStack [  7 := V ] => ( W0 :  W1 :  W2 :  W3 :  W4 :  W5 :  W6 :  V : WS):WordStack
    rule [ws-set-08]: (                                           W0 :  W1 :  W2 :  W3 :  W4 :  W5 :  W6 :  W7 :   _ : WS):WordStack [  8 := V ] => ( W0 :  W1 :  W2 :  W3 :  W4 :  W5 :  W6 :  W7 :  V : WS):WordStack
    rule [ws-set-09]: (                                     W0 :  W1 :  W2 :  W3 :  W4 :  W5 :  W6 :  W7 :  W8 :   _ : WS):WordStack [  9 := V ] => ( W0 :  W1 :  W2 :  W3 :  W4 :  W5 :  W6 :  W7 :  W8 : V : WS):WordStack
    rule [ws-set-10]: (                               W0 :  W1 :  W2 :  W3 :  W4 :  W5 :  W6 :  W7 :  W8 :  W9 :   _ : WS):WordStack [ 10 := V ] => ( W0 :  W1 :  W2 :  W3 :  W4 :  W5 :  W6 :  W7 :  W8 :  W9 : V : WS):WordStack
    rule [ws-set-11]: (                         W0 :  W1 :  W2 :  W3 :  W4 :  W5 :  W6 :  W7 :  W8 :  W9 : W10 :   _ : WS):WordStack [ 11 := V ] => ( W0 :  W1 :  W2 :  W3 :  W4 :  W5 :  W6 :  W7 :  W8 :  W9 : W10 : V : WS):WordStack
    rule [ws-set-12]: (                   W0 :  W1 :  W2 :  W3 :  W4 :  W5 :  W6 :  W7 :  W8 :  W9 : W10 : W11 :   _ : WS):WordStack [ 12 := V ] => ( W0 :  W1 :  W2 :  W3 :  W4 :  W5 :  W6 :  W7 :  W8 :  W9 : W10 : W11 : V : WS):WordStack
    rule [ws-set-13]: (             W0 :  W1 :  W2 :  W3 :  W4 :  W5 :  W6 :  W7 :  W8 :  W9 : W10 : W11 : W12 :   _ : WS):WordStack [ 13 := V ] => ( W0 :  W1 :  W2 :  W3 :  W4 :  W5 :  W6 :  W7 :  W8 :  W9 : W10 : W11 : W12 : V : WS):WordStack
    rule [ws-set-14]: (       W0 :  W1 :  W2 :  W3 :  W4 :  W5 :  W6 :  W7 :  W8 :  W9 : W10 : W11 : W12 : W13 :   _ : WS):WordStack [ 14 := V ] => ( W0 :  W1 :  W2 :  W3 :  W4 :  W5 :  W6 :  W7 :  W8 :  W9 : W10 : W11 : W12 : W13 : V : WS):WordStack
    rule [ws-set-15]: ( W0 :  W1 :  W2 :  W3 :  W4 :  W5 :  W6 :  W7 :  W8 :  W9 : W10 : W11 : W12 : W13 : W14 :   _ : WS):WordStack [ 15 := V ] => ( W0 :  W1 :  W2 :  W3 :  W4 :  W5 :  W6 :  W7 :  W8 :  W9 : W10 : W11 : W12 : W13 : W14 : V : WS):WordStack
    rule [ws-set-16]: ( W0 :  W1 :  W2 :  W3 :  W4 :  W5 :  W6 :  W7 :  W8 :  W9 : W10 : W11 : W12 : W13 : W14 : W15 :
                                                                                                                   _ : WS):WordStack [ 16 := V ] => ( W0 :  W1 :  W2 :  W3 :  W4 :  W5 :  W6 :  W7 :  W8 :  W9 : W10 : W11 : W12 : W13 : W14 : W15 : V : WS):WordStack
    rule [ws-set-17]: ( W0 :  W1 :  W2 :  W3 :  W4 :  W5 :  W6 :  W7 :  W8 :  W9 : W10 : W11 : W12 : W13 : W14 : W15 :
                                                                                                           W16 :   _ : WS):WordStack [ 16 := V ] => ( W0 :  W1 :  W2 :  W3 :  W4 :  W5 :  W6 :  W7 :  W8 :  W9 : W10 : W11 : W12 : W13 : W14 : W15 : W16 : V : WS):WordStack
    rule [ws-set-18]: ( W0 :  W1 :  W2 :  W3 :  W4 :  W5 :  W6 :  W7 :  W8 :  W9 : W10 : W11 : W12 : W13 : W14 : W15 :
                                                                                                     W16 : W17 :   _ : WS):WordStack [ 16 := V ] => ( W0 :  W1 :  W2 :  W3 :  W4 :  W5 :  W6 :  W7 :  W8 :  W9 : W10 : W11 : W12 : W13 : W14 : W15 : W16 : W17 : V : WS):WordStack
    rule [ws-set-19]: ( W0 :  W1 :  W2 :  W3 :  W4 :  W5 :  W6 :  W7 :  W8 :  W9 : W10 : W11 : W12 : W13 : W14 : W15 :
                                                                                               W16 : W17 : W18 :   _ : WS):WordStack [ 16 := V ] => ( W0 :  W1 :  W2 :  W3 :  W4 :  W5 :  W6 :  W7 :  W8 :  W9 : W10 : W11 : W12 : W13 : W14 : W15 : W16 : W17 : W18 : V : WS):WordStack
    rule [ws-set-20]: ( W0 :  W1 :  W2 :  W3 :  W4 :  W5 :  W6 :  W7 :  W8 :  W9 : W10 : W11 : W12 : W13 : W14 : W15 :
                                                                                         W16 : W17 : W18 : W19 :   _ : WS):WordStack [ 16 := V ] => ( W0 :  W1 :  W2 :  W3 :  W4 :  W5 :  W6 :  W7 :  W8 :  W9 : W10 : W11 : W12 : W13 : W14 : W15 : W16 : W17 : W18 : W19 : V : WS):WordStack
    rule [ws-set-21]: ( W0 :  W1 :  W2 :  W3 :  W4 :  W5 :  W6 :  W7 :  W8 :  W9 : W10 : W11 : W12 : W13 : W14 : W15 :
                                                                                   W16 : W17 : W18 : W19 : W20 :   _ : WS):WordStack [ 16 := V ] => ( W0 :  W1 :  W2 :  W3 :  W4 :  W5 :  W6 :  W7 :  W8 :  W9 : W10 : W11 : W12 : W13 : W14 : W15 : W16 : W17 : W18 : W19 : W20 : V : WS):WordStack
    rule [ws-set-22]: ( W0 :  W1 :  W2 :  W3 :  W4 :  W5 :  W6 :  W7 :  W8 :  W9 : W10 : W11 : W12 : W13 : W14 : W15 :
                                                                             W16 : W17 : W18 : W19 : W20 : W21 :   _ : WS):WordStack [ 16 := V ] => ( W0 :  W1 :  W2 :  W3 :  W4 :  W5 :  W6 :  W7 :  W8 :  W9 : W10 : W11 : W12 : W13 : W14 : W15 : W16 : W17 : W18 : W19 : W20 : W21 : V : WS):WordStack
    rule [ws-set-23]: ( W0 :  W1 :  W2 :  W3 :  W4 :  W5 :  W6 :  W7 :  W8 :  W9 : W10 : W11 : W12 : W13 : W14 : W15 :
                                                                       W16 : W17 : W18 : W19 : W20 : W21 : W22 :   _ : WS):WordStack [ 16 := V ] => ( W0 :  W1 :  W2 :  W3 :  W4 :  W5 :  W6 :  W7 :  W8 :  W9 : W10 : W11 : W12 : W13 : W14 : W15 : W16 : W17 : W18 : W19 : W20 : W21 : W22 : V : WS):WordStack
    rule [ws-set-24]: ( W0 :  W1 :  W2 :  W3 :  W4 :  W5 :  W6 :  W7 :  W8 :  W9 : W10 : W11 : W12 : W13 : W14 : W15 :
                                                                 W16 : W17 : W18 : W19 : W20 : W21 : W22 : W23 :   _ : WS):WordStack [ 16 := V ] => ( W0 :  W1 :  W2 :  W3 :  W4 :  W5 :  W6 :  W7 :  W8 :  W9 : W10 : W11 : W12 : W13 : W14 : W15 : W16 : W17 : W18 : W19 : W20 : W21 : W22 : W23 : V : WS):WordStack
    rule [ws-set-25]: ( W0 :  W1 :  W2 :  W3 :  W4 :  W5 :  W6 :  W7 :  W8 :  W9 : W10 : W11 : W12 : W13 : W14 : W15 :
                                                           W16 : W17 : W18 : W19 : W20 : W21 : W22 : W23 : W24 :   _ : WS):WordStack [ 16 := V ] => ( W0 :  W1 :  W2 :  W3 :  W4 :  W5 :  W6 :  W7 :  W8 :  W9 : W10 : W11 : W12 : W13 : W14 : W15 : W16 : W17 : W18 : W19 : W20 : W21 : W22 : W23 : W24 : V : WS):WordStack
    rule [ws-set-26]: ( W0 :  W1 :  W2 :  W3 :  W4 :  W5 :  W6 :  W7 :  W8 :  W9 : W10 : W11 : W12 : W13 : W14 : W15 :
                                                     W16 : W17 : W18 : W19 : W20 : W21 : W22 : W23 : W24 : W25 :   _ : WS):WordStack [ 16 := V ] => ( W0 :  W1 :  W2 :  W3 :  W4 :  W5 :  W6 :  W7 :  W8 :  W9 : W10 : W11 : W12 : W13 : W14 : W15 : W16 : W17 : W18 : W19 : W20 : W21 : W22 : W23 : W24 : W25 : V : WS):WordStack
    rule [ws-set-27]: ( W0 :  W1 :  W2 :  W3 :  W4 :  W5 :  W6 :  W7 :  W8 :  W9 : W10 : W11 : W12 : W13 : W14 : W15 :
                                               W16 : W17 : W18 : W19 : W20 : W21 : W22 : W23 : W24 : W25 : W26 :   _ : WS):WordStack [ 16 := V ] => ( W0 :  W1 :  W2 :  W3 :  W4 :  W5 :  W6 :  W7 :  W8 :  W9 : W10 : W11 : W12 : W13 : W14 : W15 : W16 : W17 : W18 : W19 : W20 : W21 : W22 : W23 : W24 : W25 : W26 : V : WS):WordStack
    rule [ws-set-28]: ( W0 :  W1 :  W2 :  W3 :  W4 :  W5 :  W6 :  W7 :  W8 :  W9 : W10 : W11 : W12 : W13 : W14 : W15 :
                                         W16 : W17 : W18 : W19 : W20 : W21 : W22 : W23 : W24 : W25 : W26 : W27 :   _ : WS):WordStack [ 16 := V ] => ( W0 :  W1 :  W2 :  W3 :  W4 :  W5 :  W6 :  W7 :  W8 :  W9 : W10 : W11 : W12 : W13 : W14 : W15 : W16 : W17 : W18 : W19 : W20 : W21 : W22 : W23 : W24 : W25 : W26 : W27 : V : WS):WordStack
    rule [ws-set-29]: ( W0 :  W1 :  W2 :  W3 :  W4 :  W5 :  W6 :  W7 :  W8 :  W9 : W10 : W11 : W12 : W13 : W14 : W15 :
                                   W16 : W17 : W18 : W19 : W20 : W21 : W22 : W23 : W24 : W25 : W26 : W27 : W28 :   _ : WS):WordStack [ 16 := V ] => ( W0 :  W1 :  W2 :  W3 :  W4 :  W5 :  W6 :  W7 :  W8 :  W9 : W10 : W11 : W12 : W13 : W14 : W15 : W16 : W17 : W18 : W19 : W20 : W21 : W22 : W23 : W24 : W25 : W26 : W27 : W28 : V : WS):WordStack
    rule [ws-set-30]: ( W0 :  W1 :  W2 :  W3 :  W4 :  W5 :  W6 :  W7 :  W8 :  W9 : W10 : W11 : W12 : W13 : W14 : W15 :
                             W16 : W17 : W18 : W19 : W20 : W21 : W22 : W23 : W24 : W25 : W26 : W27 : W28 : W29 :   _ : WS):WordStack [ 16 := V ] => ( W0 :  W1 :  W2 :  W3 :  W4 :  W5 :  W6 :  W7 :  W8 :  W9 : W10 : W11 : W12 : W13 : W14 : W15 : W16 : W17 : W18 : W19 : W20 : W21 : W22 : W23 : W24 : W25 : W26 : W27 : W28 : W29 : V : WS):WordStack
    rule [ws-set-31]: ( W0 :  W1 :  W2 :  W3 :  W4 :  W5 :  W6 :  W7 :  W8 :  W9 : W10 : W11 : W12 : W13 : W14 : W15 :
                       W16 : W17 : W18 : W19 : W20 : W21 : W22 : W23 : W24 : W25 : W26 : W27 : W28 : W29 : W30 :   _ : WS):WordStack [ 16 := V ] => ( W0 :  W1 :  W2 :  W3 :  W4 :  W5 :  W6 :  W7 :  W8 :  W9 : W10 : W11 : W12 : W13 : W14 : W15 : W16 : W17 : W18 : W19 : W20 : W21 : W22 : W23 : W24 : W25 : W26 : W27 : W28 : W29 : W30 : V : WS):WordStack
 // For unexpected cases
    rule [ws-set-N]:  ( W0 :  W1 :  W2 :  W3 :  W4 :  W5 :  W6 :  W7 :  W8 :  W9 : W10 : W11 : W12 : W13 : W14 : V15 :
                       W16 : W17 : W18 : W19 : W20 : W21 : W22 : W23 : W24 : W25 : W26 : W27 : W28 : W29 : W30 : V31 : WS):WordStack [ N := V ] =>
                      ( W0 :  W1 :  W2 :  W3 :  W4 :  W5 :  W6 :  W7 :  W8 :  W9 : W10 : W11 : W12 : W13 : W14 : V15 :
                       W16 : W17 : W18 : W19 : W20 : W21 : W22 : W23 : W24 : W25 : W26 : W27 : W28 : W29 : W30 : V31 : (WS [ N -Int 32 := V ] )):WordStack requires 31 <Int N
 // For totality
    rule [ws-set-O]: _:WordStack [ _ := _ ] => .WordStack [owise]
```

-   `#sizeWordStack` calculates the size of a `WordStack`.
-   `_in_` determines if a `Int` occurs in a `WordStack`.

```k
    syntax Int ::= #sizeWordStack ( WordStack ) [symbol(#sizeWordStack), function, total, smtlib(sizeWordStack)]
 // ------------------------------------------------------------------------------------------------------------
    rule [ws-size-00]: #sizeWordStack (.WordStack) => 0
    rule [ws-size-01]: #sizeWordStack (_ : .WordStack) => 1
    rule [ws-size-02]: #sizeWordStack (_ : _ : .WordStack) => 2
    rule [ws-size-03]: #sizeWordStack (_ : _ : _ : .WordStack) => 3
    rule [ws-size-04]: #sizeWordStack (_ : _ : _ : _ : .WordStack) => 4
    rule [ws-size-05]: #sizeWordStack (_ : _ : _ : _ : _ : .WordStack) => 5
    rule [ws-size-06]: #sizeWordStack (_ : _ : _ : _ : _ : _ : .WordStack) => 6
    rule [ws-size-07]: #sizeWordStack (_ : _ : _ : _ : _ : _ : _ : .WordStack) => 7
    rule [ws-size-08]: #sizeWordStack (_ : _ : _ : _ : _ : _ : _ : _ : .WordStack) => 8
    rule [ws-size-09]: #sizeWordStack (_ : _ : _ : _ : _ : _ : _ : _ : _ : .WordStack) => 9
    rule [ws-size-10]: #sizeWordStack (_ : _ : _ : _ : _ : _ : _ : _ : _ : _ : .WordStack) => 10
    rule [ws-size-11]: #sizeWordStack (_ : _ : _ : _ : _ : _ : _ : _ : _ : _ : _ : .WordStack) => 11
    rule [ws-size-12]: #sizeWordStack (_ : _ : _ : _ : _ : _ : _ : _ : _ : _ : _ : _ : .WordStack) => 12
    rule [ws-size-13]: #sizeWordStack (_ : _ : _ : _ : _ : _ : _ : _ : _ : _ : _ : _ : _ : .WordStack) => 13
    rule [ws-size-14]: #sizeWordStack (_ : _ : _ : _ : _ : _ : _ : _ : _ : _ : _ : _ : _ : _ : .WordStack) => 14
    rule [ws-size-15]: #sizeWordStack (_ : _ : _ : _ : _ : _ : _ : _ : _ : _ : _ : _ : _ : _ : _ : .WordStack) => 15
    rule [ws-size-16]: #sizeWordStack (_ : _ : _ : _ : _ : _ : _ : _ : _ : _ : _ : _ : _ : _ : _ : _ : .WordStack) => 16

    rule #sizeWordStack ( _ : WS ) => 1 +Int #sizeWordStack(WS)
```

-   `WordStack2List` converts a term of sort `WordStack` to a term of sort `List`.

```k
    syntax List ::= WordStack2List ( WordStack ) [symbol(WordStack2List), function, total]
 // --------------------------------------------------------------------------------------
    rule WordStack2List(.WordStack) => .List
    rule WordStack2List(W : WS) => ListItem(W) WordStack2List(WS)
```


-   `WS [ START := WS' ]` assigns a contiguous chunk of `WS'` to `WS` starting at position `START`.
-   `#write(WM, IDX, VAL)` assigns a value `VAL` at position `IDX` in `WM`.
-   TODO: remove the first rule for `:=` when [#1844](https://github.com/runtimeverification/evm-semantics/issues/1844) is fixed.

```k
    syntax Bytes ::= "#write" "(" Bytes "," Int "," Int ")" [function]
                   | Bytes "[" Int ":=" Bytes "]" [function, total, symbol(mapWriteRange)]
 // --------------------------------------------------------------------------------------
    rule #write(WM, IDX, VAL) => padRightBytes(WM, IDX +Int 1, 0) [ IDX <- VAL ] [concrete]

    rule WS [ START := WS' ] => WS                                                                            requires 0     <=Int START andBool lengthBytes(WS')  ==Int 0 [concrete]
    rule WS [ START := WS' ] => replaceAtBytes(padRightBytes(WS, START +Int lengthBytes(WS'), 0), START, WS') requires 0     <=Int START andBool lengthBytes(WS') =/=Int 0 [concrete]
    rule _  [ START := _ ]   => .Bytes                                                                        requires START  <Int 0                                       [concrete]
```

Bytes helper functions
----------------------

-   `#asWord` will interpret a stack of bytes as a single word (with MSB first).
-   `#asInteger` will interpret a stack of bytes as a single arbitrary-precision integer (with MSB first).
-   `#asAccount` will interpret a stack of bytes as a single account id (with MSB first).
    Differs from `#asWord` only in that an empty stack represents the empty account, not account zero.
-   `#asByteStack` will split a single word up into a `Bytes`.
-   `#range(WS, N, W)` access the range of `WS` beginning with `N` of width `W`.
-   `#padToWidth(N, WS)` and `#padRightToWidth` make sure that a `Bytes` is the correct size.

```k
    syntax Int ::= #asWord ( Bytes ) [symbol(asWord), function, total, smtlib(asWord)]
 // ----------------------------------------------------------------------------------
    rule #asWord(WS) => chop(Bytes2Int(WS, BE, Unsigned)) [concrete]

    syntax Int ::= #asInteger ( Bytes ) [symbol(#asInteger), function, total]
 // -------------------------------------------------------------------------
    rule #asInteger(WS) => Bytes2Int(WS, BE, Unsigned) [concrete]

    syntax Account ::= #asAccount ( Bytes ) [symbol(#asAccount), function]
 // ----------------------------------------------------------------------
    rule #asAccount(BS) => .Account    requires lengthBytes(BS) ==Int 0
    rule #asAccount(BS) => #asWord(BS) [owise]

    syntax Bytes ::= #asByteStack ( Int ) [symbol(#asByteStack), function, total]
 // -----------------------------------------------------------------------------
    rule #asByteStack(W) => Int2Bytes(W, BE, Unsigned) [concrete]

    syntax Bytes ::= #range ( Bytes , Int , Int ) [symbol(#range), function, total]
 // -------------------------------------------------------------------------------
    rule                #range(_, START, WIDTH)  => .Bytes                                                                       requires notBool (WIDTH >=Int 0 andBool START >=Int 0) [concrete]
    rule [bytesRange] : #range(WS, START, WIDTH) => substrBytes(padRightBytes(WS, START +Int WIDTH, 0), START, START +Int WIDTH) requires WIDTH >=Int 0 andBool START >=Int 0 andBool START <Int lengthBytes(WS) [concrete]
    rule                #range(_, _, WIDTH)      => padRightBytes(.Bytes, WIDTH, 0) [owise, concrete]

    syntax Bytes ::= #padToWidth      ( Int , Bytes ) [symbol(#padToWidth), function, total]
                   | #padRightToWidth ( Int , Bytes ) [symbol(#padRightToWidth), function, total]
 // ---------------------------------------------------------------------------------------------
    rule #padToWidth(N, BS)      =>               BS        requires notBool (0 <=Int N) [concrete]
    rule #padToWidth(N, BS)      =>  padLeftBytes(BS, N, 0) requires          0 <=Int N  [concrete]
    rule #padRightToWidth(N, BS) =>               BS        requires notBool (0 <=Int N) [concrete]
    rule #padRightToWidth(N, BS) => padRightBytes(BS, N, 0) requires          0 <=Int N  [concrete]
```

Accounts
--------

### Empty Account

-   `.Account` represents the case when an account ID is referenced in the yellowpaper, but
    the actual value of the account ID is the empty set. This is used, for example, when
    referring to the destination of a message which creates a new contract.

```k
    syntax Account ::= ".Account" | Int
 // -----------------------------------

    syntax AccountCode ::= Bytes
 // ----------------------------
```

### Addresses

-   `#addr` turns an Ethereum word into the corresponding Ethereum address (160 LSB).

```k
    syntax Int ::= #addr ( Int ) [symbol(#addr), function, total]
 // -------------------------------------------------------------
    rule #addr(W) => W %Word pow160
```

Storage/Memory Lookup
---------------------

`#lookup*` looks up a key in a map and returns 0 if the key doesn't exist, otherwise returning its value.

```k
    syntax Int ::= #lookup        ( Map , Int ) [symbol(lookup), function, total, smtlib(lookup)]
                 | #lookupMemory  ( Map , Int ) [symbol(lookupMemory), function, total, smtlib(lookupMemory)]
 // ---------------------------------------------------------------------------------------------------------
    rule [#lookup.some]:         #lookup(       (KEY |-> VAL:Int) _M, KEY ) => VAL modInt pow256
    rule [#lookup.none]:         #lookup(                          M, KEY ) => 0                 requires notBool KEY in_keys(M)
    //Impossible case, for completeness
    rule [#lookup.notInt]:       #lookup(       (KEY |-> VAL    ) _M, KEY ) => 0                 requires notBool isInt(VAL)

    rule [#lookupMemory.some]:   #lookupMemory( (KEY |-> VAL:Int) _M, KEY ) => VAL modInt 256
    rule [#lookupMemory.none]:   #lookupMemory(                    M, KEY ) => 0                 requires notBool KEY in_keys(M)
    //Impossible case, for completeness
    rule [#lookupMemory.notInt]: #lookupMemory( (KEY |-> VAL    ) _M, KEY ) => 0                 requires notBool isInt(VAL)
```

Substate Log
------------

During execution of a transaction some things are recorded in the substate log (Section 6.1 in YellowPaper).
This is a right cons-list of `SubstateLogEntry` (which contains the account ID along with the specified portions of the `wordStack` and `localMem`).

```k
    syntax SubstateLogEntry ::= "{" Int "|" List "|" Bytes "}" [symbol(logEntry)]
 // -----------------------------------------------------------------------------
```

Transactions
------------

Productions related to transactions

```k
    syntax TxType ::= ".TxType"
                    | "Legacy"
                    | "AccessList"
                    | "DynamicFee"
 // ------------------------------

    syntax Int ::= #dasmTxPrefix ( TxType ) [symbol(#dasmTxPrefix), function]
 // -------------------------------------------------------------------------
    rule #dasmTxPrefix (Legacy)     => 0
    rule #dasmTxPrefix (AccessList) => 1
    rule #dasmTxPrefix (DynamicFee) => 2

    syntax TxType ::= #asmTxPrefix ( Int ) [symbol(#asmTxPrefix), function]
 // -----------------------------------------------------------------------
    rule #asmTxPrefix (0) => Legacy
    rule #asmTxPrefix (1) => AccessList
    rule #asmTxPrefix (2) => DynamicFee

    syntax TxData ::= LegacyTx | AccessListTx | DynamicFeeTx
 // --------------------------------------------------------

    syntax LegacyTx     ::= LegacyTxData       ( nonce: Int,                       gasPrice: Int, gasLimit: Int, to: Account, value: Int, data: Bytes )                                   [symbol(LegacyTxData)]
                          | LegacySignedTxData ( nonce: Int,                       gasPrice: Int, gasLimit: Int, to: Account, value: Int, data: Bytes, networkChainId: Int )              [symbol(LegacySignedTxData)]
    syntax AccessListTx ::= AccessListTxData   ( nonce: Int,                       gasPrice: Int, gasLimit: Int, to: Account, value: Int, data: Bytes, chainId: Int, accessLists: JSONs ) [symbol(AccessListTxData)]
    syntax DynamicFeeTx ::= DynamicFeeTxData   ( nonce: Int, priorityGasFee: Int, maxGasFee: Int, gasLimit: Int, to: Account, value: Int, data: Bytes, chainId: Int, accessLists: JSONs)  [symbol(DynamicFeeTxData)]
 // ----------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------

endmodule
```
