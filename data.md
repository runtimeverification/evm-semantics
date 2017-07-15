EVM Words
=========

EVM uses bounded 256 bit integer words, and sometimes also bytes (8 bit words).
Here we provide the arithmetic of these words, as well as some data-structures over them.
Both are implemented using K's `Int`.

```{.k .rvk}
requires "krypto.k"
```

```{.k .uiuck .rvk}
requires "domains.k"

module EVM-DATA
    imports KRYPTO

    syntax KResult ::= Int
```

Primitives
----------

Primitives provide the basic conversion from K's sorts `Int` and `Bool` to EVM's sort `Word`.

-   `Int` is a subsort of `Word`.
-   `chop` interperets an integer module $2^256$.

```{.k .uiuck .rvk}
    syntax Word ::= Int | chop ( Word ) [function]
 // ----------------------------------------------
    rule chop( W:Int ) => W %Int (2 ^Int 256)
```

-   `bool2Word` interperets a `Bool` as a `Word`.
-   `word2Bool` interperets a `Word` as a `Bool`.

```{.k .uiuck .rvk}
    syntax Word ::= bool2Word ( Bool ) [function]
 // ---------------------------------------------
    rule bool2Word(true)  => 1
    rule bool2Word(false) => 0

    syntax Bool ::= word2Bool ( Word ) [function]
 // ---------------------------------------------
    rule word2Bool( 0 ) => false
    rule word2Bool( W ) => true  requires W =/=K 0
```

-   `#ifWord_#then_#else_#fi` provides a conditional in `Word` expressions.

```{.k .uiuck .rvk}
    syntax Word ::= "#ifWord" Bool "#then" Word "#else" Word "#fi" [function]
 // -------------------------------------------------------------------------
    rule #ifWord true  #then W #else _ #fi => W
    rule #ifWord false #then _ #else W #fi => W
```

-   `sgn` gives the twos-complement interperetation of the sign of a `Word`.
-   `abs` gives the twos-complement interperetation of the magnitude of a `Word`.

```{.k .uiuck .rvk}
    syntax Int ::= sgn ( Word ) [function]
                 | abs ( Word ) [function]
 // --------------------------------------
    rule sgn(I:Int) => -1 requires I >=Int (2 ^Int 255)
    rule sgn(I:Int) => 1  requires I <Int (2 ^Int 255)

    rule abs(I:Int) => 0 -Word I requires sgn(I) ==K -1
    rule abs(I:Int) => I         requires sgn(I) ==K 1
```

### Symbolic Words

-   `#symbolicWord` generates a fresh existentially-bound symbolic word.

Note: Comment out this block (remove the `k` tag) if using RV K.

```{.k .uiuck}
    syntax Word ::= "#symbolicWord" [function]
 // ------------------------------------------
    rule #symbolicWord => ?X:Int
```

Arithmetic
----------

-   `up/Int` performs integer division but rounds up instead of down.

NOTE: Here, we choose to add `I2 -Int 1` to the numerator beforing doing the division to mimic the C++ implementation.
You could alternatively calculate `I1 %Int I2`, then add one to the normal integer division afterward depending on the result.

```{.k .uiuck .rvk}
    syntax Int ::= Int "up/Int" Int [function]
 // ------------------------------------------
    rule I1 up/Int 0  => 0
    rule I1 up/Int 1  => I1
    rule I1 up/Int I2 => (I1 +Int (I2 -Int 1)) /Int I2 requires I2 >Int 1
```

-   `logNInt` returns the log base N (floored) of an integer.

```{.k .uiuck .rvk}
    syntax Int ::= log2Int ( Int ) [function]
 // -----------------------------------------
    rule log2Int(1)     => 0
    rule log2Int(W:Int) => 1 +Int log2Int(W >>Int 1) requires W >Int 1

    syntax Int ::= log256Int ( Int ) [function]
 // -------------------------------------------
    rule log256Int(N:Int) => log2Int(N) /Int 8
```

The corresponding `<op>Word` operations automatically perform the correct `Word` modulus.

```{.k .uiuck .rvk}
    syntax Word ::= Word "+Word" Word [function]
                  | Word "*Word" Word [function]
                  | Word "-Word" Word [function]
                  | Word "/Word" Word [function]
                  | Word "%Word" Word [function]
 // --------------------------------------------
    rule W0:Int +Word W1:Int => chop( W0 +Int W1 )
    rule W0:Int -Word W1:Int => chop( (W0 +Int (2 ^Int 256)) -Int W1 )
    rule W0:Int *Word W1:Int => chop( W0 *Int W1 )
    rule W0:Int /Word 0      => 0
    rule W0:Int /Word W1:Int => chop( W0 /Int W1 ) requires W1 =/=K 0
    rule W0:Int %Word 0      => 0
    rule W0:Int %Word W1:Int => chop( W0 %Int W1 ) requires W1 =/=K 0
```

Care is needed for `^Word` to avoid big exponentiation.

```{.k .uiuck .rvk}
    syntax Word ::= Word "^Word" Word [function]
 // --------------------------------------------
    rule W0:Int ^Word W1:Int => (W0 ^Word (W1 /Int 2)) ^Word 2  requires W1 >=Int (2 ^Int 16) andBool W1 %Int 2 ==Int 0
    rule W0:Int ^Word W1:Int => (W0 ^Word (W1 -Int 1)) *Word W0 requires W1 >=Int (2 ^Int 16) andBool W1 %Int 2 ==Int 1
    rule W0:Int ^Word W1:Int => chop( W0 ^Int W1 )              requires W1 <Int (2 ^Int 16)
```

`/sWord` and `%sWord` give the signed interperetations of `/Word` and `%Word`.

```{.k .uiuck .rvk}
    syntax Word ::= Word "/sWord" Word [function]
                  | Word "%sWord" Word [function]
 // ---------------------------------------------
    rule W0:Int /sWord W1:Int => #sgnInterp(sgn(W0) *Int sgn(W1) , abs(W0) /Word abs(W1))
    rule W0:Int %sWord W1:Int => #sgnInterp(sgn(W0)              , abs(W0) %Word abs(W1))

    syntax Word ::= #sgnInterp ( Word , Word ) [function]
 // -----------------------------------------------------
    rule #sgnInterp( 0  , W1 ) => 0
    rule #sgnInterp( W0 , W1 ) => W1         requires W0 >Int 0
    rule #sgnInterp( W0 , W1 ) => 0 -Word W1 requires W0 <Int 0
```

Comparison Operators
--------------------

The `<op>Word` comparison operators automatically interperet the `Bool` as a `Word`.

```{.k .uiuck .rvk}
    syntax Word ::= Word "<Word"  Word [function]
                  | Word ">Word"  Word [function]
                  | Word "<=Word" Word [function]
                  | Word ">=Word" Word [function]
                  | Word "==Word" Word [function]
 // ---------------------------------------------
    rule W0:Int <Word  W1:Int => 1 requires W0 <Int   W1
    rule W0:Int <Word  W1:Int => 0 requires W0 >=Int  W1
    rule W0:Int >Word  W1:Int => 1 requires W0 >Int   W1
    rule W0:Int >Word  W1:Int => 0 requires W0 <=Int  W1
    rule W0:Int <=Word W1:Int => 1 requires W0 <=Int  W1
    rule W0:Int <=Word W1:Int => 0 requires W0 >Int   W1
    rule W0:Int >=Word W1:Int => 1 requires W0 >=Int  W1
    rule W0:Int >=Word W1:Int => 0 requires W0 <Int   W1
    rule W0:Int ==Word W1:Int => 1 requires W0 ==Int  W1
    rule W0:Int ==Word W1:Int => 0 requires W0 =/=Int W1
```

-   `s<Word` implements a less-than for `Word` (with signed interperetation).

```{.k .uiuck .rvk}
    syntax Word ::= Word "s<Word" Word [function]
 // ---------------------------------------------
    rule W0:Int s<Word W1:Int => W0 <Word W1           requires sgn(W0) ==K 1  andBool sgn(W1) ==K 1
    rule W0:Int s<Word W1:Int => bool2Word(false)      requires sgn(W0) ==K 1  andBool sgn(W1) ==K -1
    rule W0:Int s<Word W1:Int => bool2Word(true)       requires sgn(W0) ==K -1 andBool sgn(W1) ==K 1
    rule W0:Int s<Word W1:Int => abs(W1) <Word abs(W0) requires sgn(W0) ==K -1 andBool sgn(W1) ==K -1
```

Bitwise Operators
-----------------

Bitwise logical operators are lifted from the integer versions.

```{.k .uiuck .rvk}
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

-   `bit` gets bit $N$ (0 being MSB).
-   `byte` gets byte $N$ (0 being the MSB).

```{.k .uiuck .rvk}
    syntax Word ::= bit  ( Word , Word ) [function]
                  | byte ( Word , Word ) [function]
 // -----------------------------------------------
    rule bit(N:Int, _)  => 0 requires N <Int 0 orBool N >=Int 256
    rule byte(N:Int, _) => 0 requires N <Int 0 orBool N >=Int 32

    rule bit(N:Int, W:Int)  => (W >>Int (255 -Int N)) %Int 2                            requires N >=Int 0 andBool N <Int 256
    rule byte(N:Int, W:Int) => (W >>Int (256 -Int (8 *Int (N +Int 1)))) %Int (2 ^Int 8) requires N >=Int 0 andBool N <Int 32
```

-   `#nBits` shifts in $N$ ones from the right.
-   `#nBytes` shifts in $N$ bytes of ones from the right.
-   `_<<Byte_` shifts an integer 8 bits to the left.

```{.k .uiuck .rvk}
    syntax Int  ::= #nBits  ( Int )  [function]
                  | #nBytes ( Int )  [function]
                  | Int "<<Byte" Int [function]
 // -------------------------------------------
    rule #nBits(N)  => (2 ^Int N) -Int 1  requires N >=Int 0
    rule #nBytes(N) => #nBits(N *Int 8)   requires N >=Int 0
    rule N <<Byte M => N <<Int (8 *Int M)
```

-   `signextend(N, W)` sign-extends from byte $N$ of $W$ (0 being MSB).

```{.k .uiuck .rvk}
    syntax Word ::= signextend( Word , Word ) [function]
 // ----------------------------------------------------
    rule signextend(N:Int, W:Int) => W requires N >=Int 32 orBool N <Int 0
    rule signextend(N:Int, W:Int) => chop( (#nBytes(31 -Int N) <<Byte (N +Int 1)) |Int W ) requires N <Int 32 andBool N >=Int 0 andBool         word2Bool(bit(256 -Int (8 *Int (N +Int 1)), W))
    rule signextend(N:Int, W:Int) => chop( #nBytes(N +Int 1)                      &Int W ) requires N <Int 32 andBool N >=Int 0 andBool notBool word2Bool(bit(256 -Int (8 *Int (N +Int 1)), W))
```

-   `keccak` serves as a wrapper around the `Keccak256` in `KRYPTO`.

```{.k .uiuck .rvk}
    syntax Word ::= keccak ( WordStack ) [function]
 // -----------------------------------------------
    rule keccak(WS) => #parseHexWord(Keccak256(#unparseByteStack(WS)))
```

Data Structures
===============

Several data-structures and operations over `Word` are useful to have around.

Word Stack
----------

EVM is a stack machine, and so needs a stack of words to operate on.
The stack and some standard operations over it are provided here.
This stack also serves as a cons-list, so we provide some standard cons-list manipulation tools.

```{.k .uiuck .rvk}
    syntax WordStack ::= ".WordStack" | Word ":" WordStack
 // ------------------------------------------------------
```

-   `_++_` acts as `WordStack` append.
-   `#take( N , WS)` keeps the first $N$ elements of a `WordStack` (passing with zeros as needed).
-   `#drop( N , WS)` removes the first $N$ elements of a `WordStack`.

```{.k .uiuck .rvk}
    syntax WordStack ::= WordStack "++" WordStack [function]
 // --------------------------------------------------------
    rule .WordStack ++ WS' => WS'
    rule (W : WS)   ++ WS' => W : (WS ++ WS')

    syntax WordStack ::= #take ( Int , WordStack ) [function]
 // ---------------------------------------------------------
    rule #take(0, WS)         => .WordStack
    rule #take(N, .WordStack) => 0 : #take(N -Int 1, .WordStack) requires N >Int 0
    rule #take(N, (W : WS))   => W : #take(N -Int 1, WS)         requires N >Int 0

    syntax WordStack ::= #drop ( Int , WordStack ) [function]
 // ---------------------------------------------------------
    rule #drop(0, WS)         => WS
    rule #drop(N, .WordStack) => .WordStack
    rule #drop(N, (W : WS))   => #drop(N -Int 1, WS) requires N >Int 0
```

-   `WS [ N ]` accesses element $N$ of $WS$.
-   `WS [ N := W ]` sets element $N$ of $WS$ to $W$ (padding with zeros as needed).

```{.k .uiuck .rvk}
    syntax Word ::= WordStack "[" Int "]" [function]
 // ------------------------------------------------
    rule (W0 : WS)   [0] => W0
    rule (.WordStack)[N] => 0            requires N >Int 0
    rule (W0 : WS)   [N] => WS[N -Int 1] requires N >Int 0

    syntax WordStack ::= WordStack "[" Int ":=" Word "]" [function]
 // ---------------------------------------------------------------
    rule (W0 : WS)  [ 0 := W ] => W  : WS
    rule .WordStack [ N := W ] => 0  : (.WordStack [ N -Int 1 := W ]) requires N >Int 0
    rule (W0 : WS)  [ N := W ] => W0 : (WS [ N -Int 1 := W ])         requires N >Int 0

    syntax WordStack ::= WordStack "[" Int ".." Int "]" [function]
 // --------------------------------------------------------------
    rule WS [ START .. WIDTH ] => #take(WIDTH, #drop(START, WS))
```

-   `#sizeWordStack` calculates the size of a `WordStack`.
-   `_in_` determines if a `Word` occurs in a `WordStack`.

```{.k .uiuck .rvk}
    syntax Int ::= #sizeWordStack ( WordStack ) [function]
 // ------------------------------------------------------
    rule #sizeWordStack ( .WordStack ) => 0
    rule #sizeWordStack ( W : WS )     => 1 +Int #sizeWordStack(WS)

    syntax Bool ::= Word "in" WordStack [function]
 // ----------------------------------------------
    rule W in .WordStack => false
    rule W in (W' : WS)  => (W ==K W') orElseBool (W in WS)
```

-   `#padToWidth(N, WS)` makes sure that a `WordStack` is the correct size.

```{.k .uiuck .rvk}
    syntax WordStack ::= #padToWidth ( Int , WordStack ) [function]
 // ---------------------------------------------------------------
    rule #padToWidth(N, WS) => WS                     requires notBool #sizeWordStack(WS) <Int N
    rule #padToWidth(N, WS) => #padToWidth(N, 0 : WS) requires #sizeWordStack(WS) <Int N
```

Byte Arrays
-----------

The local memory of execution is a byte-array (instead of a word-array).

-   `#asWord` will interperet a stack of bytes as a single word (with MSB first).
-   `#asByteStack` will split a single word up into a `WordStack` where each word is a byte wide.

```{.k .uiuck .rvk}
    syntax Word ::= #asWord ( WordStack ) [function]
 // ------------------------------------------------
    rule #asWord( .WordStack )    => 0
    rule #asWord( W : .WordStack) => W
    rule #asWord( W0 : W1 : WS )  => #asWord(((W0 *Word 256) +Word W1) : WS)

    syntax WordStack ::= #asByteStack ( Word )             [function]
                       | #asByteStack ( Word , WordStack ) [function, klabel(#asByteStackAux)]
 // ------------------------------------------------------------------------------------------
    rule #asByteStack( W ) => #asByteStack( W , .WordStack )
    rule #asByteStack( 0 , WS ) => WS
    rule #asByteStack( W , WS ) => #asByteStack( W /Int 256 , W %Int 256 : WS ) requires W =/=K 0
```

Addresses
---------

-   `#addr` turns an Ethereum word into the corresponding Ethereum address (160 LSB).

```{.k .uiuck .rvk}
    syntax Word ::= #addr ( Word ) [function]
 // -----------------------------------------
    rule #addr(W) => W %Word (2 ^Word 160)
```

-   `#newAddr` computes the address of a new account given the address and nonce of the creating account.

```{.k .uiuck .rvk}
    syntax Word ::= #newAddr ( Word , Word ) [function]
 // ---------------------------------------------------
    rule #newAddr(ACCT, NONCE) => #addr(#parseHexWord(Keccak256(#rlpEncodeLength(#rlpEncodeWord(ACCT) +String #rlpEncodeWord(NONCE), 192))))

    syntax String ::= #rlpEncodeLength ( String , Int )          [function]
                    | #rlpEncodeLength ( String , Int , String ) [function, klabel(#rlpEncodeLengthAux)]
                    | #rlpEncodeWord ( Word )                    [function]
 // -----------------------------------------------------------------------
    rule #rlpEncodeWord(0) => "\x80"
    rule #rlpEncodeWord(WORD) => chrChar(WORD) requires WORD >Int 0 andBool WORD <Int 128
    rule #rlpEncodeWord(WORD) => #rlpEncodeLength(#unparseByteStack(#asByteStack(WORD)), 128) requires WORD >=Int 128
    rule #rlpEncodeLength(STR, OFFSET) => chrChar(lengthString(STR) +Int OFFSET) +String STR requires lengthString(STR) <Int 56
    rule #rlpEncodeLength(STR, OFFSET) => #rlpEncodeLength(STR, OFFSET, #unparseByteStack(#asByteStack(lengthString(STR)))) requires lengthString(STR) >=Int 56
    rule #rlpEncodeLength(STR, OFFSET, BL) => chrChar(lengthString(BL) +Int OFFSET +Int 55) +String BL +String STR
```

Word Map
--------

Most of EVM data is held in finite maps.
We are using the polymorphic `Map` sort for these word maps.

-   `WM [ N := WS ]` assigns a contiguous chunk of $WM$ to $WS$ starting at position $W$.
-   `#asMapWordStack` converts a `WordStack` to a `Map`.
-   `#range(M, START, WIDTH)` reads off $WIDTH$ elements from $WM$ beginning at position $START$ (padding with zeros as needed).

```{.k .uiuck .rvk}
    syntax Map ::= Map "[" Word ":=" WordStack "]" [function]
 // ---------------------------------------------------------
    rule WM[ N := .WordStack ] => WM
    rule WM[ N := W : WS     ] => (WM[N <- W])[N +Word 1 := WS]

    syntax Map ::= #asMapWordStack ( WordStack ) [function]
 // -------------------------------------------------------
    rule #asMapWordStack(WS:WordStack) => .Map [ 0 := WS ]

    syntax WordStack ::= #range ( Map , Word , Word )            [function]
    syntax WordStack ::= #range ( Map , Word , Word , WordStack) [function, klabel(#rangeAux)]
 // ------------------------------------------------------------------------------------------
    rule #range(WM, START:Int, WIDTH:Int) => #range(WM, START +Int WIDTH -Int 1, WIDTH, .WordStack)

    rule #range(WM,           END,     0,         WS) => WS
    rule #range(WM,           END:Int, WIDTH:Int, WS) => #range(WM, END -Int 1, WIDTH -Int 1, 0 : WS) requires (WIDTH >Int 0) andBool notBool END in_keys(WM)
    rule #range(END |-> W WM, END:Int, WIDTH:Int, WS) => #range(WM, END -Int 1, WIDTH -Int 1, W : WS) requires (WIDTH >Int 0)
```

Parsing/Unparsing
=================

The EVM test-sets are represented in JSON format with hex-encoding of the data and programs.
Here we provide some standard parser/unparser functions for that format.

JSON
----

Writing a JSON parser in K takes 6 lines.

```{.k .uiuck .rvk}
    syntax JSONList ::= List{JSON,","}
    syntax JSONKey  ::= String | Word
    syntax JSON     ::= String
                      | JSONKey ":" JSON
                      | "{" JSONList "}"
                      | "[" JSONList "]"
 // ------------------------------------
```

Parsing
-------

These parsers can interperet hex-encoded strings as `Word`s, `WordStack`s, and `Map`s.

-   `#parseHexWord` interperets a string as a single hex-encoded `Word`.
-   `#parseHexBytes` interperets a string as a stack of bytes.
-   `#parseByteStack` interperets a string as a stack of bytes, but makes sure to remove the leading "0x".
-   `#parseWordStack` interperets a JSON list as a stack of `Word`.
-   `#parseMap` interperets a JSON key/value object as a map from `Word` to `Word`.
-   `#parseAddr` interperets a string as a 160 bit hex-endcoded address.

```{.k .uiuck .rvk}
    syntax Word ::= #parseHexWord ( String ) [function]
                  | #parseWord    ( String ) [function]
 // ---------------------------------------------------
    rule #parseHexWord("")   => 0
    rule #parseHexWord("0x") => 0
    rule #parseHexWord(S)    => String2Base(replaceAll(S, "0x", ""), 16) requires (S =/=String "") andBool (S =/=String "0x")

    rule #parseWord("") => 0
    rule #parseWord(S)  => #parseHexWord(S) requires lengthString(S) >=Int 2 andBool substrString(S, 0, 2) ==String "0x"
    rule #parseWord(S)  => String2Int(S) [owise]

    syntax WordStack ::= #parseHexBytes  ( String ) [function]
                       | #parseByteStack ( String ) [function]
 // ----------------------------------------------------------
    rule #parseByteStack(S) => #parseHexBytes(replaceAll(S, "0x", ""))
    rule #parseHexBytes("") => .WordStack
    rule #parseHexBytes(S)  => #parseHexWord(substrString(S, 0, 2)) : #parseHexBytes(substrString(S, 2, lengthString(S))) requires lengthString(S) >=Int 2

    syntax WordStack ::= #parseWordStack ( JSON ) [function]
 // --------------------------------------------------------
    rule #parseWordStack( [ .JSONList ] )            => .WordStack
    rule #parseWordStack( [ (WORD:String) , REST ] ) => #parseHexWord(WORD) : #parseWordStack( [ REST ] )

    syntax Map ::= #parseMap ( JSON ) [function]
 // --------------------------------------------
    rule #parseMap( { .JSONList                   } ) => .Map
    rule #parseMap( { _   : (VALUE:String) , REST } ) => #parseMap({ REST })                                                requires #parseHexWord(VALUE) ==K 0
    rule #parseMap( { KEY : (VALUE:String) , REST } ) => #parseMap({ REST }) [ #parseHexWord(KEY) <- #parseHexWord(VALUE) ] requires #parseHexWord(VALUE) =/=K 0

    syntax Word ::= #parseAddr ( String ) [function]
 // ------------------------------------------------
    rule #parseAddr(S) => #addr(#parseHexWord(S))
```

Unparsing
---------

We need to interperet a `WordStack` as a `String` again so that we can call `Keccak256` on it from `KRYPTO`.

-   `#unparseByteStack` turns a stack of bytes (as a `WordStack`) into a `String`.
-   `#padByte` ensures that the `String` interperetation of a `Word` is wide enough.

```{.k .uiuck .rvk}
    syntax String ::= #unparseByteStack ( WordStack ) [function]
 // ------------------------------------------------------------
    rule #unparseByteStack( .WordStack )   => ""
    rule #unparseByteStack( (W:Int) : WS ) => chrChar(W %Int (2 ^Int 8)) +String #unparseByteStack(WS)

    syntax String ::= #padByte( String ) [function]
 // -----------------------------------------------
    rule #padByte( S ) => S             requires lengthString(S) ==K 2
    rule #padByte( S ) => "0" +String S requires lengthString(S) ==K 1
endmodule
```
