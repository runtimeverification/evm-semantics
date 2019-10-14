EVM Words
=========

### Module `EVM-DATA`

EVM uses bounded 256 bit integer words, and sometimes also bytes (8 bit words).
Here we provide the arithmetic of these words, as well as some data-structures over them.
Both are implemented using K's `Int`.

```k
requires "krypto.k"

module EVM-DATA
    imports KRYPTO
    imports STRING-BUFFER
    imports MAP-SYMBOLIC
    imports COLLECTIONS
```

```{.k .concrete}
    imports BYTES
```

### JSON Formatting

The JSON format is used extensively for communication in the Ethereum circles.
Writing a JSON-ish parser in K takes 6 lines.

```k
    syntax JSONList ::= List{JSON,","}
    syntax JSONKey  ::= String | Int
    syntax JSON     ::= String | Int | Bool
                      | JSONKey ":" JSON
                      | "{" JSONList "}"
                      | "[" JSONList "]"
 // ------------------------------------
```

Utilities
---------

### Important Powers

Some important numbers that are referred to often during execution.
These can be used for pattern-matching on the LHS of rules as well (`macro` attribute expands all occurances of these in rules).

```k
    syntax Int ::= "pow256" /* 2 ^Int 256 */
                 | "pow255" /* 2 ^Int 255 */
                 | "pow160" /* 2 ^Int 160 */
                 | "pow16"  /* 2 ^Int 16  */
 // ----------------------------------------
    rule pow256 => 115792089237316195423570985008687907853269984665640564039457584007913129639936 [macro]
    rule pow255 => 57896044618658097711785492504343953926634992332820282019728792003956564819968  [macro]
    rule pow160 => 1461501637330902918203684832716283019655932542976 [macro]
    rule pow16  => 65536 [macro]

    syntax Int ::= "minSInt128"
                 | "maxSInt128"
                 | "minUInt8"
                 | "maxUInt8"
                 | "minUInt16"
                 | "maxUInt16"
                 | "minUInt48"
                 | "maxUInt48"
                 | "minUInt128"
                 | "maxUInt128"
                 | "minUInt160"
                 | "maxUInt160"
                 | "minSInt256"
                 | "maxSInt256"
                 | "minUInt256"
                 | "maxUInt256"
                 | "minSFixed128x10"
                 | "maxSFixed128x10"
                 | "minUFixed128x10"
                 | "maxUFixed128x10"
 // --------------------------------
    rule minSInt128      => -170141183460469231731687303715884105728                                        [macro]  /*  -2^127      */
    rule maxSInt128      =>  170141183460469231731687303715884105727                                        [macro]  /*   2^127 - 1  */
    rule minSFixed128x10 => -1701411834604692317316873037158841057280000000000                              [macro]  /* (-2^127    ) * 10^10 */
    rule maxSFixed128x10 =>  1701411834604692317316873037158841057270000000000                              [macro]  /* ( 2^127 - 1) * 10^10 */
    rule minSInt256      => -57896044618658097711785492504343953926634992332820282019728792003956564819968  [macro]  /*  -2^255      */
    rule maxSInt256      =>  57896044618658097711785492504343953926634992332820282019728792003956564819967  [macro]  /*   2^255 - 1  */

    rule minUInt8        =>  0                                                                              [macro]
    rule maxUInt8        =>  255                                                                            [macro]
    rule minUInt16       =>  0                                                                              [macro]
    rule maxUInt16       =>  65535                                                                          [macro]  /*   2^16 -  1  */
    rule minUInt48       =>  0                                                                              [macro]
    rule maxUInt48       =>  281474976710655                                                                [macro]  /*   2^48 -  1  */
    rule minUInt128      =>  0                                                                              [macro]
    rule maxUInt128      =>  340282366920938463463374607431768211455                                        [macro]  /*   2^128 - 1  */
    rule minUFixed128x10 =>  0                                                                              [macro]
    rule maxUFixed128x10 =>  3402823669209384634633746074317682114550000000000                              [macro]  /* ( 2^128 - 1) * 10^10 */
    rule minUInt160      =>  0                                                                              [macro]
    rule maxUInt160      =>  1461501637330902918203684832716283019655932542975                              [macro]  /*   2^160 - 1  */
    rule minUInt256      =>  0                                                                              [macro]
    rule maxUInt256      =>  115792089237316195423570985008687907853269984665640564039457584007913129639935 [macro]  /*   2^256 - 1  */

    syntax Int ::= "eth"
 // --------------------
    rule eth => 1000000000000000000 [macro]
```

-   Range of types

```k
    syntax Bool ::= #rangeSInt    ( Int , Int )
                  | #rangeUInt    ( Int , Int )
                  | #rangeSFixed  ( Int , Int , Int )
                  | #rangeUFixed  ( Int , Int , Int )
                  | #rangeAddress ( Int )
                  | #rangeBytes   ( Int , Int )
 // -------------------------------------------
    rule #rangeSInt    ( 128 ,      X ) => #range ( minSInt128      <= X <= maxSInt128      ) [macro]
    rule #rangeSInt    ( 256 ,      X ) => #range ( minSInt256      <= X <= maxSInt256      ) [macro]
    rule #rangeUInt    (   8 ,      X ) => #range ( minUInt8        <= X <= maxUInt8        ) [macro]
    rule #rangeUInt    (  16 ,      X ) => #range ( minUInt16       <= X <= maxUInt16       ) [macro]
    rule #rangeUInt    (  48 ,      X ) => #range ( minUInt48       <= X <= maxUInt48       ) [macro]
    rule #rangeUInt    ( 128 ,      X ) => #range ( minUInt128      <= X <= maxUInt128      ) [macro]
    rule #rangeUInt    ( 256 ,      X ) => #range ( minUInt256      <= X <= maxUInt256      ) [macro]
    rule #rangeSFixed  ( 128 , 10 , X ) => #range ( minSFixed128x10 <= X <= maxSFixed128x10 ) [macro]
    rule #rangeUFixed  ( 128 , 10 , X ) => #range ( minUFixed128x10 <= X <= maxUFixed128x10 ) [macro]
    rule #rangeAddress (            X ) => #range ( minUInt160      <= X <= maxUInt160      ) [macro]
    rule #rangeBytes   (   N ,      X ) => #range ( 0               <= X <= #nBytes(N)      ) [macro]

    syntax Bool ::= "#range" "(" Int "<"  Int "<"  Int ")"
                  | "#range" "(" Int "<"  Int "<=" Int ")"
                  | "#range" "(" Int "<=" Int "<"  Int ")"
                  | "#range" "(" Int "<=" Int "<=" Int ")"
 // ------------------------------------------------------
    rule #range ( LB <  X <  UB ) => LB  <Int X andBool X  <Int UB [macro]
    rule #range ( LB <  X <= UB ) => LB  <Int X andBool X <=Int UB [macro]
    rule #range ( LB <= X <  UB ) => LB <=Int X andBool X  <Int UB [macro]
    rule #range ( LB <= X <= UB ) => LB <=Int X andBool X <=Int UB [macro]
```

-   `chop` interprets an integer modulo $2^256$.

```k
    syntax Int ::= chop ( Int ) [function, functional, smtlib(chop)]
 // ----------------------------------------------------------------
    rule chop ( I:Int ) => I modInt pow256 [concrete, smt-lemma]
```

### Boolean Conversions

Primitives provide the basic conversion from K's sorts `Int` and `Bool` to EVM's words.

-   `bool2Word` interprets a `Bool` as a `Int`.
-   `word2Bool` interprets a `Int` as a `Bool`.

```k
    syntax Int ::= bool2Word ( Bool ) [function, functional]
 // --------------------------------------------------------
    rule bool2Word( B:Bool ) => 1 requires B
    rule bool2Word( B:Bool ) => 0 requires notBool B

    syntax Bool ::= word2Bool ( Int ) [function, functional]
 // --------------------------------------------------------
    rule word2Bool( W ) => false requires W  ==Int 0
    rule word2Bool( W ) => true  requires W =/=Int 0
```

-   `sgn` gives the twos-complement interperetation of the sign of a word.
-   `abs` gives the twos-complement interperetation of the magnitude of a word.

```k
    syntax Int ::= sgn ( Int ) [function, functional]
                 | abs ( Int ) [function, functional]
 // -------------------------------------------------
    rule sgn(I) => -1 requires I >=Int pow255
    rule sgn(I) => 1  requires I <Int pow255

    rule abs(I) => 0 -Word I requires sgn(I) ==Int -1
    rule abs(I) => I         requires sgn(I) ==Int 1
```

-   #signed : uInt256 -> sInt256  (i.e., [minUInt256..maxUInt256] -> [minSInt256..maxSInt256])
- #unsigned : sInt256 -> uInt256  (i.e., [minSInt256..maxSInt256] -> [minUInt256..maxUInt256])

```k
    syntax Int ::= #signed ( Int ) [function]
 // -----------------------------------------
    rule #signed(DATA) => DATA
      requires 0 <=Int DATA andBool DATA <=Int maxSInt256 [concrete]

    rule #signed(DATA) => DATA -Int pow256
      requires maxSInt256 <Int DATA andBool DATA <=Int maxUInt256 [concrete]

    syntax Int ::= #unsigned ( Int ) [function]
 // -------------------------------------------
    rule #unsigned(DATA) => DATA
      requires 0 <=Int DATA andBool DATA <=Int maxSInt256 [concrete]

    rule #unsigned(DATA) => pow256 +Int DATA
      requires minSInt256 <=Int DATA andBool DATA <Int 0 [concrete]
```

### Empty Account

-   `.Account` represents the case when an account ID is referenced in the yellowpaper, but
    the actual value of the account ID is the empty set. This is used, for example, when
    referring to the destination of a message which creates a new contract.

```k
    syntax Account ::= ".Account" | Int
 // -----------------------------------
```

Word Operations
---------------

### Low-Level

-   `up/Int` performs integer division but rounds up instead of down.

NOTE: Here, we choose to add `I2 -Int 1` to the numerator beforing doing the division to mimic the C++ implementation.
You could alternatively calculate `I1 modInt I2`, then add one to the normal integer division afterward depending on the result.

```k
    syntax Int ::= Int "up/Int" Int [function]
 // ------------------------------------------
    rule I1 up/Int 0  => 0
    rule I1 up/Int 1  => I1
    rule I1 up/Int I2 => (I1 +Int (I2 -Int 1)) /Int I2 requires I2 >Int 1
```

-   `log256Int` returns the log base 256 (floored) of an integer.

```k
    syntax Int ::= log256Int ( Int ) [function]
 // -------------------------------------------
    rule log256Int(N) => log2Int(N) /Int 8
```

The corresponding `<op>Word` operations automatically perform the correct modulus for EVM words.
Warning: operands are assumed to be within the range of a 256 bit EVM word. Unbound integers may not return the correct result.

```k
    syntax Int ::= Int "+Word" Int [function, functional]
                 | Int "*Word" Int [function, functional]
                 | Int "-Word" Int [function, functional]
                 | Int "/Word" Int [function, functional]
                 | Int "%Word" Int [function, functional]
 // -----------------------------------------------------
    rule W0 +Word W1 => chop( W0 +Int W1 )
    rule W0 -Word W1 => W0 -Int W1 requires W0 >=Int W1
    rule W0 -Word W1 => chop( (W0 +Int pow256) -Int W1 ) requires W0 <Int W1
    rule W0 *Word W1 => chop( W0 *Int W1 )
    rule W0 /Word W1 => 0            requires W1  ==Int 0
    rule W0 /Word W1 => W0 /Int W1   requires W1 =/=Int 0
    rule W0 %Word W1 => 0            requires W1  ==Int 0
    rule W0 %Word W1 => W0 modInt W1 requires W1 =/=Int 0
```

Care is needed for `^Word` to avoid big exponentiation.
The helper `powmod` is a totalization of the operator `_^%Int__` (which comes with K).
`_^%Int__` is not defined when the modulus (third argument) is zero, but `powmod` is.

```k
    syntax Int ::= Int "^Word" Int       [function]
    syntax Int ::= powmod(Int, Int, Int) [function, functional]
 // -----------------------------------------------------------
    rule W0 ^Word W1 => powmod(W0, W1, pow256)

    rule powmod(W0, W1, W2) => W0 ^%Int W1 W2  requires W2 =/=Int 0 [concrete]
    rule powmod(W0, W1, W2) => 0               requires W2  ==Int 0 [concrete]
```

`/sWord` and `%sWord` give the signed interperetations of `/Word` and `%Word`.

```k
    syntax Int ::= Int "/sWord" Int [function]
                 | Int "%sWord" Int [function]
 // ------------------------------------------
    rule W0 /sWord W1 => #sgnInterp(sgn(W0) *Int sgn(W1) , abs(W0) /Word abs(W1))
    rule W0 %sWord W1 => #sgnInterp(sgn(W0)              , abs(W0) %Word abs(W1))

    syntax Int ::= #sgnInterp ( Int , Int ) [function, functional]
 // --------------------------------------------------------------
    rule #sgnInterp( W0 , W1 ) => 0          requires W0 ==Int 0
    rule #sgnInterp( W0 , W1 ) => W1         requires W0 >Int 0
    rule #sgnInterp( W0 , W1 ) => 0 -Word W1 requires W0 <Int 0
```

### Word Comparison

The `<op>Word` comparisons similarly lift K operators to EVM ones:

```k
    syntax Int ::= Int "<Word"  Int [function, functional]
                 | Int ">Word"  Int [function, functional]
                 | Int "<=Word" Int [function, functional]
                 | Int ">=Word" Int [function, functional]
                 | Int "==Word" Int [function, functional]
 // ------------------------------------------------------
    rule W0 <Word  W1 => bool2Word(W0 <Int  W1)
    rule W0 >Word  W1 => bool2Word(W0 >Int  W1)
    rule W0 <=Word W1 => bool2Word(W0 <=Int W1)
    rule W0 >=Word W1 => bool2Word(W0 >=Int W1)
    rule W0 ==Word W1 => bool2Word(W0 ==Int W1)
```

-   `s<Word` implements a less-than for `Word` (with signed interperetation).

```k
    syntax Int ::= Int "s<Word" Int [function, functional]
 // ------------------------------------------------------
    rule W0 s<Word W1 => W0 <Word W1           requires sgn(W0) ==K 1  andBool sgn(W1) ==K 1    [concrete]
    rule W0 s<Word W1 => bool2Word(false)      requires sgn(W0) ==K 1  andBool sgn(W1) ==K -1   [concrete]
    rule W0 s<Word W1 => bool2Word(true)       requires sgn(W0) ==K -1 andBool sgn(W1) ==K 1    [concrete]
    rule W0 s<Word W1 => abs(W1) <Word abs(W0) requires sgn(W0) ==K -1 andBool sgn(W1) ==K -1   [concrete]
```

### Bitwise Operators

Bitwise logical operators are lifted from the integer versions.

```k
    syntax Int ::= "~Word" Int       [function, functional]
                 | Int "|Word"   Int [function, functional]
                 | Int "&Word"   Int [function, functional]
                 | Int "xorWord" Int [function, functional]
                 | Int "<<Word"  Int [function]
                 | Int ">>Word"  Int [function]
                 | Int ">>sWord" Int [function]
 // -------------------------------------------
    rule ~Word W       => W xorInt maxUInt256
    rule W0 |Word   W1 => W0 |Int W1
    rule W0 &Word   W1 => W0 &Int W1
    rule W0 xorWord W1 => W0 xorInt W1
    rule W0 <<Word  W1 => chop( W0 <<Int W1 ) requires W1 <Int 256
    rule W0 <<Word  W1 => 0 requires W1 >=Int 256
    rule W0 >>Word  W1 => W0 >>Int W1
    rule W0 >>sWord W1 => chop( (abs(W0) *Int sgn(W0)) >>Int W1 )
```

-   `bit` gets bit $N$ (0 being MSB).
-   `byte` gets byte $N$ (0 being the MSB).

```k
    syntax Int ::= bit  ( Int , Int ) [function]
                 | byte ( Int , Int ) [function]
 // --------------------------------------------
    rule bit (N, _) => 0 requires notBool (N >=Int 0 andBool N <Int 256)
    rule byte(N, _) => 0 requires notBool (N >=Int 0 andBool N <Int  32)

    rule bit (N, W) => bitRangeInt(W , (255 -Int N)        , 1) requires N >=Int 0 andBool N <Int 256
    rule byte(N, W) => bitRangeInt(W , ( 31 -Int N) *Int 8 , 8) requires N >=Int 0 andBool N <Int  32
```

-   `#nBits` shifts in $N$ ones from the right.
-   `#nBytes` shifts in $N$ bytes of ones from the right.
-   `_<<Byte_` shifts an integer 8 bits to the left.
-   `_>>Byte_` shifts an integer 8 bits to the right.

```k
    syntax Int ::= #nBits  ( Int )  [function]
                 | #nBytes ( Int )  [function]
                 | Int "<<Byte" Int [function]
                 | Int ">>Byte" Int [function]
 // ------------------------------------------
    rule #nBits(N)  => (1 <<Int N) -Int 1 requires N >=Int 0
    rule #nBytes(N) => #nBits(N *Int 8)   requires N >=Int 0
    rule N <<Byte M => N <<Int (8 *Int M)
    rule N >>Byte M => N >>Int (8 *Int M)
```

-   `signextend(N, W)` sign-extends from byte $N$ of $W$ (0 being MSB).

```k
    syntax Int ::= signextend( Int , Int ) [function, functional]
 // -------------------------------------------------------------
    rule signextend(N, W) => W requires N >=Int 32 orBool N <Int 0    [concrete]
    rule signextend(N, W) => chop( (#nBytes(31 -Int N) <<Byte (N +Int 1)) |Int W ) requires N <Int 32 andBool N >=Int 0 andBool         word2Bool(bit(256 -Int (8 *Int (N +Int 1)), W))   [concrete]
    rule signextend(N, W) => chop( #nBytes(N +Int 1)                      &Int W ) requires N <Int 32 andBool N >=Int 0 andBool notBool word2Bool(bit(256 -Int (8 *Int (N +Int 1)), W))   [concrete]
```

-   `keccak` serves as a wrapper around the `Keccak256` in `KRYPTO`.

```k
    syntax Int ::= keccak ( ByteArray ) [function, smtlib(smt_keccak)]
 // ------------------------------------------------------------------
    rule keccak(WS) => #parseHexWord(Keccak256(#unparseByteStack(WS))) [concrete]
```

Data-Structures over `Word`
===========================

A WordStack for EVM
-------------------


### As a cons-list

A cons-list is used for the EVM wordstack.

-   `.WordStack` serves as the empty worstack, and
-   `_:_` serves as the "cons" operator.

```k
    syntax WordStack [flatPredicate]
    syntax WordStack ::= ".WordStack"      [smtlib(_dotWS)]
                       | Int ":" WordStack [klabel(_:_WS), smtlib(_WS_)]
 // --------------------------------------------------------------------
```

-   `#take(N , WS)` keeps the first $N$ elements of a `WordStack` (passing with zeros as needed).
-   `#drop(N , WS)` removes the first $N$ elements of a `WordStack`.

```k
    syntax WordStack ::= #take ( Int , WordStack ) [function, functional]
 // ---------------------------------------------------------------------
    rule #take(N, WS)         => .WordStack                      requires notBool N >Int 0
    rule #take(N, .WordStack) => 0 : #take(N -Int 1, .WordStack) requires N >Int 0
    rule #take(N, (W : WS))   => W : #take(N -Int 1, WS)         requires N >Int 0

    syntax WordStack ::= #drop ( Int , WordStack ) [function, functional]
 // ---------------------------------------------------------------------
    rule #drop(N, WS)         => WS                  requires notBool N >Int 0
    rule #drop(N, .WordStack) => .WordStack
    rule #drop(N, (W : WS))   => #drop(N -Int 1, WS) requires N >Int 0
```

### Element Access

-   `WS [ N ]` accesses element $N$ of $WS$.
-   `WS [ N := W ]` sets element $N$ of $WS$ to $W$ (padding with zeros as needed).

```k
    syntax Int ::= WordStack "[" Int "]" [function]
 // -----------------------------------------------
    rule (W0 : WS)   [N] => W0           requires N ==Int 0
    rule (W0 : WS)   [N] => WS[N -Int 1] requires N >Int 0

    syntax WordStack ::= WordStack "[" Int ":=" Int "]" [function]
 // --------------------------------------------------------------
    rule (W0 : WS)  [ N := W ] => W  : WS                             requires N ==Int 0
    rule (W0 : WS)  [ N := W ] => W0 : (WS [ N -Int 1 := W ])         requires N >Int 0
```

-   Definedness conditions for `WS [ N ]` and `WS [ N := W ]`

```{.k .symbolic}
    rule #Ceil(WS[N])        => {((0 <=Int N) andBool (N <Int #sizeWordStack(WS))) #Equals true}  [anywhere]
    rule #Ceil(WS[ N := W ]) => {((0 <=Int N) andBool (N <Int #sizeWordStack(WS))) #Equals true}  [anywhere]
```

-   `#sizeWordStack` calculates the size of a `WordStack`.
-   `_in_` determines if a `Int` occurs in a `WordStack`.

```k
    syntax Int ::= #sizeWordStack ( WordStack )       [function, functional, smtlib(sizeWordStack)]
                 | #sizeWordStack ( WordStack , Int ) [function, functional, klabel(sizeWordStackAux), smtlib(sizeWordStackAux)]
 // ----------------------------------------------------------------------------------------------------------------------------
    rule #sizeWordStack ( WS ) => #sizeWordStack(WS, 0)
    rule #sizeWordStack ( .WordStack, SIZE ) => SIZE
    rule #sizeWordStack ( W : WS, SIZE )     => #sizeWordStack(WS, SIZE +Int 1)

    syntax Bool ::= Int "in" WordStack [function]
 // ---------------------------------------------
    rule W in .WordStack => false
    rule W in (W' : WS)  => (W ==K W') orElseBool (W in WS)
```

-   `#replicateAux` pushes `N` copies of `A` onto a `WordStack`.
-   `#replicate` is a `WordStack` of length `N` with `A` the value of every element.

```k
    syntax WordStack ::= #replicate    ( Int, Int )            [function, functional]
                       | #replicateAux ( Int, Int, WordStack ) [function, functional]
 // ---------------------------------------------------------------------------------
    rule #replicate   ( N, A )     => #replicateAux(N, A, .WordStack)
    rule #replicateAux( N, A, WS ) => #replicateAux(N -Int 1, A, A : WS) requires         N >Int 0
    rule #replicateAux( N, A, WS ) => WS                                 requires notBool N >Int 0
```

-   `WordStack2List` converts a term of sort `WordStack` to a term of sort `List`.

```k
    syntax List ::= WordStack2List ( WordStack ) [function, functional]
 // -------------------------------------------------------------------
    rule WordStack2List(.WordStack) => .List
    rule WordStack2List(W : WS) => ListItem(W) WordStack2List(WS)
```

Byte Arrays
-----------

The local memory of execution is a byte-array (instead of a word-array).

-   `#asWord` will interperet a stack of bytes as a single word (with MSB first).
-   `#asInteger` will interperet a stack of bytes as a single arbitrary-precision integer (with MSB first).
-   `#asAccount` will interpret a stack of bytes as a single account id (with MSB first).
    Differs from `#asWord` only in that an empty stack represents the empty account, not account zero.
-   `#asByteStack` will split a single word up into a `ByteArray`.
-   `_++_` acts as `ByteArray` append.
-   `WS [ N .. W ]` access the range of `WS` beginning with `N` of width `W`.
-   `#sizeByteArray` calculates the size of a `ByteArray`.
-   `#padToWidth(N, WS)` and `#padRightToWidth` make sure that a `WordStack` is the correct size.

```{.k .concrete}
    syntax ByteArray ::= Bytes
                       | ".ByteArray" [function]
 // --------------------------------------------
    rule .ByteArray => .Bytes

    syntax Int ::= #asWord ( ByteArray ) [function, smtlib(asWord)]
 // ---------------------------------------------------------------
    rule #asWord(WS) => chop(Bytes2Int(WS, BE, Unsigned))

    syntax Int ::= #asInteger ( ByteArray ) [function]
 // --------------------------------------------------
    rule #asInteger(WS) => Bytes2Int(WS, BE, Unsigned)

    syntax String ::= #asString ( ByteArray ) [function]
 // ----------------------------------------------------
    rule #asString(WS) => Bytes2String(WS)

    syntax Account ::= #asAccount ( ByteArray ) [function]
 // ------------------------------------------------------
    rule #asAccount(BS) => .Account    requires lengthBytes(BS) ==Int 0
    rule #asAccount(BS) => #asWord(BS) [owise]

    syntax ByteArray ::= #asByteStack ( Int ) [function]
 // ----------------------------------------------------
    rule #asByteStack(W) => Int2Bytes(W, BE, Unsigned)

    syntax ByteArray ::= ByteArray "++" ByteArray [function, right, klabel(_++_WS), smtlib(_plusWS_)]
 // -------------------------------------------------------------------------------------------------
    rule WS ++ WS' => WS +Bytes WS'

    syntax ByteArray ::= ByteArray "[" Int ".." Int "]" [function]
 // --------------------------------------------------------------
    rule WS [ START .. WIDTH ] => substrBytes(padRightBytes(WS, START +Int WIDTH, 0), START, START +Int WIDTH) requires START <Int #sizeByteArray(WS)
    rule WS [ START .. WIDTH ] => padRightBytes(.Bytes, WIDTH, 0)                                              [owise]

    syntax Int ::= #sizeByteArray ( ByteArray ) [function, functional]
 // ------------------------------------------------------------------
    rule #sizeByteArray ( WS ) => lengthBytes(WS)

    syntax ByteArray ::= #padToWidth ( Int , ByteArray ) [function]
 // ---------------------------------------------------------------
    rule #padToWidth(N, WS) => padLeftBytes(WS, N, 0)
```

```{.k .symbolic}
    syntax ByteArray ::= WordStack
                       | ".ByteArray" [function]
 // --------------------------------------------
    rule .ByteArray => .WordStack

    syntax Int ::= #asWord ( ByteArray ) [function, functional, smtlib(asWord)]
 // ---------------------------------------------------------------------------
    rule #asWord( .WordStack     ) => 0                                    // [concrete]
    rule #asWord( W : .WordStack ) => W                                    // [concrete]
    rule #asWord( W0 : W1 : WS   ) => #asWord(((W0 *Word 256) +Word W1) : WS) [concrete]

    syntax Int ::= #asInteger ( ByteArray ) [function]
 // --------------------------------------------------
    rule #asInteger( .WordStack     ) => 0
    rule #asInteger( W : .WordStack ) => W
    rule #asInteger( W0 : W1 : WS   ) => #asInteger(((W0 *Int 256) +Int W1) : WS)

    syntax String ::= #asString ( ByteArray ) [function]
 // ----------------------------------------------------
    rule #asString( .WordStack     ) => ""
    rule #asString( W : .WordStack ) => chrChar( W )
    rule #asString( W0 : WS        ) => chrChar( W0 ) +String #asString( WS )

    syntax Account ::= #asAccount ( ByteArray ) [function]
 // ------------------------------------------------------
    rule #asAccount( .WordStack ) => .Account
    rule #asAccount( W : WS     ) => #asWord(W : WS)

    syntax ByteArray ::= #asByteStack ( Int )             [function, functional]
                       | #asByteStack ( Int , ByteArray ) [function, klabel(#asByteStackAux), smtlib(asByteStack)]
 // --------------------------------------------------------------------------------------------------------------
    rule #asByteStack( W ) => #asByteStack( W , .WordStack )                                        [concrete]
    rule #asByteStack( 0 , WS ) => WS                                                            // [concrete]
    rule #asByteStack( W , WS ) => #asByteStack( W /Int 256 , W modInt 256 : WS ) requires W =/=K 0 [concrete]

    syntax ByteArray ::= ByteArray "++" ByteArray [function, memo, right, klabel(_++_WS), smtlib(_plusWS_)]
 // -------------------------------------------------------------------------------------------------------
    rule .WordStack ++ WS' => WS'
    rule (W : WS)   ++ WS' => W : {WS ++ WS'}:>WordStack

    syntax ByteArray ::= ByteArray "[" Int ".." Int "]" [function, functional, memo]
 // --------------------------------------------------------------------------------
    rule WS [ START .. WIDTH ] => #take(WIDTH, #drop(START, WS))

    syntax Int ::= #sizeByteArray ( ByteArray ) [function, functional, memo]
 // ------------------------------------------------------------------------
    rule #sizeByteArray ( WS ) => #sizeWordStack(WS)

    syntax ByteArray ::= #padToWidth      ( Int , ByteArray ) [function, functional, memo]
                       | #padRightToWidth ( Int , ByteArray ) [function, memo]
 // --------------------------------------------------------------------------------------
    rule #padToWidth(N, WS)      => #replicateAux(N -Int #sizeByteArray(WS), 0, WS) [concrete]
    rule #padRightToWidth(N, WS) => WS ++ #replicate(N -Int #sizeByteArray(WS), 0)  [concrete]
```

Addresses
---------

-   `#addr` turns an Ethereum word into the corresponding Ethereum address (160 LSB).

```k
    syntax Int ::= #addr ( Int ) [function]
 // ---------------------------------------
    rule #addr(W) => W %Word pow160
```

-   `#newAddr` computes the address of a new account given the address and nonce of the creating account.
-   `#sender` computes the sender of the transaction from its data and signature.
-   `#addrFromPrivateKey` computes the address of an account given its private key

```k
    syntax Int ::= #newAddr ( Int , Int ) [function]
                 | #newAddr ( Int , Int , ByteArray ) [function, klabel(#newAddrCreate2)]
 // -------------------------------------------------------------------------------------
    rule #newAddr(ACCT, NONCE) => #addr(#parseHexWord(Keccak256(#rlpEncodeLength(#rlpEncodeBytes(ACCT, 20) +String #rlpEncodeWord(NONCE), 192))))
    rule #newAddr(ACCT, SALT, INITCODE) => #addr(#parseHexWord(Keccak256("\xff" +String #unparseByteStack(#padToWidth(20, #asByteStack(ACCT))) +String #unparseByteStack(#padToWidth(32, #asByteStack(SALT))) +String #unparseByteStack(#parseHexBytes(Keccak256(#unparseByteStack(INITCODE)))))))

    syntax Account ::= #sender ( Int , Int , Int , Account , Int , String , Int , ByteArray , ByteArray ) [function]
                     | #sender ( String , Int , String , String )                                         [function, klabel(#senderAux)]
                     | #sender ( String )                                                                 [function, klabel(#senderAux2)]
 // -------------------------------------------------------------------------------------------------------------------------------------
    rule #sender(TN, TP, TG, TT, TV, DATA, TW, TR, TS)
      => #sender(#unparseByteStack(#parseHexBytes(Keccak256(#rlpEncodeLength(#rlpEncodeWordStack(TN : TP : TG : .WordStack) +String #rlpEncodeAccount(TT) +String #rlpEncodeWord(TV) +String #rlpEncodeString(DATA), 192)))), TW, #unparseByteStack(TR), #unparseByteStack(TS))

    rule #sender(HT, TW, TR, TS) => #sender(ECDSARecover(HT, TW, TR, TS))

    rule #sender("")  => .Account
    rule #sender(STR) => #addr(#parseHexWord(Keccak256(STR))) requires STR =/=String ""

    syntax Int ::= #addrFromPrivateKey ( String ) [function]
 // --------------------------------------------------------
    rule #addrFromPrivateKey ( KEY ) => #addr( #parseHexWord( Keccak256 ( Hex2Raw( ECDSAPubKey( Hex2Raw( KEY ) ) ) ) ) )
```

-   `#blockHeaderHash` computes the hash of a block header given all the block data.

```k
    syntax Int ::= #blockHeaderHash( Int , Int , Int , Int , Int , Int , ByteArray , Int , Int , Int , Int , Int , ByteArray , Int , Int ) [function, klabel(blockHeaderHash), symbol]
                 | #blockHeaderHash(String, String, String, String, String, String, String, String, String, String, String, String, String, String, String) [function, klabel(#blockHashHeaderStr), symbol]
 // -------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------
   rule #blockHeaderHash(HP, HO, HC, HR, HT, HE, HB, HD, HI, HL, HG, HS, HX, HM, HN)
         => #blockHeaderHash(#asWord(#parseByteStackRaw(HP)),
                             #asWord(#parseByteStackRaw(HO)),
                             #asWord(#parseByteStackRaw(HC)),
                             #asWord(#parseByteStackRaw(HR)),
                             #asWord(#parseByteStackRaw(HT)),
                             #asWord(#parseByteStackRaw(HE)),
                                     #parseByteStackRaw(HB) ,
                             #asWord(#parseByteStackRaw(HD)),
                             #asWord(#parseByteStackRaw(HI)),
                             #asWord(#parseByteStackRaw(HL)),
                             #asWord(#parseByteStackRaw(HG)),
                             #asWord(#parseByteStackRaw(HS)),
                                     #parseByteStackRaw(HX) ,
                             #asWord(#parseByteStackRaw(HM)),
                             #asWord(#parseByteStackRaw(HN)))

    rule #blockHeaderHash(HP, HO, HC, HR, HT, HE, HB, HD, HI, HL, HG, HS, HX, HM, HN)
         => #parseHexWord(Keccak256(#rlpEncodeLength(         #rlpEncodeBytes(HP, 32)
                                                      +String #rlpEncodeBytes(HO, 32)
                                                      +String #rlpEncodeBytes(HC, 20)
                                                      +String #rlpEncodeBytes(HR, 32)
                                                      +String #rlpEncodeBytes(HT, 32)
                                                      +String #rlpEncodeBytes(HE, 32)
                                                      +String #rlpEncodeString(#unparseByteStack(HB))
                                                      +String #rlpEncodeWordStack(HD : HI : HL : HG : HS : .WordStack)
                                                      +String #rlpEncodeString(#unparseByteStack(HX))
                                                      +String #rlpEncodeBytes(HM, 32)
                                                      +String #rlpEncodeBytes(HN, 8),
                                                    192)))

```

- `M3:2048` computes the 2048-bit hash of a log entry in which exactly 3 bits are set. This is used to compute the Bloom filter of a log entry.

```k
    syntax Int ::= "M3:2048" "(" ByteArray ")" [function]
 // -----------------------------------------------------
    rule M3:2048(WS) => setBloomFilterBits(#parseByteStack(Keccak256(#unparseByteStack(WS))))

    syntax Int ::= setBloomFilterBits(ByteArray) [function]
 // -------------------------------------------------------
    rule setBloomFilterBits(HASH) => (1 <<Int getBloomFilterBit(HASH, 0)) |Int (1 <<Int getBloomFilterBit(HASH, 2)) |Int (1 <<Int getBloomFilterBit(HASH, 4))

    syntax Int ::= getBloomFilterBit(ByteArray, Int) [function]
 // -----------------------------------------------------------
    rule getBloomFilterBit(X, I) => #asInteger(X [ I .. 2 ]) %Int 2048
```

Word Map
--------

Most of EVM data is held in finite maps.
We are using the polymorphic `Map` sort for these word maps.

-   `WM [ N := WS ]` assigns a contiguous chunk of $WM$ to $WS$ starting at position $W$.
-   `#range(M, START, WIDTH)` reads off $WIDTH$ elements from $WM$ beginning at position $START$ (padding with zeros as needed).

```{.k .concrete}
    syntax Map ::= Map "[" Int ":=" ByteArray "]" [function, klabel(mapWriteBytes)]
 // -------------------------------------------------------------------------------
    rule WM[ N := WS ] => WM [ N := WS, 0, #sizeByteArray(WS) ]

    syntax Map ::= Map "[" Int ":=" ByteArray "," Int "," Int "]" [function]
 // ------------------------------------------------------------------------
    rule WM [ N := WS, I, I ] => WM
    rule WM [ N := WS, I, J ] => (WM[N <- WS[I]])[ N +Int 1 := WS, I +Int 1, J ] [owise]

    syntax ByteArray ::= #range ( Map , Int , Int )                   [function]
                       | #range ( Map , Int , Int , Int , ByteArray ) [function, klabel(#rangeAux)]
 // -----------------------------------------------------------------------------------------------
    rule #range(WM, START, WIDTH) => #range(WM, START, 0, WIDTH, padLeftBytes(.Bytes, WIDTH, 0))
    rule #range(WM, I, WIDTH, WIDTH, WS) => WS
    rule #range(WM, I,     J, WIDTH, WS) => #range(WM, I +Int 1, J +Int 1, WIDTH, WS [ J <- {WM[I] orDefault 0}:>Int ]) [owise]
```

```{.k .symbolic}
    syntax Map ::= Map "[" Int ":=" ByteArray "]" [function, functional]
 // --------------------------------------------------------------------
    rule WM[ N := .WordStack ] => WM
    rule WM[ N := W : WS     ] => (WM[N <- W])[N +Int 1 := WS] [concrete]

    syntax ByteArray ::= #range ( Map , Int , Int )             [function, functional]
    syntax ByteArray ::= #range ( Map , Int , Int , ByteArray ) [function, functional, klabel(#rangeAux)]
 // -----------------------------------------------------------------------------------------------------
    rule #range(WM, START, WIDTH) => #range(WM, START +Int WIDTH -Int 1, WIDTH, .WordStack) [concrete]
    rule #range(WM,           END, WIDTH, WS) => WS                                           requires notBool WIDTH >Int 0
    rule #range(WM,           END, WIDTH, WS) => #range(WM, END -Int 1, WIDTH -Int 1, 0 : WS) requires (WIDTH >Int 0) andBool notBool END in_keys(WM)
    rule #range(END |-> W WM, END, WIDTH, WS) => #range(WM, END -Int 1, WIDTH -Int 1, W : WS) requires (WIDTH >Int 0)
```

-   `#removeZeros` removes any entries in a map with zero values.

```k
    syntax Map ::= #removeZeros ( Map ) [function]
                 | #removeZeros ( List , Map ) [function, klabel(#removeZerosAux)]
 // ------------------------------------------------------------------------------
    rule #removeZeros( M )                                   => #removeZeros(Set2List(keys(M)), M)
    rule #removeZeros( .List, .Map )                         => .Map
    rule #removeZeros( ListItem(KEY) L, KEY |-> 0 REST )     => #removeZeros(L, REST)
    rule #removeZeros( ListItem(KEY) L, KEY |-> VALUE REST ) => KEY |-> VALUE #removeZeros(L, REST) requires VALUE =/=K 0
```

-   `#lookup` looks up a key in a map and returns 0 if the key doesn't exist, otherwise returning its value.

```k
    syntax Int ::= #lookup ( Map , Int ) [function]
 // -----------------------------------------------
    rule #lookup( (KEY |-> VAL) M, KEY ) => VAL                               [concrete]
    rule #lookup(               M, KEY ) => 0 requires notBool KEY in_keys(M) [concrete]
```

Parsing/Unparsing
=================

The EVM test-sets are represented in JSON format with hex-encoding of the data and programs.
Here we provide some standard parser/unparser functions for that format.

Parsing
-------

These parsers can interperet hex-encoded strings as `Int`s, `ByteArray`s, and `Map`s.

-   `#parseHexWord` interprets a string as a single hex-encoded `Word`.
-   `#parseHexBytes` interprets a string as a hex-encoded stack of bytes.
-   `#parseByteStack` interprets a string as a hex-encoded stack of bytes, but makes sure to remove the leading "0x".
-   `#parseByteStackRaw` inteprets a string as a stack of bytes.
-   `#parseWordStack` interprets a JSON list as a stack of `Word`.
-   `#parseMap` interprets a JSON key/value object as a map from `Word` to `Word`.
-   `#parseAddr` interprets a string as a 160 bit hex-endcoded address.

```k
    syntax Int ::= #parseHexWord ( String ) [function]
                 | #parseWord    ( String ) [function]
 // --------------------------------------------------
    rule #parseHexWord("")   => 0
    rule #parseHexWord("0x") => 0
    rule #parseHexWord(S)    => String2Base(replaceAll(S, "0x", ""), 16) requires (S =/=String "") andBool (S =/=String "0x")

    rule #parseWord("") => 0
    rule #parseWord(S)  => #parseHexWord(S) requires lengthString(S) >=Int 2 andBool substrString(S, 0, 2) ==String "0x"
    rule #parseWord(S)  => String2Int(S) [owise]
```

```{.k .concrete}
    syntax ByteArray ::= #parseHexBytes     ( String ) [function]
                       | #parseByteStack    ( String ) [function]
                       | #parseByteStackRaw ( String ) [function]
 // -------------------------------------------------------------
    rule #parseByteStack(S) => #parseHexBytes(replaceAll(S, "0x", ""))
    rule #parseHexBytes("") => .ByteArray
    rule #parseHexBytes(S)  => Int2Bytes(1, #parseHexWord(substrString(S, 0, 2)), BE) +Bytes {#parseHexBytes(substrString(S, 2, lengthString(S)))}:>Bytes requires lengthString(S) >=Int 2

    rule #parseByteStackRaw(S) => String2Bytes(S)
```

```{.k .symbolic}
    syntax ByteArray ::= #parseHexBytes     ( String ) [function]
                       | #parseByteStack    ( String ) [function]
                       | #parseByteStackRaw ( String ) [function]
 // -------------------------------------------------------------
    rule #parseByteStack(S) => #parseHexBytes(replaceAll(S, "0x", ""))
    rule #parseHexBytes("") => .WordStack
    rule #parseHexBytes(S)  => #parseHexWord(substrString(S, 0, 2)) : {#parseHexBytes(substrString(S, 2, lengthString(S)))}:>WordStack requires lengthString(S) >=Int 2

    rule #parseByteStackRaw(S) => ordChar(substrString(S, 0, 1)) : {#parseByteStackRaw(substrString(S, 1, lengthString(S)))}:>WordStack requires lengthString(S) >=Int 1
    rule #parseByteStackRaw("") => .WordStack
```

```k
    syntax Map ::= #parseMap ( JSON ) [function]
 // --------------------------------------------
    rule #parseMap( { .JSONList                   } ) => .Map
    rule #parseMap( { _   : (VALUE:String) , REST } ) => #parseMap({ REST })                                                requires #parseHexWord(VALUE) ==K 0
    rule #parseMap( { KEY : (VALUE:String) , REST } ) => #parseMap({ REST }) [ #parseHexWord(KEY) <- #parseHexWord(VALUE) ] requires #parseHexWord(VALUE) =/=K 0

    syntax Int ::= #parseAddr ( String ) [function]
 // -----------------------------------------------
    rule #parseAddr(S) => #addr(#parseHexWord(S))
```

Unparsing
---------

We need to interperet a `ByteArray` as a `String` again so that we can call `Keccak256` on it from `KRYPTO`.

-   `#unparseByteStack` turns a stack of bytes (as a `ByteArray`) into a `String`.
-   `#padByte` ensures that the `String` interperetation of a `Int` is wide enough.

```{.k .concrete}
    syntax String ::= #unparseByteStack ( ByteArray ) [function, klabel(unparseByteStack), symbol]
 // ----------------------------------------------------------------------------------------------
    rule #unparseByteStack(WS) => Bytes2String(WS)
```

```{.k .symbolic}
    syntax String ::= #unparseByteStack ( ByteArray )                [function, klabel(unparseByteStack), symbol]
                    | #unparseByteStack ( ByteArray , StringBuffer ) [function, klabel(#unparseByteStackAux)]
 // ---------------------------------------------------------------------------------------------------------
    rule #unparseByteStack ( WS ) => #unparseByteStack(WS, .StringBuffer)

    rule #unparseByteStack( .WordStack, BUFFER ) => StringBuffer2String(BUFFER)
    rule #unparseByteStack( W : WS, BUFFER )     => #unparseByteStack(WS, BUFFER +String chrChar(W modInt (2 ^Int 8)))
```

```k
    syntax String ::= #padByte( String ) [function]
 // -----------------------------------------------
    rule #padByte( S ) => S             requires lengthString(S) ==K 2
    rule #padByte( S ) => "0" +String S requires lengthString(S) ==K 1

    syntax String ::= #unparseQuantity( Int ) [function]
 // ----------------------------------------------------
    rule #unparseQuantity( I ) => "0x" +String Base2String(I, 16)

    syntax String ::= #unparseData          ( Int, Int  ) [function]
                    | #unparseDataByteArray ( ByteArray ) [function]
 // ----------------------------------------------------------------
    rule #unparseData( DATA, LENGTH ) => #unparseDataByteArray(#padToWidth(LENGTH,#asByteStack(DATA)))

    rule #unparseDataByteArray( DATA ) => replaceFirst(Base2String(#asInteger(#asByteStack(1) ++ DATA), 16), "1", "0x")
```

String Helper Functions
-----------------------

- `Hex2Raw` Takes a string of hex encoded bytes and converts it to a raw bytestring
- `Raw2Hex` Takes a string of raw bytes and converts it to a hex representation

```k
    syntax String ::= Hex2Raw ( String ) [function]
                    | Raw2Hex ( String ) [function]
 // -----------------------------------------------
    rule Hex2Raw ( S ) => #unparseByteStack( #parseByteStack ( S ) )
    rule Raw2Hex ( S ) => #unparseDataByteArray( #parseByteStackRaw ( S ) )
```

Recursive Length Prefix (RLP)
=============================

RLP encoding is used extensively for executing the blocks of a transaction.
For details about RLP encoding, see the [YellowPaper Appendix B](http://gavwood.com/paper.pdf).

Encoding
--------

-   `#rlpEncodeWord` RLP encodes a single EVM word.
-   `#rlpEncodeString` RLP encodes a single `String`.

```k
    syntax String ::= #rlpEncodeWord ( Int )            [function]
                    | #rlpEncodeBytes ( Int , Int )     [function]
                    | #rlpEncodeWordStack ( WordStack ) [function]
                    | #rlpEncodeString ( String )       [function]
                    | #rlpEncodeAccount ( Account )     [function]
 // --------------------------------------------------------------
    rule #rlpEncodeWord(0) => "\x80"
    rule #rlpEncodeWord(WORD) => chrChar(WORD) requires WORD >Int 0 andBool WORD <Int 128
    rule #rlpEncodeWord(WORD) => #rlpEncodeLength(#unparseByteStack(#asByteStack(WORD)), 128) requires WORD >=Int 128

    rule #rlpEncodeBytes(WORD, LEN) => #rlpEncodeString(#unparseByteStack(#padToWidth(LEN, #asByteStack(WORD))))

    rule #rlpEncodeWordStack(.WordStack) => ""
    rule #rlpEncodeWordStack(W : WS)     => #rlpEncodeWord(W) +String #rlpEncodeWordStack(WS)

    rule #rlpEncodeString(STR) => STR                        requires lengthString(STR) ==Int 1 andBool ordChar(STR) <Int 128
    rule #rlpEncodeString(STR) => #rlpEncodeLength(STR, 128) [owise]

    rule #rlpEncodeAccount(.Account) => "\x80"
    rule #rlpEncodeAccount(ACCT)     => #rlpEncodeBytes(ACCT, 20) requires ACCT =/=K .Account

    syntax String ::= #rlpEncodeLength ( String , Int )          [function]
                    | #rlpEncodeLength ( String , Int , String ) [function, klabel(#rlpEncodeLengthAux)]
 // ----------------------------------------------------------------------------------------------------
    rule #rlpEncodeLength(STR, OFFSET) => chrChar(lengthString(STR) +Int OFFSET) +String STR requires lengthString(STR) <Int 56
    rule #rlpEncodeLength(STR, OFFSET) => #rlpEncodeLength(STR, OFFSET, #unparseByteStack(#asByteStack(lengthString(STR)))) requires lengthString(STR) >=Int 56
    rule #rlpEncodeLength(STR, OFFSET, BL) => chrChar(lengthString(BL) +Int OFFSET +Int 55) +String BL +String STR

    syntax String ::= #rlpEncodeMerkleTree ( MerkleTree ) [function]
 // ----------------------------------------------------------------
    rule #rlpEncodeMerkleTree ( .MerkleTree ) => "\x80"

    rule #rlpEncodeMerkleTree ( MerkleLeaf ( PATH, VALUE ) )
      => #rlpEncodeLength(         #rlpEncodeString( #asString( #HPEncode( PATH, 1 ) ) )
                           +String #rlpEncodeString( VALUE )
                         , 192
                         )

    rule #rlpEncodeMerkleTree ( MerkleExtension ( PATH, TREE ) )
      => #rlpEncodeLength(         #rlpEncodeString( #asString( #HPEncode( PATH, 0 ) ) )
                           +String #rlpMerkleH( #rlpEncodeMerkleTree( TREE ) )
                         , 192
                         )

    rule #rlpEncodeMerkleTree ( MerkleBranch (  0 |->  P0:MerkleTree  1 |->  P1:MerkleTree  2 |->  P2:MerkleTree  3 |->  P3:MerkleTree
                                                4 |->  P4:MerkleTree  5 |->  P5:MerkleTree  6 |->  P6:MerkleTree  7 |->  P7:MerkleTree
                                                8 |->  P8:MerkleTree  9 |->  P9:MerkleTree 10 |-> P10:MerkleTree 11 |-> P11:MerkleTree
                                               12 |-> P12:MerkleTree 13 |-> P13:MerkleTree 14 |-> P14:MerkleTree 15 |-> P15:MerkleTree
                                             , VALUE
                                             )
                        )
      => #rlpEncodeLength(         #rlpMerkleH( #rlpEncodeMerkleTree(  P0 ) ) +String #rlpMerkleH( #rlpEncodeMerkleTree(  P1 ) )
                           +String #rlpMerkleH( #rlpEncodeMerkleTree(  P2 ) ) +String #rlpMerkleH( #rlpEncodeMerkleTree(  P3 ) )
                           +String #rlpMerkleH( #rlpEncodeMerkleTree(  P4 ) ) +String #rlpMerkleH( #rlpEncodeMerkleTree(  P5 ) )
                           +String #rlpMerkleH( #rlpEncodeMerkleTree(  P6 ) ) +String #rlpMerkleH( #rlpEncodeMerkleTree(  P7 ) )
                           +String #rlpMerkleH( #rlpEncodeMerkleTree(  P8 ) ) +String #rlpMerkleH( #rlpEncodeMerkleTree(  P9 ) )
                           +String #rlpMerkleH( #rlpEncodeMerkleTree( P10 ) ) +String #rlpMerkleH( #rlpEncodeMerkleTree( P11 ) )
                           +String #rlpMerkleH( #rlpEncodeMerkleTree( P12 ) ) +String #rlpMerkleH( #rlpEncodeMerkleTree( P13 ) )
                           +String #rlpMerkleH( #rlpEncodeMerkleTree( P14 ) ) +String #rlpMerkleH( #rlpEncodeMerkleTree( P15 ) )
                           +String #rlpEncodeString( VALUE )
                         , 192
                         )

    syntax String ::= #rlpMerkleH ( String ) [function,klabel(MerkleRLPAux)]
 // ------------------------------------------------------------------------
    rule #rlpMerkleH ( X ) => #rlpEncodeString( Hex2Raw( Keccak256( X ) ) )
      requires lengthString( X ) >=Int 32

    rule #rlpMerkleH ( X ) => X [owise]
```

Decoding
--------

-   `#rlpDecode` RLP decodes a single `String` into a `JSON`.
-   `#rlpDecodeList` RLP decodes a single `String` into a `JSONList`, interpereting the string as the RLP encoding of a list.

```k
    syntax JSON ::= #rlpDecode(String)               [function]
                  | #rlpDecode(String, LengthPrefix) [function, klabel(#rlpDecodeAux)]
 // ----------------------------------------------------------------------------------
    rule #rlpDecode(STR) => #rlpDecode(STR, #decodeLengthPrefix(STR, 0))
    rule #rlpDecode(STR, #str(LEN, POS))  => substrString(STR, POS, POS +Int LEN)
    rule #rlpDecode(STR, #list(LEN, POS)) => [#rlpDecodeList(STR, POS)]

    syntax JSONList ::= #rlpDecodeList(String, Int)               [function]
                      | #rlpDecodeList(String, Int, LengthPrefix) [function, klabel(#rlpDecodeListAux)]
 // ---------------------------------------------------------------------------------------------------
    rule #rlpDecodeList(STR, POS) => #rlpDecodeList(STR, POS, #decodeLengthPrefix(STR, POS)) requires POS <Int lengthString(STR)
    rule #rlpDecodeList(STR, POS) => .JSONList [owise]
    rule #rlpDecodeList(STR, POS, _:LengthPrefixType(L, P)) => #rlpDecode(substrString(STR, POS, L +Int P)) , #rlpDecodeList(STR, L +Int P)

    syntax LengthPrefixType ::= "#str" | "#list"
    syntax LengthPrefix ::= LengthPrefixType "(" Int "," Int ")"
                          | #decodeLengthPrefix ( String , Int )                                [function]
                          | #decodeLengthPrefix ( String , Int , Int )                          [function, klabel(#decodeLengthPrefixAux)]
                          | #decodeLengthPrefixLength ( LengthPrefixType , String , Int , Int ) [function]
                          | #decodeLengthPrefixLength ( LengthPrefixType , Int    , Int , Int ) [function, klabel(#decodeLengthPrefixLengthAux)]
 // --------------------------------------------------------------------------------------------------------------------------------------------
    rule #decodeLengthPrefix(STR, START) => #decodeLengthPrefix(STR, START, ordChar(substrString(STR, START, START +Int 1)))

    rule #decodeLengthPrefix(STR, START, B0) => #str(1, START)                                   requires B0 <Int 128
    rule #decodeLengthPrefix(STR, START, B0) => #str(B0 -Int 128, START +Int 1)                  requires B0 >=Int 128 andBool B0 <Int (128 +Int 56)
    rule #decodeLengthPrefix(STR, START, B0) => #decodeLengthPrefixLength(#str, STR, START, B0)  requires B0 >=Int (128 +Int 56) andBool B0 <Int 192
    rule #decodeLengthPrefix(STR, START, B0) => #list(B0 -Int 192, START +Int 1)                 requires B0 >=Int 192 andBool B0 <Int 192 +Int 56
    rule #decodeLengthPrefix(STR, START, B0) => #decodeLengthPrefixLength(#list, STR, START, B0) [owise]

    rule #decodeLengthPrefixLength(#str,  STR, START, B0) => #decodeLengthPrefixLength(#str,  START, B0 -Int 128 -Int 56 +Int 1, #asWord(#parseByteStackRaw(substrString(STR, START +Int 1, START +Int 1 +Int (B0 -Int 128 -Int 56 +Int 1)))))
    rule #decodeLengthPrefixLength(#list, STR, START, B0) => #decodeLengthPrefixLength(#list, START, B0 -Int 192 -Int 56 +Int 1, #asWord(#parseByteStackRaw(substrString(STR, START +Int 1, START +Int 1 +Int (B0 -Int 192 -Int 56 +Int 1)))))
    rule #decodeLengthPrefixLength(TYPE, START, LL, L) => TYPE(L, START +Int 1 +Int LL)
```

Merkle Patricia Tree
====================

- Appendix C and D from the Ethereum Yellow Paper
- https://github.com/ethereum/wiki/wiki/Patricia-Tree

```k
    syntax KItem ::= Int | MerkleTree // For testing purposes

    syntax MerkleTree ::= MerkleBranch    ( Map, String )
                        | MerkleExtension ( ByteArray, MerkleTree )
                        | MerkleLeaf      ( ByteArray, String )
                        | ".MerkleTree"
                        | ".MerkleBranch"            [function]
 // -----------------------------------------------------------
    rule .MerkleBranch
      => MerkleBranch (  0 |-> .MerkleTree  1 |-> .MerkleTree  2 |-> .MerkleTree  3 |-> .MerkleTree
                         4 |-> .MerkleTree  5 |-> .MerkleTree  6 |-> .MerkleTree  7 |-> .MerkleTree
                         8 |-> .MerkleTree  9 |-> .MerkleTree 10 |-> .MerkleTree 11 |-> .MerkleTree
                        12 |-> .MerkleTree 13 |-> .MerkleTree 14 |-> .MerkleTree 15 |-> .MerkleTree
                      , ""
                      )

    syntax MerkleTree ::= MerkleUpdate ( MerkleTree,     String, String ) [function]
                        | MerkleUpdate ( MerkleTree,  ByteArray, String ) [function,klabel(MerkleUpdateAux)]
 // --------------------------------------------------------------------------------------------------------
    rule MerkleUpdate ( TREE, S:String, VALUE ) => MerkleUpdate ( TREE, #nibbleize ( #parseByteStackRaw( S ) ), VALUE )

    rule MerkleUpdate ( .MerkleTree, PATH:ByteArray, VALUE ) => MerkleLeaf ( PATH, VALUE )

    rule MerkleUpdate ( MerkleLeaf ( LEAFPATH, _ ), PATH, VALUE )
      => MerkleLeaf( LEAFPATH, VALUE )
      requires #asInteger( LEAFPATH ) ==Int #asInteger( PATH )

    rule MerkleUpdate ( MerkleLeaf ( LEAFPATH, LEAFVALUE ), PATH, VALUE )
      => MerkleUpdate ( MerkleUpdate ( .MerkleBranch, LEAFPATH, LEAFVALUE ), PATH, VALUE )
      requires #sizeByteArray( LEAFPATH ) >Int 0
       andBool #sizeByteArray( PATH ) >Int 0
       andBool LEAFPATH[0] =/=Int PATH[0]

    rule MerkleUpdate ( MerkleLeaf ( LEAFPATH, LEAFVALUE ), PATH, VALUE )
      => #merkleExtensionBuilder( .ByteArray, LEAFPATH, LEAFVALUE, PATH, VALUE ) [owise]

    rule MerkleUpdate ( MerkleExtension ( EXTPATH, EXTTREE ), PATH, VALUE )
      => MerkleExtension ( EXTPATH, MerkleUpdate ( EXTTREE, .ByteArray, VALUE ) )
      requires #asInteger( EXTPATH ) ==Int #asInteger( PATH )

    rule MerkleUpdate ( MerkleExtension ( EXTPATH, EXTTREE ), PATH, VALUE )
      => #merkleExtensionBrancher( MerkleUpdate( .MerkleBranch, PATH, VALUE ), EXTPATH, EXTTREE )
      requires #sizeByteArray( EXTPATH ) >Int 0
       andBool #sizeByteArray( PATH ) >Int 0
       andBool EXTPATH[0] =/=Int PATH[0]

    rule MerkleUpdate ( MerkleExtension ( EXTPATH, EXTTREE ), PATH, VALUE )
      => #merkleExtensionSplitter( .ByteArray, EXTPATH, EXTTREE, PATH, VALUE ) [owise]

    rule MerkleUpdate ( MerkleBranch( M, _ ), PATH, VALUE )
      => MerkleBranch( M, VALUE )
      requires #sizeByteArray( PATH ) ==Int 0

    rule MerkleUpdate ( MerkleBranch( M, BRANCHVALUE ), PATH, VALUE )
      => #merkleBrancher ( M, BRANCHVALUE, PATH[0], PATH[1 .. #sizeByteArray(PATH) -Int 1], VALUE ) [owise]
```

Merkle Tree Aux Functions
-------------------------

```k
    syntax ByteArray ::= #nibbleize ( ByteArray ) [function]
                       | #byteify   ( ByteArray ) [function]
 // --------------------------------------------------------
    rule #nibbleize ( B ) =>    #asByteStack ( ( B [ 0 ] /Int 16 ) *Int 256 +Int ( B [ 0 ] %Int 16 ) )[0 .. 2]
                             ++ #nibbleize ( B[1 .. #sizeByteArray(B) -Int 1] )
      requires #sizeByteArray( B ) >Int 0

    rule #nibbleize ( _ ) => .ByteArray [owise]

    rule #byteify ( B ) =>    #asByteStack ( B[0] *Int 16 +Int B[1] )
                           ++ #byteify ( B[2 .. #sizeByteArray(B) -Int 2] )
      requires #sizeByteArray(B) >Int 0

    rule #byteify ( _ ) => .ByteArray [owise]

    syntax ByteArray ::= #HPEncode ( ByteArray, Int ) [function]
 // ------------------------------------------------------------
    rule #HPEncode ( X, T ) => #asByteStack ( ( f(T) +Int 1 ) *Int 16 +Int X[0] ) ++ #byteify( X[1 .. #sizeByteArray(X) -Int 1] )
      requires #sizeByteArray(X) %Int 2 =/=Int 0

    rule #HPEncode ( X, T ) => #asByteStack ( f(T) *Int 16 )[0 .. 1] ++ #byteify( X ) [owise]

    syntax Int ::= f ( Int ) [function,klabel(HPEncodeAux)]
 // -------------------------------------------------------
    rule f ( X ) => 0 requires X ==Int 0
    rule f ( _ ) => 2 [owise]

    syntax MerkleTree ::= #merkleBrancher ( Map, String, Int, ByteArray, String ) [function]
 // ----------------------------------------------------------------------------------------
    rule #merkleBrancher ( X |-> TREE M, BRANCHVALUE, X, PATH, VALUE )
      => MerkleBranch( M[X <- MerkleUpdate( TREE, PATH, VALUE )], BRANCHVALUE )

    syntax MerkleTree ::= #merkleExtensionBuilder( ByteArray, ByteArray, String, ByteArray, String ) [function]
 // -----------------------------------------------------------------------------------------------------------
    rule #merkleExtensionBuilder( PATH, P1, V1, P2, V2 )
      => #merkleExtensionBuilder( PATH ++ ( #asByteStack( P1[0] )[0 .. 1] )
                                , P1[1 .. #sizeByteArray(P1) -Int 1], V1
                                , P2[1 .. #sizeByteArray(P2) -Int 1], V2
                                )
      [owise]

    rule #merkleExtensionBuilder( PATH, P1, V1, P2, V2 )
      => MerkleExtension( PATH, MerkleUpdate( MerkleUpdate( .MerkleBranch, P1, V1 ), P2, V2 ) )
      requires #sizeByteArray(P1) >Int 0
       andBool #sizeByteArray(P2) >Int 0
       andBool P1[0] =/=Int P2[0]

    rule #merkleExtensionBuilder( PATH, P1, V1, P2, V2 )
      => MerkleExtension( PATH, MerkleUpdate( MerkleUpdate( .MerkleBranch, P1, V1 ), P2, V2 ) )
      requires #sizeByteArray(P1) ==Int 0
        orBool #sizeByteArray(P2) ==Int 0

    syntax MerkleTree ::= #merkleExtensionBrancher ( MerkleTree, ByteArray, MerkleTree )                   [function]
                        | #merkleExtensionSplitter ( ByteArray, ByteArray, MerkleTree, ByteArray, String ) [function]
 // -----------------------------------------------------------------------------------------------------------------
    rule #merkleExtensionBrancher( MerkleBranch(M, VALUE), PATH, EXTTREE )
      => MerkleBranch( M[PATH[0] <- MerkleExtension( PATH[1 .. #sizeByteArray(PATH) -Int 1], EXTTREE )], VALUE )

    rule #merkleExtensionSplitter( PATH, P1, TREE, P2, VALUE )
      => #merkleExtensionSplitter( PATH ++ ( #asByteStack( P1[0] )[0 .. 1] )
                                 , P1[1 .. #sizeByteArray(P1) -Int 1], TREE
                                 , P2[1 .. #sizeByteArray(P2) -Int 1], VALUE
                                 )
      [owise]

    rule #merkleExtensionSplitter( PATH, P1, TREE, P2, VALUE )
      => MerkleExtension( PATH, #merkleExtensionBrancher( MerkleUpdate( .MerkleBranch, P2, VALUE ), P1, TREE ) )
      requires #sizeByteArray(P1) >Int 0
       andBool #sizeByteArray(P2) >Int 0
       andBool P1[0] =/=Int P2[0]

    rule #merkleExtensionSplitter( PATH, P1, TREE, P2, VALUE )
      => MerkleExtension( PATH, MerkleUpdate( TREE, P2, VALUE ) )
      requires #sizeByteArray(P1) ==Int 0

    rule #merkleExtensionSplitter( PATH, P1, TREE, P2, VALUE )
      => MerkleExtension( PATH, #merkleExtensionBrancher( MerkleUpdate( .MerkleBranch, P2, VALUE ), P1, TREE ) )
      requires #sizeByteArray(P2) ==Int 0

endmodule
```
