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
    imports DOMAINS

    syntax KResult ::= Int
```

### JSON Formatting

The JSON format is used extensively for communication in the Ethereum circles.
Writing a JSON-ish parser in K takes 6 lines.

```k
    syntax JSONList ::= List{JSON,","}
    syntax JSONKey  ::= String | Int
    syntax JSON     ::= String
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
    syntax Int ::= "pow256" [function] /* 2 ^Int 256 */
                 | "pow255" [function] /* 2 ^Int 255 */
                 | "pow16"  [function] /* 2 ^Int 16  */
 // ---------------------------------------------------
    rule pow256 => 115792089237316195423570985008687907853269984665640564039457584007913129639936 [macro]
    rule pow255 => 57896044618658097711785492504343953926634992332820282019728792003956564819968  [macro]
    rule pow16  => 65536 [macro]
```

-   `chop` interperets an integer modulo $2^256$.

```k
    syntax Int ::= chop ( Int ) [function, smtlib(chop)]
 // ----------------------------------------------------
```

One common bug is integer overflow/underflow.
In normal execution, the wrapping of integers happens without raising any issue.

```{.k .not-bug-checker}
    rule chop ( I:Int ) => I modInt pow256 [concrete, smt-lemma]
```

When checking for bugs, execution only continues if overflow would not occur.

```{.k .bug-checker}
    rule chop ( I:Int ) => I requires I >=Int 0 andBool I <Int pow256
```

### Boolean Conversions

Primitives provide the basic conversion from K's sorts `Int` and `Bool` to EVM's words.

-   `bool2Word` interperets a `Bool` as a `Int`.
-   `word2Bool` interperets a `Int` as a `Bool`.

```k
    syntax Int ::= bool2Word ( Bool ) [function]
 // --------------------------------------------
    rule bool2Word( B:Bool ) => 1 requires B
    rule bool2Word( B:Bool ) => 0 requires notBool B

    syntax Bool ::= word2Bool ( Int ) [function]
 // --------------------------------------------
    rule word2Bool( 0 ) => false
    rule word2Bool( W ) => true  requires W =/=K 0
```

-   `sgn` gives the twos-complement interperetation of the sign of a word.
-   `abs` gives the twos-complement interperetation of the magnitude of a word.

```k
    syntax Int ::= sgn ( Int ) [function]
                 | abs ( Int ) [function]
 // -------------------------------------
    rule sgn(I) => -1 requires I >=Int pow255
    rule sgn(I) => 1  requires I <Int pow255

    rule abs(I) => 0 -Word I requires sgn(I) ==K -1
    rule abs(I) => I         requires sgn(I) ==K 1
```

### Empty Account

-   `.Account` represents the case when an account ID is referenced in the yellowpaper, but
    the actual value of the account ID is the empty set. This is used, for example, when
    referring to the destination of a message which creates a new contract.

```k
    syntax Account ::= ".Account" | Int
```

### Symbolic Words

-   `#symbolicWord` generates a fresh existentially-bound symbolic word.

```k
    syntax Int ::= "#symbolicWord" [function]
 // -----------------------------------------
    rule #symbolicWord => chop ( ?X:Int )
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

-   `logNInt` returns the log base N (floored) of an integer.

```k
    syntax Int ::= log2Int ( Int ) [function]
 // -----------------------------------------
    rule log2Int(1) => 0
    rule log2Int(W) => 1 +Int log2Int(W >>Int 1) requires W >Int 1

    syntax Int ::= log256Int ( Int ) [function]
 // -------------------------------------------
    rule log256Int(N) => log2Int(N) /Int 8
```

The corresponding `<op>Word` operations automatically perform the correct modulus for EVM words.

```k
    syntax Int ::= Int "+Word" Int [function]
                 | Int "*Word" Int [function]
                 | Int "-Word" Int [function]
                 | Int "/Word" Int [function]
                 | Int "%Word" Int [function]
 // -----------------------------------------
    rule W0 +Word W1 => chop( W0 +Int W1 )
    rule W0 -Word W1 => chop( W0 -Int W1 ) requires W0 >=Int W1
    rule W0 -Word W1 => chop( (W0 +Int pow256) -Int W1 ) requires W0 <Int W1
    rule W0 *Word W1 => chop( W0 *Int W1 )
    rule W0 /Word 0  => 0
    rule W0 /Word W1 => chop( W0 /Int W1 ) requires W1 =/=K 0
    rule W0 %Word 0  => 0
    rule W0 %Word W1 => chop( W0 modInt W1 ) requires W1 =/=K 0
```

Care is needed for `^Word` to avoid big exponentiation.
The helper `powmod` is a totalization of the operator `_^%Int__` (which comes with K).
`_^%Int__` is not defined when the modulus (third argument) is zero, but `powmod` is.

```k
    syntax Int ::= Int "^Word" Int       [function]
    syntax Int ::= powmod(Int, Int, Int) [function]
 // -----------------------------------------------
    rule W0 ^Word W1 => powmod(W0, W1, pow256)

    rule powmod(W0, W1, W2) => W0 ^%Int W1 W2 requires W2 =/=Int 0
    rule powmod(W0, W1, 0)  => 0
```

`/sWord` and `%sWord` give the signed interperetations of `/Word` and `%Word`.

```k
    syntax Int ::= Int "/sWord" Int [function]
                 | Int "%sWord" Int [function]
 // ------------------------------------------
    rule W0 /sWord W1 => #sgnInterp(sgn(W0) *Int sgn(W1) , abs(W0) /Word abs(W1))
    rule W0 %sWord W1 => #sgnInterp(sgn(W0)              , abs(W0) %Word abs(W1))

    syntax Int ::= #sgnInterp ( Int , Int ) [function]
 // --------------------------------------------------
    rule #sgnInterp( 0  , W1 ) => 0
    rule #sgnInterp( W0 , W1 ) => W1         requires W0 >Int 0
    rule #sgnInterp( W0 , W1 ) => 0 -Word W1 requires W0 <Int 0
```

### Word Comparison

The `<op>Word` comparisons similarly lift K operators to EVM ones:

```k
    syntax Int ::= Int "<Word"  Int [function]
                 | Int ">Word"  Int [function]
                 | Int "<=Word" Int [function]
                 | Int ">=Word" Int [function]
                 | Int "==Word" Int [function]
 // ------------------------------------------
    rule W0 <Word  W1 => bool2Word(W0 <Int  W1)
    rule W0 >Word  W1 => bool2Word(W0 >Int  W1)
    rule W0 <=Word W1 => bool2Word(W0 <=Int W1)
    rule W0 >=Word W1 => bool2Word(W0 >=Int W1)
    rule W0 ==Word W1 => bool2Word(W0 ==Int W1)
```

-   `s<Word` implements a less-than for `Word` (with signed interperetation).

```k
    syntax Int ::= Int "s<Word" Int [function]
 // ------------------------------------------
    rule W0 s<Word W1 => W0 <Word W1           requires sgn(W0) ==K 1  andBool sgn(W1) ==K 1
    rule W0 s<Word W1 => bool2Word(false)      requires sgn(W0) ==K 1  andBool sgn(W1) ==K -1
    rule W0 s<Word W1 => bool2Word(true)       requires sgn(W0) ==K -1 andBool sgn(W1) ==K 1
    rule W0 s<Word W1 => abs(W1) <Word abs(W0) requires sgn(W0) ==K -1 andBool sgn(W1) ==K -1
```

### Bitwise Operators

Bitwise logical operators are lifted from the integer versions.

```k
    syntax Int ::= "~Word" Int       [function]
                 | Int "|Word"   Int [function]
                 | Int "&Word"   Int [function]
                 | Int "xorWord" Int [function]
 // -------------------------------------------
    rule ~Word W       => chop( W xorInt (pow256 -Int 1) )
    rule W0 |Word   W1 => chop( W0 |Int W1 )
    rule W0 &Word   W1 => chop( W0 &Int W1 )
    rule W0 xorWord W1 => chop( W0 xorInt W1 )
```

-   `bit` gets bit $N$ (0 being MSB).
-   `byte` gets byte $N$ (0 being the MSB).

```k
    syntax Int ::= bit  ( Int , Int ) [function]
                 | byte ( Int , Int ) [function]
 // --------------------------------------------
    rule bit(N, _)  => 0 requires N <Int 0 orBool N >=Int 256
    rule byte(N, _) => 0 requires N <Int 0 orBool N >=Int 32

    rule bit(N, W)  => (W >>Int (255 -Int N)) modInt 2                     requires N >=Int 0 andBool N <Int 256
    rule byte(N, W) => (W >>Int (256 -Int (8 *Int (N +Int 1)))) modInt 256 requires N >=Int 0 andBool N <Int 32
```

-   `#nBits` shifts in $N$ ones from the right.
-   `#nBytes` shifts in $N$ bytes of ones from the right.
-   `_<<Byte_` shifts an integer 8 bits to the left.

```k
    syntax Int ::= #nBits  ( Int )  [function]
                 | #nBytes ( Int )  [function]
                 | Int "<<Byte" Int [function]
 // ------------------------------------------
    rule #nBits(N)  => (1 <<Int N) -Int 1  requires N >=Int 0
    rule #nBytes(N) => #nBits(N *Int 8)   requires N >=Int 0
    rule N <<Byte M => N <<Int (8 *Int M)
```

-   `signextend(N, W)` sign-extends from byte $N$ of $W$ (0 being MSB).

```k
    syntax Int ::= signextend( Int , Int ) [function]
 // -------------------------------------------------
    rule signextend(N, W) => W requires N >=Int 32 orBool N <Int 0
    rule signextend(N, W) => chop( (#nBytes(31 -Int N) <<Byte (N +Int 1)) |Int W ) requires N <Int 32 andBool N >=Int 0 andBool         word2Bool(bit(256 -Int (8 *Int (N +Int 1)), W))
    rule signextend(N, W) => chop( #nBytes(N +Int 1)                      &Int W ) requires N <Int 32 andBool N >=Int 0 andBool notBool word2Bool(bit(256 -Int (8 *Int (N +Int 1)), W))
```

-   `keccak` serves as a wrapper around the `Keccak256` in `KRYPTO`.

```k
    syntax Int ::= keccak ( WordStack ) [function, smtlib(smt_keccak)]
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
    syntax WordStack ::= ".WordStack" | Int ":" WordStack
 // -----------------------------------------------------
```

-   `_++_` acts as `WordStack` append.
-   `#take(N , WS)` keeps the first $N$ elements of a `WordStack` (passing with zeros as needed).
-   `#drop(N , WS)` removes the first $N$ elements of a `WordStack`.

```k
    syntax WordStack ::= WordStack "++" WordStack [function, right]
 // ---------------------------------------------------------------
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

### Element Access

-   `WS [ N ]` accesses element $N$ of $WS$.
-   `WS [ N .. W ]` access the range of `WS` beginning with `N` of width `W`.
-   `WS [ N := W ]` sets element $N$ of $WS$ to $W$ (padding with zeros as needed).

```k
    syntax Int ::= WordStack "[" Int "]" [function]
 // -----------------------------------------------
    rule (W0 : WS)   [0] => W0
    rule (.WordStack)[N] => 0            requires N >Int 0
    rule (W0 : WS)   [N] => WS[N -Int 1] requires N >Int 0

    syntax WordStack ::= WordStack "[" Int ".." Int "]" [function]
 // --------------------------------------------------------------
    rule WS [ START .. WIDTH ] => #take(WIDTH, #drop(START, WS))

    syntax WordStack ::= WordStack "[" Int ":=" Int "]" [function]
 // --------------------------------------------------------------
    rule (W0 : WS)  [ 0 := W ] => W  : WS
    rule .WordStack [ N := W ] => 0  : (.WordStack [ N -Int 1 := W ]) requires N >Int 0
    rule (W0 : WS)  [ N := W ] => W0 : (WS [ N -Int 1 := W ])         requires N >Int 0
```

-   `#sizeWordStack` calculates the size of a `WordStack`.
-   `_in_` determines if a `Int` occurs in a `WordStack`.

```k
    syntax Int ::= #sizeWordStack ( WordStack )       [function, smtlib(sizeWordStack)]
                 | #sizeWordStack ( WordStack , Int ) [function, klabel(sizeWordStackAux), smtlib(sizeWordStackAux)]
 // ----------------------------------------------------------------------------------------------------------------
    rule #sizeWordStack ( WS ) => #sizeWordStack(WS, 0)
    rule #sizeWordStack ( .WordStack, SIZE ) => SIZE
    rule #sizeWordStack ( W : WS, SIZE )     => #sizeWordStack(WS, SIZE +Int 1)

    syntax Bool ::= Int "in" WordStack [function]
 // ---------------------------------------------
    rule W in .WordStack => false
    rule W in (W' : WS)  => (W ==K W') orElseBool (W in WS)
```

-   `#padToWidth(N, WS)` makes sure that a `WordStack` is the correct size.

```k
    syntax WordStack ::= #padToWidth ( Int , WordStack ) [function]
 // ---------------------------------------------------------------
    rule #padToWidth(N, WS) => WS                     requires notBool #sizeWordStack(WS) <Int N [concrete]
    rule #padToWidth(N, WS) => #padToWidth(N, 0 : WS) requires #sizeWordStack(WS) <Int N         [concrete]
```

-   `WordStack2List` converts a term of sort `WordStack` to a term of sort `List`.

```k
    syntax List ::= WordStack2List ( WordStack ) [function]
 // -------------------------------------------------------
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
-   `#asByteStack` will split a single word up into a `WordStack` where each word is a byte wide.

```k
    syntax Int ::= #asWord ( WordStack ) [function, smtlib(asWord)]
 // ---------------------------------------------------------------
    rule #asWord( .WordStack     ) => 0                                    // [concrete]
    rule #asWord( W : .WordStack ) => W                                    // [concrete]
    rule #asWord( W0 : W1 : WS   ) => #asWord(((W0 *Word 256) +Word W1) : WS) [concrete]

    syntax Int ::= #asInteger ( WordStack ) [function]
 // --------------------------------------------------
    rule #asInteger( .WordStack     ) => 0
    rule #asInteger( W : .WordStack ) => W
    rule #asInteger( W0 : W1 : WS   ) => #asInteger(((W0 *Int 256) +Int W1) : WS)

    syntax Account ::= #asAccount ( WordStack ) [function]
 // ------------------------------------------------------
    rule #asAccount( .WordStack ) => .Account
    rule #asAccount( W : WS     ) => #asWord(W : WS)

    syntax WordStack ::= #asByteStack ( Int )             [function]
                       | #asByteStack ( Int , WordStack ) [function, klabel(#asByteStackAux), smtlib(asByteStack)]
 // --------------------------------------------------------------------------------------------------------------
    rule #asByteStack( W ) => #asByteStack( W , .WordStack )                                        [concrete]
    rule #asByteStack( 0 , WS ) => WS                                                            // [concrete]
    rule #asByteStack( W , WS ) => #asByteStack( W /Int 256 , W modInt 256 : WS ) requires W =/=K 0 [concrete]
```

Addresses
---------

-   `#addr` turns an Ethereum word into the corresponding Ethereum address (160 LSB).

```k
    syntax Int ::= #addr ( Int ) [function]
 // ---------------------------------------
    rule #addr(W) => W %Word (2 ^Word 160)
```

-   `#newAddr` computes the address of a new account given the address and nonce of the creating account.
-   `#sender` computes the sender of the transaction from its data and signature.

```k
    syntax Int ::= #newAddr ( Int , Int ) [function]
 // ------------------------------------------------
    rule #newAddr(ACCT, NONCE) => #addr(#parseHexWord(Keccak256(#rlpEncodeLength(#rlpEncodeBytes(ACCT, 20) +String #rlpEncodeWord(NONCE), 192))))

    syntax Int ::= #sender ( Int , Int , Int , Account , Int , String , Int , WordStack , WordStack ) [function]
                 | #sender ( String , Int , String , String )                                         [function, klabel(#senderAux)]
                 | #sender ( String )                                                                 [function, klabel(#senderAux2)]
 // ---------------------------------------------------------------------------------------------------------------------------------
    rule #sender(TN, TP, TG, TT, TV, DATA, TW, TR, TS)
      => #sender(#unparseByteStack(#parseHexBytes(Keccak256(#rlpEncodeLength(#rlpEncodeWordStack(TN : TP : TG : .WordStack) +String #rlpEncodeAccount(TT) +String #rlpEncodeWord(TV) +String #rlpEncodeString(DATA), 192)))), TW, #unparseByteStack(TR), #unparseByteStack(TS))

    rule #sender(HT, TW, TR, TS) => #sender(ECDSARecover(HT, TW, TR, TS))

    rule #sender("")  => .Account
    rule #sender(STR) => #addr(#parseHexWord(Keccak256(STR))) requires STR =/=String ""
```

-   `#blockHeaderHash` computes the hash of a block header given all the block data.

```k
    syntax Int ::= #blockHeaderHash( Int , Int , Int , Int , Int , Int , WordStack , Int , Int , Int , Int , Int , WordStack , Int , Int ) [function]
                 | #blockHeaderHash(String, String, String, String, String, String, String, String, String, String, String, String, String, String, String) [function, klabel(#blockHashHeaderStr)]
 // -----------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------
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

Word Map
--------

Most of EVM data is held in finite maps.
We are using the polymorphic `Map` sort for these word maps.

-   `WM [ N := WS ]` assigns a contiguous chunk of $WM$ to $WS$ starting at position $W$.
-   `#asMapWordStack` converts a `WordStack` to a `Map`.
-   `#range(M, START, WIDTH)` reads off $WIDTH$ elements from $WM$ beginning at position $START$ (padding with zeros as needed).

```k
    syntax Map ::= Map "[" Int ":=" WordStack "]" [function]
 // --------------------------------------------------------
    rule WM[ N := .WordStack ] => WM
    rule WM[ N := W : WS     ] => (WM[N <- W])[N +Int 1 := WS]

    syntax Map ::= #asMapWordStack ( WordStack ) [function]
 // -------------------------------------------------------
    rule #asMapWordStack(WS:WordStack) => .Map [ 0 := WS ]

    syntax WordStack ::= #range ( Map , Int , Int )            [function]
    syntax WordStack ::= #range ( Map , Int , Int , WordStack) [function, klabel(#rangeAux)]
 // ----------------------------------------------------------------------------------------
    rule #range(WM, START, WIDTH) => #range(WM, START +Int WIDTH -Int 1, WIDTH, .WordStack)

    rule #range(WM,           END, 0,     WS) => WS
    rule #range(WM,           END, WIDTH, WS) => #range(WM, END -Int 1, WIDTH -Int 1, 0 : WS) requires (WIDTH >Int 0) andBool notBool END in_keys(WM)
    rule #range(END |-> W WM, END, WIDTH, WS) => #range(WM, END -Int 1, WIDTH -Int 1, W : WS) requires (WIDTH >Int 0)
```

-   `#removeZeros` removes any entries in a map with zero values.

```k
    syntax Map ::= #removeZeros ( Map ) [function]
 // ----------------------------------------------
    rule #removeZeros( .Map )               => .Map
    rule #removeZeros( KEY |-> 0     REST ) => #removeZeros(REST)
    rule #removeZeros( KEY |-> VALUE REST ) => KEY |-> VALUE #removeZeros(REST) requires VALUE =/=K 0
```

-   `#lookup` looks up a key in a map and returns 0 if the key doesn't exist, otherwise returning its value.

```k
    syntax Int ::= #lookup ( Map , Int ) [function]
 // -----------------------------------------------
    rule #lookup( (KEY |-> VAL) M, KEY ) => VAL
    rule #lookup(               M, KEY ) => 0 requires notBool KEY in_keys(M)
```

Parsing/Unparsing
=================

The EVM test-sets are represented in JSON format with hex-encoding of the data and programs.
Here we provide some standard parser/unparser functions for that format.

Parsing
-------

These parsers can interperet hex-encoded strings as `Int`s, `WordStack`s, and `Map`s.

-   `#parseHexWord` interperets a string as a single hex-encoded `Word`.
-   `#parseHexBytes` interperets a string as a hex-encoded stack of bytes.
-   `#parseByteStack` interperets a string as a hex-encoded stack of bytes, but makes sure to remove the leading "0x".
-   `#parseByteStackRaw` inteprets a string as a stack of bytes.
-   `#parseWordStack` interperets a JSON list as a stack of `Word`.
-   `#parseMap` interperets a JSON key/value object as a map from `Word` to `Word`.
-   `#parseAddr` interperets a string as a 160 bit hex-endcoded address.

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

    syntax WordStack ::= #parseHexBytes  ( String ) [function]
                       | #parseByteStack ( String ) [function]
                       | #parseByteStackRaw ( String ) [function]
 // ----------------------------------------------------------
    rule #parseByteStack(S) => #parseHexBytes(replaceAll(S, "0x", ""))
    rule #parseHexBytes("") => .WordStack
    rule #parseHexBytes(S)  => #parseHexWord(substrString(S, 0, 2)) : #parseHexBytes(substrString(S, 2, lengthString(S))) requires lengthString(S) >=Int 2

    rule #parseByteStackRaw(S) => ordChar(substrString(S, 0, 1)) : #parseByteStackRaw(substrString(S, 1, lengthString(S))) requires lengthString(S) >=Int 1
    rule #parseByteStackRaw("") => .WordStack

    syntax WordStack ::= #parseWordStack ( JSON ) [function]
 // --------------------------------------------------------
    rule #parseWordStack( [ .JSONList ] )            => .WordStack
    rule #parseWordStack( [ (WORD:String) , REST ] ) => #parseHexWord(WORD) : #parseWordStack( [ REST ] )

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

We need to interperet a `WordStack` as a `String` again so that we can call `Keccak256` on it from `KRYPTO`.

-   `#unparseByteStack` turns a stack of bytes (as a `WordStack`) into a `String`.
-   `#padByte` ensures that the `String` interperetation of a `Int` is wide enough.

```k
    syntax String ::= #unparseByteStack ( WordStack )                [function, klabel(unparseByteStack)]
                    | #unparseByteStack ( WordStack , StringBuffer ) [function, klabel(#unparseByteStackAux)]
 // ---------------------------------------------------------------------------------------------------------
    rule #unparseByteStack ( WS ) => #unparseByteStack(WS, .StringBuffer)

    rule #unparseByteStack( .WordStack, BUFFER ) => StringBuffer2String(BUFFER)
    rule #unparseByteStack( W : WS, BUFFER )     => #unparseByteStack(WS, BUFFER +String chrChar(W modInt (2 ^Int 8)))

    syntax String ::= #padByte( String ) [function]
 // -----------------------------------------------
    rule #padByte( S ) => S             requires lengthString(S) ==K 2
    rule #padByte( S ) => "0" +String S requires lengthString(S) ==K 1
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
endmodule
```
