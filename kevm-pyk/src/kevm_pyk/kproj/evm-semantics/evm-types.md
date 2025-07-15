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
    imports WORD
    imports MINT
```

Machine Integers
----------------

We use 256-bit machine integers as our word data type.

```k
    syntax MInt{256}

    syntax MInt{256} ::= "pow160p256" [macro] /* 2^160 */
 // -----------------------------------------------------
    rule pow160p256 => 1461501637330902918203684832716283019655932542976p256

    syntax MInt{256} ::= "maxUInt64p256" [macro] /* 2^64 - 1 */
 // -----------------------------------------------------------
    rule maxUInt64p256 => 18446744073709551615p256

    syntax MInt{256} ::= "maxSInt256p256" [macro] /* 2^255 - 1 */
 // -------------------------------------------------------------
    rule maxSInt256p256 => 57896044618658097711785492504343953926634992332820282019728792003956564819967p256

    syntax MInt{256} ::= "maxUInt256p256" [macro] /* 2^256 - 1 */
 // -------------------------------------------------------------
    rule maxUInt256p256 => 115792089237316195423570985008687907853269984665640564039457584007913129639935p256

    syntax Bool ::= #rangeNonceMInt256( MInt{256} ) [alias]
 // -------------------------------------------------------
    rule #rangeNonceMInt256(X) => 0p256 <=uMInt X andBool X <uMInt maxUInt64p256

    syntax MInt{256} ::= #addrAsMInt256 ( MInt{256} ) [function]
 // ------------------------------------------------------------
    rule #addrAsMInt256(W)   => W %uMInt pow160p256

    syntax Bytes ::= "#writeMInt256" "(" Bytes "," MInt{256} "," MInt{256} ")" [function]
                   | Bytes "[" MInt{256} ":=MInt256" Bytes "]"                 [function]
 // -------------------------------------------------------------------------------------
    rule #writeMInt256(WM, IDX, VAL) => #let BYTES = padRightBytes(WM, IDX +MInt 1p256, 0p256) #in BYTES[ IDX <- VAL ]

    rule WS [ _     :=MInt256 WS' ] => WS                                                                                 requires lengthBytes(WS')  ==MInt 0p256
    rule WS [ START :=MInt256 WS' ] => replaceAtBytes(padRightBytes(WS, START +MInt lengthBytes(WS'), 0p256), START, WS') requires lengthBytes(WS') =/=MInt 0p256

    syntax Bytes ::= #rangeMInt256 ( Bytes , MInt{256} , MInt{256} ) [function]
 // ---------------------------------------------------------------------------
    rule #rangeMInt256(WS, START, WIDTH) => substrBytes(padRightBytes(WS, START +MInt WIDTH, 0p256), START, START +MInt WIDTH) requires START <uMInt lengthBytes(WS)
    rule #rangeMInt256( _,     _, WIDTH) => padRightBytes(.Bytes, WIDTH, 0p256) [owise]

    syntax MInt{256} ::= bool2MInt256 ( Bool ) [function]
 // -----------------------------------------------------
    rule bool2MInt256( true  ) => 1p256
    rule bool2MInt256( false ) => 0p256

    syntax Bool ::= mint2562Bool ( MInt{256} ) [function]
 // -----------------------------------------------------
    rule mint2562Bool( W ) => false requires W  ==MInt 0p256
    rule mint2562Bool( W ) => true  requires W =/=MInt 0p256

    syntax MInt{256} ::= #nBitsMInt256  ( MInt{256} )  [function]
                       | #nBytesMInt256 ( MInt{256} )  [function]
 // -------------------------------------------------------------
    rule #nBitsMInt256 (N) => (1p256 <<MInt N) -MInt 1p256
    rule #nBytesMInt256(N) => #nBitsMInt256(8p256 *MInt N)

    // returns the bit/byte at the given index, index 0 is the LSB
    syntax MInt{256} ::= bitOfMInt256 (MInt{256}, index: MInt{256}) [function]
    syntax MInt{256} ::= byteOfMInt256(MInt{256}, index: MInt{256}) [function]
 // --------------------------------------------------------------------------
    rule bitOfMInt256 (W, N) => ((#nBitsMInt256(1p256) <<MInt N) &MInt W) >>lMInt N
    rule byteOfMInt256(W, N) => ((#nBytesMInt256(1p256) <<MInt (8p256 *MInt N)) &MInt W) >>lMInt (8p256 *MInt N)

    syntax MInt{256} ::= bitMInt256  ( MInt{256} , MInt{256} ) [function]
                       | byteMInt256 ( MInt{256} , MInt{256} ) [function]
 // ---------------------------------------------------------------------
    rule bitMInt256 (N, _) => 0p256 requires N >=uMInt 256p256
    rule byteMInt256(N, _) => 0p256 requires N >=uMInt  32p256

    rule bitMInt256 (N, W) => bitOfMInt256 (W , (255p256 -MInt N)) requires N <uMInt 256p256
    rule byteMInt256(N, W) => byteOfMInt256(W , ( 31p256 -MInt N)) requires N <uMInt  32p256

    syntax MInt{256} ::= signextendMInt256( MInt{256} , MInt{256} ) [function]
 // --------------------------------------------------------------------------
    rule signextendMInt256(N, W) => W requires N >=uMInt 32p256
    rule signextendMInt256(N, W) => (#nBytesMInt256(31p256 -MInt N) <<MInt (8p256 *MInt (N +MInt 1p256))) |MInt W requires N <uMInt 32p256 andBool         mint2562Bool(bitMInt256(256p256 -MInt (8p256 *MInt (N +MInt 1p256)), W))
    rule signextendMInt256(N, W) => #nBytesMInt256(N +MInt 1p256)                                         &MInt W requires N <uMInt 32p256 andBool notBool mint2562Bool(bitMInt256(256p256 -MInt (8p256 *MInt (N +MInt 1p256)), W))

    syntax MInt{256} ::= addmodMInt256   ( MInt{256} , MInt{256}, MInt{256} ) [function]
    syntax MInt{256} ::= mulmodMInt256   ( MInt{256} , MInt{256}, MInt{256} ) [function]
    syntax MInt{256} ::= addmodMInt256Aux( MInt{256} , MInt{256}, MInt{256} ) [function]
    syntax MInt{256} ::= mulmodMInt256Aux( MInt{256} , MInt{256}, MInt{256} ) [function]
 // ------------------------------------------------------------------------------------
    rule addmodMInt256   ( _,  _, W2) => 0p256                                                                                                             requires W2 ==MInt 0p256
    rule addmodMInt256   (W0, W1, W2) => #let ADDRES = W0 +MInt W1 #in #if ADDRES <uMInt W0 #then addmodMInt256Aux(W0, W1, W2)  #else ADDRES %uMInt W2 #fi requires W2 =/=MInt 0p256

    rule mulmodMInt256   ( _,  _, W2) => 0p256                        requires W2 ==MInt 0p256
    rule mulmodMInt256   (W0, W1, W2) => mulmodMInt256Aux(W0, W1, W2) requires W2 =/=MInt 0p256

    rule addmodMInt256Aux(W0, W1, W2) => Int2MInt((MInt2Unsigned(W0) +Int MInt2Unsigned(W1)) modInt MInt2Unsigned(W2))::MInt{256}

    rule mulmodMInt256Aux(W0, W1, W2) => Int2MInt((MInt2Unsigned(W0) *Int MInt2Unsigned(W1)) modInt MInt2Unsigned(W2))::MInt{256}

    syntax Bool ::= inBoundsMInt256( MInt{256} , MInt{256}, MInt{256} ) [function]
 // ------------------------------------------------------------------------------
    rule inBoundsMInt256(S, W, L) =>
      #let R::MInt{256} = S +MInt W #in
      #if R <uMInt S #then false #else R <=uMInt L #fi
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

Bytes helper functions
----------------------

-   `#asWord` will interpret a stack of bytes as a single word (with MSB first).
-   `#asInteger` will interpret a stack of bytes as a single arbitrary-precision integer (with MSB first).
-   `#asAccount` will interpret a stack of bytes as a single account id (with MSB first).
    Differs from `#asWord` only in that an empty stack represents the empty account, not account zero.
-   `asAccountNotNil` will interpret a stack of bytes as a single account id (with MSB first), but will fail if the
    stack is empty.
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

    syntax Bytes ::= #asByteStack ( Int ) [symbol(#asByteStack), function, total]
 // -----------------------------------------------------------------------------
    rule #asByteStack(W) => Int2Bytes(W, BE, Unsigned) [concrete]

    syntax Bytes ::= #range ( Bytes , Int , Int ) [symbol(#range), function, total]
 // -------------------------------------------------------------------------------
    rule                #range(_, START, WIDTH)  => .Bytes                                                                       requires notBool (WIDTH >=Int 0 andBool START >=Int 0) [concrete]
    rule [bytesRange] : #range(WS, START, WIDTH) => substrBytes(padRightBytes(WS, START +Int WIDTH, 0), START, START +Int WIDTH) requires WIDTH >=Int 0 andBool START >=Int 0 andBool START <Int lengthBytes(WS) [concrete]
    rule                #range(_, _, WIDTH)      => padRightBytes(.Bytes, WIDTH, 0) [owise, concrete]

    syntax Bytes ::= #padToWidth      ( Int , Bytes ) [symbol(#padToWidth), function, total]
 // ----------------------------------------------------------------------------------------
    rule #padToWidth(N, BS)      =>               BS        requires notBool (0 <=Int N) [concrete]
    rule #padToWidth(N, BS)      =>  padLeftBytes(BS, N, 0) requires          0 <=Int N  [concrete]

    syntax Bool ::= Bytes "==Bytes" Bytes   [symbol(_==Bytes_), function, total]
    rule B1 ==Bytes B2 => B1 ==K B2
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
```

### Addresses

-   `#addr` turns an Ethereum word into the corresponding Ethereum address (160 LSB).

```k
    syntax Int ::= #addr ( Int ) [symbol(#addr), function, total]
 // -------------------------------------------------------------
    rule #addr(W) => W %Word pow160

endmodule
```
