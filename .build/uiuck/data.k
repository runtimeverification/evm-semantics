// EVM Words
// =========

// EVM uses bounded 256 bit integer words, and sometimes also bytes (8 bit words).
// Here we provide the arithmetic of these words, as well as some data-structures
// over them. Both are implemented using K's `Int`.


requires "krypto.k"
requires "domains.k"

module EVM-DATA
    imports KRYPTO
    imports STRING-BUFFER

    syntax KResult ::= Int


// Some important numbers that are referred to often during execution:


    syntax Int ::= "pow256" [function]
                 | "pow255" [function]
                 | "pow16"  [function]
 // ----------------------------------
    rule pow256 => 2 ^Int 256
    rule pow255 => 2 ^Int 255
    rule pow16  => 2 ^Int 16


// The JSON format is used extensively for communication in the Ethereum circles.
// Writing a JSON-ish parser in K takes 6 lines.


    syntax JSONList ::= List{JSON,","}
    syntax JSONKey  ::= String | Int
    syntax JSON     ::= String
                      | JSONKey ":" JSON
                      | "{" JSONList "}"
                      | "[" JSONList "]"
 // ------------------------------------


// Primitives
// ----------

// Primitives provide the basic conversion from K's sorts `Int` and `Bool` to EVM's
// words.

// -   `chop` interperets an integers modulo $2^256$.


    syntax Int ::= chop ( Int ) [function]
 // --------------------------------------
    rule chop ( I:Int ) => I %Int pow256 requires I <Int 0  orBool I >=Int pow256
    rule chop ( I:Int ) => I             requires I >=Int 0 andBool I <Int pow256


// -   `bool2Word` interperets a `Bool` as a `Int`.
// -   `word2Bool` interperets a `Int` as a `Bool`.


    syntax Int ::= bool2Word ( Bool ) [function]
 // --------------------------------------------
    rule bool2Word(true)  => 1
    rule bool2Word(false) => 0

    syntax Bool ::= word2Bool ( Int ) [function]
 // --------------------------------------------
    rule word2Bool( 0 ) => false
    rule word2Bool( W ) => true  requires W =/=K 0


// -   `#ifInt_#then_#else_#fi` provides a conditional in `Int` expressions.


    syntax Int ::= "#ifInt" Bool "#then" Int "#else" Int "#fi" [function, smtlib(ifInt)]
 // ------------------------------------------------------------------------------------


// If we don't place the `Bool` condition as a side-condition for UIUC-K, it will
// attempt to only do an "implies-check" instead of full unification (which is
// problematic when `B` is symbolic during proving).


    rule #ifInt B #then W #else _ #fi => W requires B
    rule #ifInt B #then _ #else W #fi => W requires notBool B


// -   `sgn` gives the twos-complement interperetation of the sign of a word.
// -   `abs` gives the twos-complement interperetation of the magnitude of a word.


    syntax Int ::= sgn ( Int ) [function]
                 | abs ( Int ) [function]
 // -------------------------------------
    rule sgn(I) => -1 requires I >=Int pow255
    rule sgn(I) => 1  requires I <Int pow255

    rule abs(I) => 0 -Word I requires sgn(I) ==K -1
    rule abs(I) => I         requires sgn(I) ==K 1


// ### Symbolic Words

// -   `#symbolicWord` generates a fresh existentially-bound symbolic word.

// Note: Comment out this block (remove the `k` tag) if using RV K.


    syntax Int ::= "#symbolicWord" [function]
 // -----------------------------------------
    rule #symbolicWord => ?X:Int requires ?X >=Int 0 andBool ?X <=Int pow256


// Arithmetic
// ----------

// -   `up/Int` performs integer division but rounds up instead of down.

// NOTE: Here, we choose to add `I2 -Int 1` to the numerator beforing doing the
// division to mimic the C++ implementation. You could alternatively calculate
// `I1 %Int I2`, then add one to the normal integer division afterward depending on
// the result.


    syntax Int ::= Int "up/Int" Int [function]
 // ------------------------------------------
    rule I1 up/Int 0  => 0
    rule I1 up/Int 1  => I1
    rule I1 up/Int I2 => (I1 +Int (I2 -Int 1)) /Int I2 requires I2 >Int 1


// -   `logNInt` returns the log base N (floored) of an integer.


    syntax Int ::= log2Int ( Int ) [function]
 // -----------------------------------------
    rule log2Int(1) => 0
    rule log2Int(W) => 1 +Int log2Int(W >>Int 1) requires W >Int 1

    syntax Int ::= log256Int ( Int ) [function]
 // -------------------------------------------
    rule log256Int(N) => log2Int(N) /Int 8


// The corresponding `<op>Word` operations automatically perform the correct
// modulus for EVM words.


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
    rule W0 %Word W1 => chop( W0 %Int W1 ) requires W1 =/=K 0


// Care is needed for `^Word` to avoid big exponentiation.


    syntax Int ::= Int "^Word" Int [function]
 // -----------------------------------------
    rule W0 ^Word W1 => (W0 ^Word (W1 /Int 2)) ^Word 2  requires W1 >=Int pow16 andBool W1 %Int 2 ==Int 0
    rule W0 ^Word W1 => (W0 ^Word (W1 -Int 1)) *Word W0 requires W1 >=Int pow16 andBool W1 %Int 2 ==Int 1


// RV-K has a more efficient power-modulus operator.


    rule W0 ^Word W1 => (W0 ^Int W1) %Int pow256 requires W1 <Int pow16


// `/sWord` and `%sWord` give the signed interperetations of `/Word` and `%Word`.


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


// Comparison Operators
// --------------------

// The `<op>Word` comparison operators automatically interperet the `Bool` as a
// `Word`.


    syntax Int ::= Int "<Word"  Int [function]
                 | Int ">Word"  Int [function]
                 | Int "<=Word" Int [function]
                 | Int ">=Word" Int [function]
                 | Int "==Word" Int [function]
 // ------------------------------------------
    rule W0 <Word  W1 => 1 requires W0 <Int   W1
    rule W0 <Word  W1 => 0 requires W0 >=Int  W1
    rule W0 >Word  W1 => 1 requires W0 >Int   W1
    rule W0 >Word  W1 => 0 requires W0 <=Int  W1
    rule W0 <=Word W1 => 1 requires W0 <=Int  W1
    rule W0 <=Word W1 => 0 requires W0 >Int   W1
    rule W0 >=Word W1 => 1 requires W0 >=Int  W1
    rule W0 >=Word W1 => 0 requires W0 <Int   W1
    rule W0 ==Word W1 => 1 requires W0 ==Int  W1
    rule W0 ==Word W1 => 0 requires W0 =/=Int W1


// -   `s<Word` implements a less-than for `Word` (with signed interperetation).


    syntax Int ::= Int "s<Word" Int [function]
 // ------------------------------------------
    rule W0 s<Word W1 => W0 <Word W1           requires sgn(W0) ==K 1  andBool sgn(W1) ==K 1
    rule W0 s<Word W1 => bool2Word(false)      requires sgn(W0) ==K 1  andBool sgn(W1) ==K -1
    rule W0 s<Word W1 => bool2Word(true)       requires sgn(W0) ==K -1 andBool sgn(W1) ==K 1
    rule W0 s<Word W1 => abs(W1) <Word abs(W0) requires sgn(W0) ==K -1 andBool sgn(W1) ==K -1


// Bitwise Operators
// -----------------

// Bitwise logical operators are lifted from the integer versions.


    syntax Int ::= "~Word" Int       [function]
                 | Int "|Word"   Int [function]
                 | Int "&Word"   Int [function]
                 | Int "xorWord" Int [function]
 // -------------------------------------------
    rule ~Word W       => chop( W xorInt (pow256 -Int 1) )
    rule W0 |Word   W1 => chop( W0 |Int W1 )
    rule W0 &Word   W1 => chop( W0 &Int W1 )
    rule W0 xorWord W1 => chop( W0 xorInt W1 )


// -   `bit` gets bit $N$ (0 being MSB).
// -   `byte` gets byte $N$ (0 being the MSB).


    syntax Int ::= bit  ( Int , Int ) [function]
                 | byte ( Int , Int ) [function]
 // --------------------------------------------
    rule bit(N, _)  => 0 requires N <Int 0 orBool N >=Int 256
    rule byte(N, _) => 0 requires N <Int 0 orBool N >=Int 32

    rule bit(N, W)  => (W >>Int (255 -Int N)) %Int 2                     requires N >=Int 0 andBool N <Int 256
    rule byte(N, W) => (W >>Int (256 -Int (8 *Int (N +Int 1)))) %Int 256 requires N >=Int 0 andBool N <Int 32


// -   `#nBits` shifts in $N$ ones from the right.
// -   `#nBytes` shifts in $N$ bytes of ones from the right.
// -   `_<<Byte_` shifts an integer 8 bits to the left.


    syntax Int ::= #nBits  ( Int )  [function]
                 | #nBytes ( Int )  [function]
                 | Int "<<Byte" Int [function]
 // ------------------------------------------
    rule #nBits(N)  => (1 <<Int N) -Int 1  requires N >=Int 0
    rule #nBytes(N) => #nBits(N *Int 8)   requires N >=Int 0
    rule N <<Byte M => N <<Int (8 *Int M)


// -   `signextend(N, W)` sign-extends from byte $N$ of $W$ (0 being MSB).


    syntax Int ::= signextend( Int , Int ) [function]
 // -------------------------------------------------
    rule signextend(N, W) => W requires N >=Int 32 orBool N <Int 0
    rule signextend(N, W) => chop( (#nBytes(31 -Int N) <<Byte (N +Int 1)) |Int W ) requires N <Int 32 andBool N >=Int 0 andBool         word2Bool(bit(256 -Int (8 *Int (N +Int 1)), W))
    rule signextend(N, W) => chop( #nBytes(N +Int 1)                      &Int W ) requires N <Int 32 andBool N >=Int 0 andBool notBool word2Bool(bit(256 -Int (8 *Int (N +Int 1)), W))


// -   `keccak` serves as a wrapper around the `Keccak256` in `KRYPTO`.


    syntax Int ::= keccak ( WordStack ) [function]
 // ----------------------------------------------
    rule keccak(WS) => #parseHexWord(Keccak256(#unparseByteStack(WS)))


// Data Structures
// ===============

// Several data-structures and operations over `Int` are useful to have around.

// Word Stack
// ----------

// EVM is a stack machine, and so needs a stack of words to operate on. The stack
// and some standard operations over it are provided here. This stack also serves
// as a cons-list, so we provide some standard cons-list manipulation tools.


    syntax WordStack ::= ".WordStack" | Int ":" WordStack
 // -----------------------------------------------------


// -   `_++_` acts as `WordStack` append.
// -   `#take(N , WS)` keeps the first $N$ elements of a `WordStack` (passing with
//     zeros as needed).
// -   `#drop(N , WS)` removes the first $N$ elements of a `WordStack`.
// -   `WS [ N .. W ]` access the range of `WS` beginning with `N` of width `W`.


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

    syntax WordStack ::= WordStack "[" Int ".." Int "]" [function]
 // --------------------------------------------------------------
    rule WS [ START .. WIDTH ] => #take(WIDTH, #drop(START, WS))


// -   `WS [ N ]` accesses element $N$ of $WS$.
// -   `WS [ N := W ]` sets element $N$ of $WS$ to $W$ (padding with zeros
//     as needed).


    syntax Int ::= WordStack "[" Int "]" [function]
 // -----------------------------------------------
    rule (W0 : WS)   [0] => W0
    rule (.WordStack)[N] => 0            requires N >Int 0
    rule (W0 : WS)   [N] => WS[N -Int 1] requires N >Int 0

    syntax WordStack ::= WordStack "[" Int ":=" Int "]" [function]
 // --------------------------------------------------------------
    rule (W0 : WS)  [ 0 := W ] => W  : WS
    rule .WordStack [ N := W ] => 0  : (.WordStack [ N -Int 1 := W ]) requires N >Int 0
    rule (W0 : WS)  [ N := W ] => W0 : (WS [ N -Int 1 := W ])         requires N >Int 0


// -   `#sizeWordStack` calculates the size of a `WordStack`.
// -   `_in_` determines if a `Int` occurs in a `WordStack`.


    syntax Int ::= #sizeWordStack ( WordStack )  [function, smtlib(sizeWordStack)]
 // ------------------------------------------------------------------------------
    rule #sizeWordStack ( .WordStack ) => 0
    rule #sizeWordStack ( W : WS )     => 1 +Int #sizeWordStack(WS)

    syntax Bool ::= Int "in" WordStack [function]
 // ---------------------------------------------
    rule W in .WordStack => false
    rule W in (W' : WS)  => (W ==K W') orElseBool (W in WS)


// -   `#padToWidth(N, WS)` makes sure that a `WordStack` is the correct size.


    syntax WordStack ::= #padToWidth ( Int , WordStack ) [function]
 // ---------------------------------------------------------------
    rule #padToWidth(N, WS) => WS                     requires notBool #sizeWordStack(WS) <Int N
    rule #padToWidth(N, WS) => #padToWidth(N, 0 : WS) requires #sizeWordStack(WS) <Int N


// Byte Arrays
// -----------

// The local memory of execution is a byte-array (instead of a word-array).

// -   `#asWord` will interperet a stack of bytes as a single word (with
//     MSB first).
// -   `#asByteStack` will split a single word up into a `WordStack` where each
//     word is a byte wide.


    syntax Int ::= #asWord ( WordStack ) [function, smtlib(asWord)]
 // ---------------------------------------------------------------
    rule #asWord( .WordStack )    => 0
    rule #asWord( W : .WordStack) => W
    rule #asWord( W0 : W1 : WS )  => #asWord(((W0 *Word 256) +Word W1) : WS)

    syntax WordStack ::= #asByteStack ( Int )             [function]
                       | #asByteStack ( Int , WordStack ) [function, klabel(#asByteStackAux), smtlib(asByteStack)]
 // --------------------------------------------------------------------------------------------------------------
    rule #asByteStack( W ) => #asByteStack( W , .WordStack )
    rule #asByteStack( 0 , WS ) => WS
    rule #asByteStack( W , WS ) => #asByteStack( W /Int 256 , W %Int 256 : WS ) requires W =/=K 0


// Addresses
// ---------

// -   `#addr` turns an Ethereum word into the corresponding Ethereum address
//     (160 LSB).


    syntax Int ::= #addr ( Int ) [function]
 // ---------------------------------------
    rule #addr(W) => W %Word (2 ^Word 160)


// -   `#newAddr` computes the address of a new account given the address and nonce
//     of the creating account.
// -   `#sender` computes the sender of the transaction from its data
//     and signature.


    syntax Int ::= #newAddr ( Int , Int ) [function]
 // ------------------------------------------------
    rule #newAddr(ACCT, NONCE) => #addr(#parseHexWord(Keccak256(#rlpEncodeLength(#rlpEncodeWord(ACCT) +String #rlpEncodeWord(NONCE), 192))))

    syntax Int ::= #sender ( Int , Int , Int , Int , Int , String , Int , WordStack , WordStack ) [function]
                 | #sender ( String , Int , String , String )                                     [function, klabel(#senderAux)]
 // ----------------------------------------------------------------------------------------------------------------------------
    rule #sender(TN, TP, TG, TT, TV, DATA, TW, TR, TS)
      => #sender(#unparseByteStack(#parseHexBytes(Keccak256(#rlpEncodeLength(#rlpEncodeWordStack(TN : TP : TG : TT : TV : .WordStack) +String #rlpEncodeString(DATA), 192)))), TW, #unparseByteStack(TR), #unparseByteStack(TS))

    rule #sender(HT, TW, TR, TS) => #addr(#parseHexWord(Keccak256(ECDSARecover(HT, TW, TR, TS))))


// -   `#blockHeaderHash` computes the hash of a block header given all the
//     block data.


    syntax Int ::= #blockHeaderHash( Int , Int , Int , Int , Int , Int , WordStack , Int , Int , Int , Int , Int , WordStack , Int , Int ) [function]
 // -------------------------------------------------------------------------------------------------------------------------------------------------
    rule #blockHeaderHash(HP, HO, HC, HR, HT, HE, HB, HD, HI, HL, HG, HS, HX, HM, HN)
         => #parseHexWord(Keccak256(#rlpEncodeLength(         #rlpEncodeWordStack(HP : HO : HC : HR : HT : HE : .WordStack)
                                                      +String #rlpEncodeString(#unparseByteStack(HB))
                                                      +String #rlpEncodeWordStack(HD : HI : HL : HG : HS : .WordStack)
                                                      +String #rlpEncodeString(#unparseByteStack(HX))
                                                      +String #rlpEncodeWordStack(HM : HN : .WordStack)
                                                    , 192
                                                    )))


// Word Map
// --------

// Most of EVM data is held in finite maps. We are using the polymorphic `Map` sort
// for these word maps.

// -   `WM [ N := WS ]` assigns a contiguous chunk of $WM$ to $WS$ starting at
//     position $W$.
// -   `#asMapWordStack` converts a `WordStack` to a `Map`.
// -   `#range(M, START, WIDTH)` reads off $WIDTH$ elements from $WM$ beginning at
//     position $START$ (padding with zeros as needed).


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


// -   `#removeZeros` removes any entries in a map with zero values.


    syntax Map ::= #removeZeros ( Map ) [function]
 // ----------------------------------------------
    rule #removeZeros( .Map )               => .Map
    rule #removeZeros( KEY |-> 0     REST ) => #removeZeros(REST)
    rule #removeZeros( KEY |-> VALUE REST ) => KEY |-> VALUE #removeZeros(REST) requires VALUE =/=K 0


// Parsing/Unparsing
// =================

// The EVM test-sets are represented in JSON format with hex-encoding of the data
// and programs. Here we provide some standard parser/unparser functions for that
// format.

// Parsing
// -------

// These parsers can interperet hex-encoded strings as `Int`s, `WordStack`s, and
// `Map`s.

// -   `#parseHexWord` interperets a string as a single hex-encoded `Word`.
// -   `#parseHexBytes` interperets a string as a hex-encoded stack of bytes.
// -   `#parseByteStack` interperets a string as a hex-encoded stack of bytes, but
//     makes sure to remove the leading "0x".
// -   `#parseByteStackRaw` inteprets a string as a stack of bytes.
// -   `#parseWordStack` interperets a JSON list as a stack of `Word`.
// -   `#parseMap` interperets a JSON key/value object as a map from `Word` to
//     `Word`.
// -   `#parseAddr` interperets a string as a 160 bit hex-endcoded address.


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


// Unparsing
// ---------

// We need to interperet a `WordStack` as a `String` again so that we can call
// `Keccak256` on it from `KRYPTO`.

// -   `#unparseByteStack` turns a stack of bytes (as a `WordStack`) into a
//     `String`.
// -   `#padByte` ensures that the `String` interperetation of a `Int` is
//     wide enough.


    syntax String ::= #unparseByteStack ( WordStack )                [function]
                    | #unparseByteStack ( WordStack , StringBuffer ) [function, klabel(#unparseByteStackAux)]
 // ---------------------------------------------------------------------------------------------------------
    rule #unparseByteStack ( WS ) => #unparseByteStack(WS, .StringBuffer)

    rule #unparseByteStack( .WordStack, BUFFER ) => StringBuffer2String(BUFFER)
    rule #unparseByteStack( W : WS, BUFFER )     => #unparseByteStack(WS, BUFFER +String chrChar(W %Int (2 ^Int 8)))

    syntax String ::= #padByte( String ) [function]
 // -----------------------------------------------
    rule #padByte( S ) => S             requires lengthString(S) ==K 2
    rule #padByte( S ) => "0" +String S requires lengthString(S) ==K 1


// Recursive Length Prefix (RLP)
// =============================

// RLP encoding is used extensively for executing the blocks of a transaction. For
// details about RLP encoding, see the [YellowPaper Appendix
// B](http://gavwood.com/paper.pdf).

// Encoding
// --------

// -   `#rlpEncodeWord` RLP encodes a single EVM word.
// -   `#rlpEncodeString` RLP encodes a single `String`.


    syntax String ::= #rlpEncodeWord ( Int )            [function]
                    | #rlpEncodeWordStack ( WordStack ) [function]
                    | #rlpEncodeString ( String )       [function]
 // --------------------------------------------------------------
    rule #rlpEncodeWord(0) => "\x80"
    rule #rlpEncodeWord(WORD) => chrChar(WORD) requires WORD >Int 0 andBool WORD <Int 128
    rule #rlpEncodeWord(WORD) => #rlpEncodeLength(#unparseByteStack(#asByteStack(WORD)), 128) requires WORD >=Int 128

    rule #rlpEncodeWordStack(.WordStack) => ""
    rule #rlpEncodeWordStack(W : WS)     => #rlpEncodeWord(W) +String #rlpEncodeWordStack(WS)

    rule #rlpEncodeString(STR) => STR                        requires lengthString(STR) ==Int 1 andBool ordChar(STR) <Int 128
    rule #rlpEncodeString(STR) => #rlpEncodeLength(STR, 128) [owise]

    syntax String ::= #rlpEncodeLength ( String , Int )          [function]
                    | #rlpEncodeLength ( String , Int , String ) [function, klabel(#rlpEncodeLengthAux)]
 // ----------------------------------------------------------------------------------------------------
    rule #rlpEncodeLength(STR, OFFSET) => chrChar(lengthString(STR) +Int OFFSET) +String STR requires lengthString(STR) <Int 56
    rule #rlpEncodeLength(STR, OFFSET) => #rlpEncodeLength(STR, OFFSET, #unparseByteStack(#asByteStack(lengthString(STR)))) requires lengthString(STR) >=Int 56
    rule #rlpEncodeLength(STR, OFFSET, BL) => chrChar(lengthString(BL) +Int OFFSET +Int 55) +String BL +String STR


// Decoding
// --------

// -   `#rlpDecode` RLP decodes a single `String` into a `JSON`.
// -   `#rlpDecodeList` RLP decodes a single `String` into a `JSONList`,
//     interpereting the string as the RLP encoding of a list.


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

