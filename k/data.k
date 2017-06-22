// EVM Words
// =========

// EVM uses bounded 256 bit integer words. Here we provide the arithmetic of these
// words, as well as some data-structures over them.


requires "domains.k"

module EVM-DATA
    imports KRYPTO

    syntax KResult ::= Int 


// Word Operations
// ---------------

// -   `#symbolicWord` generates a fresh existentially-bound symbolic word.
// -   `chop` interperets an interger module $2^256$.


    syntax Word ::= Int
                  | "#symbolicWord"    [function]
                  | chop ( Word )      [function]
 // ---------------------------------------------
    rule #symbolicWord    => ?X:Int
    rule chop( W:Int )    => chop ( W +Int (2 ^Int 256) ) requires W <Int 0
    rule chop( W:Int )    => chop ( W %Int (2 ^Int 256) ) requires W >=Int (2 ^Int 256)
    rule chop( W:Int )    => W requires W >=Int 0 andBool W <Int (2 ^Int 256)


// -   `bool2Word` interperets a `Bool` as a `Word`.
// -   `word2Bool` interperets a `Word` as a `Bool`.


    syntax Word ::= bool2Word ( Bool ) [function]
 // ---------------------------------------------
    rule bool2Word(true)  => 1
    rule bool2Word(false) => 0

    syntax Bool ::= word2Bool ( Word ) [function]
 // ---------------------------------------------
    rule word2Bool( 0 ) => false
    rule word2Bool( W ) => true  requires W =/=K 0


// -   `#ifWord_#then_#else_#fi` provides a conditional in `Word` expressions.


    syntax Word ::= "#ifWord" Bool "#then" Word "#else" Word "#fi" [function]
 // -------------------------------------------------------------------------
    rule #ifWord true  #then W #else _ #fi => W
    rule #ifWord false #then _ #else W #fi => W


// -   `up/Int` performs integer division but rounds up instead of down.


    syntax Int ::= Int "up/Int" Int [function]
 // ------------------------------------------
    rule I1 up/Int I2 => I1 /Int I2          requires I1 %Int I2 ==K 0
    rule I1 up/Int I2 => (I1 /Int I2) +Int 1 requires I1 %Int I2 =/=K 0


// -   `sgn` gives the twos-complement interperetation of the sign of a `Word`.
// -   `abs` gives the twos-complement interperetation of the magnitude of a
//     `Word`.


    syntax Int ::= sgn ( Word ) [function]
                 | abs ( Word ) [function]
 // --------------------------------------
    rule sgn(I:Int) => -1 requires I >=Int (2 ^Int 255)
    rule sgn(I:Int) => 1  requires I <Int (2 ^Int 255)
    rule abs(I:Int) => 0 -Word I requires sgn(I) ==K -1
    rule abs(I:Int) => I         requires sgn(I) ==K 1


// -   `maxWord` and `minWord` are the lifting of `maxInt` and `minInt` (through
//     the subsort monad!).


    syntax Word ::= maxWord ( Word , Word ) [function]
                  | minWord ( Word , Word ) [function]
 // --------------------------------------------------
    rule maxWord(W0:Int, W1:Int) => maxInt(W0, W1)
    rule minWord(W0:Int, W1:Int) => minInt(W0, W1)


// ### Arithmetic


    syntax Word ::= Word "+Word" Word [function]
                  | Word "*Word" Word [function]
                  | Word "-Word" Word [function]
                  | Word "/Word" Word [function]
                  | Word "%Word" Word [function]
 // --------------------------------------------
    rule W0:Int +Word W1:Int => chop( W0 +Int W1 )
    rule W0:Int -Word W1:Int => chop( W0 -Int W1 )
    rule W0:Int *Word W1:Int => chop( W0 *Int W1 )
    rule W0:Int /Word 0      => 0
    rule W0:Int /Word W1:Int => chop( W0 /Int W1 ) requires W1 =/=K 0
    rule W0:Int %Word 0      => 0 
    rule W0:Int %Word W1:Int => chop( W0 %Int W1 ) requires W1 =/=K 0


// Care is needed for `^Word` to avoid big exponentiation.


    syntax Word ::= Word "^Word" Word [function]
 // --------------------------------------------
    rule W0:Int ^Word W1:Int => (W0 ^Word (W1 /Int 2)) ^Word 2  requires W1 >=Int (2 ^Int 16) andBool W1 %Int 2 ==Int 0
    rule W0:Int ^Word W1:Int => (W0 ^Word (W1 -Int 1)) *Word W0 requires W1 >=Int (2 ^Int 16) andBool W1 %Int 2 ==Int 1
    rule W0:Int ^Word W1:Int => chop( W0 ^Int W1 )              requires W1 <Int (2 ^Int 16)


// `/sWord` and `%sWord` give the signed interperetations of `/Word` and `%Word`.


    syntax Word ::= Word "/sWord" Word [function]
                  | Word "%sWord" Word [function]
 // ---------------------------------------------
    rule W0:Int /sWord W1:Int => twosComp(twosComp(W0) /Word twosComp(W1)) *Word (sgn(W0) *Int sgn(W1))
    rule W0:Int %sWord W1:Int => twosComp(twosComp(W0) %Word twosComp(W1)) *Word sgn(W0)


// ### Comparison Operators


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


// -   `s<Word` implements a less-than for `Word` interpereted as signed.

// ### Bitwise operators.

// Bitwise logical operators are lifted from the integer versions.


    syntax Word ::= "~Word" Word        [function]
                  | Word "|Word" Word   [function]
                  | Word "&Word" Word   [function]
                  | Word "xorWord" Word [function]
 // ----------------------------------------------
    rule ~Word W:Int           => chop( W xorInt ((2 ^Int 256) -Int 1) )
    rule W0:Int |Word   W1:Int => chop( W0 |Int W1 )
    rule W0:Int &Word   W1:Int => chop( W0 &Int W1 )
    rule W0:Int xorWord W1:Int => chop( W0 xorInt W1 )


// -   `bit` gets bit $N$ (0 being MSB).
// -   `byte` gets byte $N$ (0 being the MSB).
// -   `#nBits` shifts in $N$ ones from the right.
// -   `#nBytes` shifts in $N$ bytes of ones from the right.
// -   `_<<Byte_` shifts an integer 8 bits to the left.


    syntax Word ::= bit  ( Word , Word ) [function]
                  | byte ( Word , Word ) [function]
 // -----------------------------------------------
    rule bit(N:Int, W:Int)  => (W >>Int (255 -Int N)) %Int 2
    rule byte(N:Int, W:Int) => (W >>Int (256 -Int (8 *Int (N +Int 1)))) %Int (2 ^Int 8)

    syntax Int  ::= #nBits  ( Int )  [function]
                  | #nBytes ( Int )  [function]
                  | Int "<<Byte" Int [function]
 // -------------------------------------------
    rule #nBits(N)  => (2 ^Int N) -Int 1
    rule #nBytes(N) => #nBits(N *Int 8)
    rule N <<Byte M => N <<Int (8 *Int M)


// -   `signextend(N, W)` sign-extends from byte $N$ of $W$ (0 being MSB).

// Note that we give "uninterpreted function" semantics to `keccak`, which is
// fairly close to accurate. For SHA3, it must be noted that the we make accesses
// to local memory, which is a word addressable byte array. The authors make it
// clear why the memory has to be word addressable - the word length is the same as
// length the output of Keccak 256 in SHA3's specifications. However, there seems
// to be a lack of explanation behind the decision to use a byte array instead of a
// word array. This goes against usual notions that assembly languages follow,
// which is word addressable word array (where the length of the word is usually 32
// or 64 bits). This allows using\
// using the contents of any cell in the array as an address - an advantage that
// EVM decided to forego.


    syntax HexString ::=   String 
                         | "#addPadding"     "(" HexString ")"    [function]
                         | "#byteToHex"      "(" Word ")"         [function]
                         | "#byteStackToHex" "(" WordStack ")"    [function]
                         | HexString "+HexString" HexString       [function, strict]

    syntax KResult ::= String 

    rule X:String +HexString Y:String => X +String Y

    // If the content is not a complete byte
    rule #addPadding(X:String)        => X                              requires lengthString(X) ==Int 2
    rule #addPadding(X:String)        => #addPadding("0" +String X)     requires lengthString(X)  ==Int 1
    rule #byteToHex(X:Int)            => #addPadding(Base2String(X, 16))
    rule #byteStackToHex(.WordStack)  => "" 
    rule #byteStackToHex(W : WS)      => #byteToHex(W) +HexString #byteStackToHex(WS) 

    syntax Word ::= "keccak" "(" HexString ")"                    [strict, function]

    rule keccak(X:String) => Keccak256(X)



    //syntax Word ::= "#calcKeccak" "(" String ")"                  [strict]

    //rule keccak(X: String) =>  #calcKeccak(Keccak256(X))

    //rule #calcKeccak(X: String) => String2Base(X, 16)
 // -----------------------------------------------


// Data Structures
// ---------------

// Several data-structures over `Word` are convenient to have around.

// ### Word Stack

// EVM is a stack machine, and so needs a stack of words to operate on. The stack
// and some standard operations over it are provided here. This stack also serves
// as a cons-list, so we provide some standard cons-list manipulation tools.


    syntax WordStack ::= ".WordStack" | Word ":" WordStack
 // ------------------------------------------------------


// -   `_++_` acts as `WordStack` append.
// -   `#take( N , WS)` keeps the first $N$ elements of a `WordStack` (passing with
//     zeros as needed).
// -   `#drop( N , WS)` removes the first $N$ elements of a `WordStack`.


    syntax WordStack ::= WordStack "++" WordStack [function]
 // --------------------------------------------------------
    rule .WordStack ++ WS' => WS'
    rule (W : WS)   ++ WS' => W : (WS ++ WS')

    syntax WordStack ::= #take ( Word , WordStack ) [function]
 // ----------------------------------------------------------
    rule #take(0, WS)         => .WordStack
    rule #take(N, .WordStack) => 0 : #take(N -Word 1, .WordStack) requires word2Bool(N >Word 0)
    rule #take(N, (W : WS))   => W : #take(N -Word 1, WS)         requires word2Bool(N >Word 0)

    syntax WordStack ::= #drop ( Word , WordStack ) [function]
 // ----------------------------------------------------------
    rule #drop(0, WS)         => WS
    rule #drop(N, .WordStack) => .WordStack
    rule #drop(N, (W : WS))   => #drop(N -Word 1, WS) requires word2Bool(N >Word 0)


// -   `WS [ N ]` accesses element $N$ of $WS$.
// -   `WS [ N := W ]` sets element $N$ of $WS$ to $W$ (padding with zeros
//     as needed).


    syntax Word ::= WordStack "[" Word "]" [function]
 // -------------------------------------------------
    rule (W0 : WS)   [0] => W0
    rule (.WordStack)[N] => 0             requires word2Bool(N >Word 0)
    rule (W0 : WS)   [N] => WS[N -Word 1] requires word2Bool(N >Word 0)

    syntax WordStack ::= WordStack "[" Word ":=" Word "]" [function]
 // ----------------------------------------------------------------
    rule (W0 : WS)  [ 0 := W ] => W  : WS
    rule .WordStack [ N := W ] => 0  : (.WordStack [ N -Int 1 := W ]) requires word2Bool(N >Word 0)
    rule (W0 : WS)  [ N := W ] => W0 : (WS [ N -Int 1 := W ])         requires word2Bool(N >Word 0)

    syntax WordStack ::= WordStack "[" Word ".." Word "]" [function]
 // ----------------------------------------------------------------
    rule WS [ START .. WIDTH ] => #take(WIDTH, #drop(START, WS))


// -   `#size` calculates the size of a `WordStack`.
// -   `_in_` determines if a `Word` occurs in a `WordStack`.


    syntax Int ::= #size ( WordStack ) [function]
 // ---------------------------------------------
    rule #size ( .WordStack ) => 0
    rule #size ( W : WS )     => 1 +Int #size(WS)

    syntax Bool ::= Word "in" WordStack [function]
 // ----------------------------------------------
    rule W in .WordStack => false
    rule W in (W' : WS)  => (W ==K W') orElseBool (W in WS)


// -   `#padToWidth(N, WS)` makes sure that a `WordStack` is the correct size.


    syntax WordStack ::= #padToWidth ( Int , WordStack ) [function]
 // ---------------------------------------------------------------
    rule #padToWidth(N, WS) => WS                     requires notBool #size(WS) <Int N
    rule #padToWidth(N, WS) => #padToWidth(N, 0 : WS) requires #size(WS) <Int N


// Byte Arrays
// -----------

// The local memory of execution is a byte-array (instead of a word-array).

// -   `#asWord` will interperet a stack of bytes as a single word (with
//     MSB first).
// -   `#asByteStack` will split a single word up into a `WordStack` where each
//     word is a byte wide.


    syntax Word ::= #asWord ( WordStack ) [function]
 // ------------------------------------------------
    rule #asWord( .WordStack )    => 0
    rule #asWord( W : .WordStack) => W
    rule #asWord( W0 : W1 : WS )  => #asWord(((W0 *Word 256) +Word W1) : WS)

    syntax WordStack ::= #asByteStack ( Word )             [function]
                       | #asByteStack ( Word , WordStack ) [function]
 // -----------------------------------------------------------------
    rule #asByteStack( W ) => #asByteStack( W , .WordStack )
    rule #asByteStack( 0 , WS ) => WS
    rule #asByteStack( W , WS ) => #asByteStack( W /Int 256 , W %Int 256 : WS ) requires W =/=K 0


// Addresses
// ---------

// -   `#addr` turns an Ethereum word into the corresponding Ethereum address
//     (160 LSB).


    syntax Word ::= #addr ( Word ) [function]
 // -----------------------------------------
    rule #addr(W) => W %Word (2 ^Word 160)


// Word Map
// --------

// Most of EVM data is held in finite maps. We are using the polymorphic `Map` sort
// for these word maps.

// -   `WM [ N := WS ]` assigns a contiguous chunk of $WM$ to $WS$ starting at
//     position $W$.
// -   `#asMap` converts a `WordStack` to a `Map`.
// -   `#range(M, START, WIDTH)` reads off $WIDTH$ elements from $WM$ beginning at
//     position $START$ (padding with zeros as needed).


    syntax Map ::= Map "[" Word ":=" WordStack "]" [function]
 // ---------------------------------------------------------
    rule WM[ N := .WordStack ] => WM
    rule WM[ N := W : WS     ] => (WM[N <- W0])[N +Word 1 := WS]

    syntax Map ::= #asMap ( WordStack ) [function]
 // ----------------------------------------------
    rule #asMap(WS:WordStack) => .Map [ 0 := WS ]

    syntax WordStack ::= #range ( Map , Word , Word ) [function]
 // ------------------------------------------------------------
    rule #range(WM,         N, 0) => .WordStack
    rule #range(WM,         N, M) => 0 : #range(WM, N +Word 1, M -Word 1) requires M =/=K 0 andBool notBool N in keys(WM)
    rule #range(N |-> W WM, N, M) => W : #range(WM, N +Word 1, M -Word 1) requires M =/=K 0
endmodule

