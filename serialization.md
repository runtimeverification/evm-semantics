Parsing/Unparsing
=================

```k
requires "krypto.k"
requires "evm-types.k"
requires "json.k"
```

```k
module SERIALIZATION
    imports KRYPTO
    imports EVM-TYPES
    imports STRING-BUFFER
    imports JSON
```

Address/Hash Helpers
--------------------

-   `keccak` serves as a wrapper around the `Keccak256` in `KRYPTO`.

```k
    syntax Int ::= keccak ( ByteArray ) [function, functional, smtlib(smt_keccak)]
 // ------------------------------------------------------------------------------
    rule [keccak]: keccak(WS) => #parseHexWord(Keccak256(#unparseByteStack(WS))) [concrete]
```

-   `#newAddr` computes the address of a new account given the address and nonce of the creating account.
-   `#sender` computes the sender of the transaction from its data and signature.
-   `#addrFromPrivateKey` computes the address of an account given its private key

```k
    syntax Int ::= #newAddr ( Int , Int ) [function]
                 | #newAddr ( Int , Int , ByteArray ) [function, klabel(#newAddrCreate2)]
 // -------------------------------------------------------------------------------------
    rule [#newAddr]:        #newAddr(ACCT, NONCE) => #addr(#parseHexWord(Keccak256(#rlpEncodeLength(#rlpEncodeBytes(ACCT, 20) +String #rlpEncodeWord(NONCE), 192))))
    rule [#newAddrCreate2]: #newAddr(ACCT, SALT, INITCODE) => #addr(#parseHexWord(Keccak256("\xff" +String #unparseByteStack(#padToWidth(20, #asByteStack(ACCT))) +String #unparseByteStack(#padToWidth(32, #asByteStack(SALT))) +String #unparseByteStack(#parseHexBytes(Keccak256(#unparseByteStack(INITCODE)))))))

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

- `#hashSignedTx` Takes transaction data. Returns the hash of the rlp-encoded transaction with R S and V.
- `#hashUnsignedTx` Returns the hash of the rlp-encoded transaction without R S or V.

```k
    syntax String ::= #hashSignedTx   ( Int , Int , Int , Account , Int , ByteArray , Int , ByteArray , ByteArray ) [function]
                    | #hashUnsignedTx ( Int , Int , Int , Account , Int , ByteArray )                               [function]
 // --------------------------------------------------------------------------------------------------------------------------
    rule [hashTx]: #hashSignedTx(TN, TP, TG, TT, TV, TD, TW, TR, TS)
                => Keccak256( #rlpEncodeTransaction(TN, TP, TG, TT, TV, TD, TW, TR, TS) )

    rule [hashFakeTx]: #hashUnsignedTx(TN, TP, TG, TT, TV, TD)
                    => Keccak256( #rlpEncodeLength(         #rlpEncodeWord(TN)
                                                    +String #rlpEncodeWord(TP)
                                                    +String #rlpEncodeWord(TG)
                                                    +String #rlpEncodeAccount(TT)
                                                    +String #rlpEncodeWord(TV)
                                                    +String #rlpEncodeString(#unparseByteStack(TD))
                                                  , 192
                                                  )
                                )
```

The EVM test-sets are represented in JSON format with hex-encoding of the data and programs.
Here we provide some standard parser/unparser functions for that format.

Parsing
-------

These parsers can interperet hex-encoded strings as `Int`s, `ByteArray`s, and `Map`s.

-   `#parseHexWord` interprets a string as a single hex-encoded `Word`.
-   `#parseHexBytes` interprets a string as a hex-encoded stack of bytes.
-   `#alignHexString` makes sure that the length of a (hex)string is even.
-   `#parseByteStack` interprets a string as a hex-encoded stack of bytes, but makes sure to remove the leading "0x".
-   `#parseByteStackRaw` casts a string as a stack of bytes, ignoring any encoding.
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

    syntax String ::= #alignHexString ( String ) [function, functional]
 // -------------------------------------------------------------------
    rule #alignHexString(S) => S             requires         lengthString(S) modInt 2 ==Int 0
    rule #alignHexString(S) => "0" +String S requires notBool lengthString(S) modInt 2 ==Int 0
```

```{.k .bytes}
    syntax ByteArray ::= #parseHexBytes     ( String ) [function]
                       | #parseHexBytesAux  ( String ) [function]
                       | #parseByteStack    ( String ) [function, memo]
                       | #parseByteStackRaw ( String ) [function]
 // -------------------------------------------------------------------
    rule #parseByteStack(S) => #parseHexBytes(replaceAll(S, "0x", ""))

    rule #parseHexBytes(S)  => #parseHexBytesAux(#alignHexString(S))
    rule #parseHexBytesAux("") => .ByteArray
    rule #parseHexBytesAux(S)  => Int2Bytes(lengthString(S) /Int 2, String2Base(S, 16), BE)
      requires lengthString(S) >=Int 2

    rule #parseByteStackRaw(S) => String2Bytes(S)
```

```{.k .nobytes}
    syntax ByteArray ::= #parseHexBytes     ( String ) [function]
                       | #parseHexBytesAux  ( String ) [function]
                       | #parseByteStack    ( String ) [function]
                       | #parseByteStackRaw ( String ) [function]
 // -------------------------------------------------------------
    rule #parseByteStack(S) => #parseHexBytes(replaceAll(S, "0x", ""))

    rule #parseHexBytes(S)  => #parseHexBytesAux(#alignHexString(S))
    rule #parseHexBytesAux("") => .WordStack
    rule #parseHexBytesAux(S)  => #parseHexWord(substrString(S, 0, 2)) : #parseHexBytesAux(substrString(S, 2, lengthString(S)))
       requires lengthString(S) >=Int 2

    rule #parseByteStackRaw(S) => ordChar(substrString(S, 0, 1)) : #parseByteStackRaw(substrString(S, 1, lengthString(S))) requires lengthString(S) >=Int 1
    rule #parseByteStackRaw("") => .WordStack
```

```k
    syntax Map ::= #parseMap ( JSON ) [function]
 // --------------------------------------------
    rule #parseMap( { .JSONs                      } ) => .Map
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

```{.k .bytes}
    syntax String ::= #unparseByteStack ( ByteArray ) [function, klabel(unparseByteStack), symbol]
 // ----------------------------------------------------------------------------------------------
    rule #unparseByteStack(WS) => Bytes2String(WS)
```

```{.k .nobytes}
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

    rule #rlpEncodeString(STR) => STR                        requires           lengthString(STR) ==Int 1 andBool ordChar(STR) <Int 128
    rule #rlpEncodeString(STR) => #rlpEncodeLength(STR, 128) requires notBool ( lengthString(STR) ==Int 1 andBool ordChar(STR) <Int 128 )

    rule #rlpEncodeAccount(.Account) => "\x80"
    rule #rlpEncodeAccount(ACCT)     => #rlpEncodeBytes(ACCT, 20) requires ACCT =/=K .Account

    syntax String ::= #rlpEncodeLength ( String , Int )          [function]
                    | #rlpEncodeLength ( String , Int , String ) [function, klabel(#rlpEncodeLengthAux)]
 // ----------------------------------------------------------------------------------------------------
    rule #rlpEncodeLength(STR, OFFSET) => chrChar(lengthString(STR) +Int OFFSET) +String STR                                requires           lengthString(STR) <Int 56
    rule #rlpEncodeLength(STR, OFFSET) => #rlpEncodeLength(STR, OFFSET, #unparseByteStack(#asByteStack(lengthString(STR)))) requires notBool ( lengthString(STR) <Int 56 )
    rule #rlpEncodeLength(STR, OFFSET, BL) => chrChar(lengthString(BL) +Int OFFSET +Int 55) +String BL +String STR

    syntax String ::= #rlpEncodeTransaction( Int , Int , Int , Account , Int , ByteArray , Int , ByteArray , ByteArray ) [function]
 // -------------------------------------------------------------------------------------------------------------------------------
    rule [rlpTx]: #rlpEncodeTransaction(TN, TP, TG, TT, TV, TD, TW, TR, TS)
               => #rlpEncodeLength(         #rlpEncodeWord(TN)
                                    +String #rlpEncodeWord(TP)
                                    +String #rlpEncodeWord(TG)
                                    +String #rlpEncodeAccount(TT)
                                    +String #rlpEncodeWord(TV)
                                    +String #rlpEncodeString(#unparseByteStack(TD))
                                    +String #rlpEncodeWord(TW)
                                    +String #rlpEncodeString(#unparseByteStack(#asByteStack(#asWord(TR))))
                                    +String #rlpEncodeString(#unparseByteStack(#asByteStack(#asWord(TS))))
                                  , 192
                                  )

    syntax String ::= #rlpEncodeFullAccount( Int, Int, Map, ByteArray ) [function]
 // ------------------------------------------------------------------------------
    rule [rlpAcct]: #rlpEncodeFullAccount( NONCE, BAL, STORAGE, CODE )
                 => #rlpEncodeLength(         #rlpEncodeWord(NONCE)
                                      +String #rlpEncodeWord(BAL)
                                      +String #rlpEncodeString( Hex2Raw( Keccak256( #rlpEncodeMerkleTree( #storageRoot( STORAGE ) ) ) ) )
                                      +String #rlpEncodeString( Hex2Raw( Keccak256( #unparseByteStack( CODE ) ) ) )
                                    , 192
                                    )

    syntax String ::= #rlpEncodeReceipt ( Int , Int , ByteArray , List ) [function]
                    | #rlpEncodeLogs    ( List )                         [function]
                    | #rlpEncodeLogsAux ( List, String )                 [function]
                    | #rlpEncodeTopics  ( List, String )                 [function]
 // -------------------------------------------------------------------------------
    rule [rlpReceipt]: #rlpEncodeReceipt(RS, RG, RB, RL)
                    => #rlpEncodeLength(         #rlpEncodeWord(RS)
                                         +String #rlpEncodeWord(RG)
                                         +String #rlpEncodeString(#unparseByteStack(RB))
                                         +String #rlpEncodeLogs(RL)
                                       , 192
                                       )

    rule #rlpEncodeLogs( LOGS ) => #rlpEncodeLogsAux( LOGS, "" )

    rule #rlpEncodeLogsAux( .List, OUT ) => #rlpEncodeLength(OUT,192)
    rule #rlpEncodeLogsAux( ( ListItem({ ACCT | TOPICS | DATA }) => .List ) _
                          , ( OUT => OUT +String #rlpEncodeLength(         #rlpEncodeBytes(ACCT,20)
                                                                   +String #rlpEncodeTopics(TOPICS,"")
                                                                   +String #rlpEncodeString(#unparseByteStack(DATA))
                                                                 , 192
                                                                 )
                            )
                          )

    rule #rlpEncodeTopics( .List, OUT ) => #rlpEncodeLength(OUT,192)
    rule #rlpEncodeTopics( ( ListItem( X:Int ) => .List ) _
                         , ( OUT => OUT +String #rlpEncodeBytes(X,32) )
                         )

    syntax String ::= #rlpEncodeMerkleTree ( MerkleTree ) [function]
 // ----------------------------------------------------------------
    rule #rlpEncodeMerkleTree ( .MerkleTree ) => "\x80"

    rule #rlpEncodeMerkleTree ( MerkleLeaf ( PATH, VALUE ) )
      => #rlpEncodeLength(         #rlpEncodeString( #unparseByteStack( #HPEncode( PATH, 1 ) ) )
                           +String #rlpEncodeString( VALUE )
                         , 192
                         )

    rule #rlpEncodeMerkleTree ( MerkleExtension ( PATH, TREE ) )
      => #rlpEncodeLength(         #rlpEncodeString( #unparseByteStack( #HPEncode( PATH, 0 ) ) )
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
      requires lengthString(X) >=Int 32

    rule #rlpMerkleH ( X ) => X
      requires notBool lengthString(X) >=Int 32
```

Decoding
--------

-   `#rlpDecode` RLP decodes a single `String` into a `JSON`.
-   `#rlpDecodeList` RLP decodes a single `String` into a `JSONs`, interpereting the string as the RLP encoding of a list.

```k
    syntax JSON ::= #rlpDecode(String)               [function]
                  | #rlpDecode(String, LengthPrefix) [function, klabel(#rlpDecodeAux)]
 // ----------------------------------------------------------------------------------
    rule #rlpDecode(STR) => #rlpDecode(STR, #decodeLengthPrefix(STR, 0))
    rule #rlpDecode(STR, #str(LEN, POS))  => substrString(STR, POS, POS +Int LEN)
    rule #rlpDecode(STR, #list(LEN, POS)) => [#rlpDecodeList(STR, POS)]

    syntax JSONs ::= #rlpDecodeList(String, Int)               [function]
                   | #rlpDecodeList(String, Int, LengthPrefix) [function, klabel(#rlpDecodeListAux)]
 // ------------------------------------------------------------------------------------------------
    rule #rlpDecodeList(STR, POS) => #rlpDecodeList(STR, POS, #decodeLengthPrefix(STR, POS)) requires POS <Int lengthString(STR)
    rule #rlpDecodeList(STR, POS) => .JSONs [owise]
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
      requires #unparseByteStack( LEAFPATH ) ==String #unparseByteStack( PATH )

    rule MerkleUpdate ( MerkleLeaf ( LEAFPATH, LEAFVALUE ), PATH, VALUE )
      => MerkleUpdate ( MerkleUpdate ( .MerkleBranch, LEAFPATH, LEAFVALUE ), PATH, VALUE )
      requires #sizeByteArray( LEAFPATH ) >Int 0
       andBool #sizeByteArray( PATH ) >Int 0
       andBool LEAFPATH[0] =/=Int PATH[0]

    rule MerkleUpdate ( MerkleLeaf ( LEAFPATH, LEAFVALUE ), PATH, VALUE )
      => #merkleExtensionBuilder( .ByteArray, LEAFPATH, LEAFVALUE, PATH, VALUE )
      requires #unparseByteStack( LEAFPATH ) =/=String #unparseByteStack( PATH )
       andBool #sizeByteArray( LEAFPATH ) >Int 0
       andBool #sizeByteArray( PATH )     >Int 0
       andBool LEAFPATH[0] ==Int PATH[0]

    rule MerkleUpdate ( MerkleExtension ( EXTPATH, EXTTREE ), PATH, VALUE )
      => MerkleExtension ( EXTPATH, MerkleUpdate ( EXTTREE, .ByteArray, VALUE ) )
      requires #unparseByteStack( EXTPATH ) ==String #unparseByteStack( PATH )

    rule MerkleUpdate ( MerkleExtension ( EXTPATH, EXTTREE ), PATH, VALUE )
      => #merkleExtensionBrancher( MerkleUpdate( .MerkleBranch, PATH, VALUE ), EXTPATH, EXTTREE )
      requires #sizeByteArray( PATH ) >Int 0
       andBool EXTPATH[0] =/=Int PATH[0]

    rule MerkleUpdate ( MerkleExtension ( EXTPATH, EXTTREE ), PATH, VALUE )
      => #merkleExtensionSplitter( .ByteArray, EXTPATH, EXTTREE, PATH, VALUE )
      requires #unparseByteStack( EXTPATH ) =/=String #unparseByteStack( PATH )
       andBool #sizeByteArray( PATH ) >Int 0
       andBool EXTPATH[0] ==Int PATH[0]

    rule MerkleUpdate ( MerkleBranch( M, _ ), PATH, VALUE )
      => MerkleBranch( M, VALUE )
      requires #sizeByteArray( PATH ) ==Int 0

    rule MerkleUpdate ( MerkleBranch( M, BRANCHVALUE ), PATH, VALUE )
      => #merkleUpdateBranch ( M, BRANCHVALUE, PATH[0], PATH[1 .. #sizeByteArray(PATH) -Int 1], VALUE )
      requires #sizeByteArray( PATH ) >Int 0
```

- `MerkleUpdateMap` Takes a mapping of `ByteArray |-> String` and generates a trie

```k
    syntax MerkleTree ::= MerkleUpdateMap    ( MerkleTree , Map        ) [function]
                        | MerkleUpdateMapAux ( MerkleTree , Map , List ) [function]
 // -------------------------------------------------------------------------------
    rule MerkleUpdateMap(TREE, MMAP) => MerkleUpdateMapAux(TREE, MMAP, keys_list(MMAP))

    rule MerkleUpdateMapAux(TREE, _, .List ) => TREE
    rule MerkleUpdateMapAux(TREE                                                    , MMAP, ListItem(KEY) REST)
      => MerkleUpdateMapAux(MerkleUpdate(TREE, #nibbleize(KEY), {MMAP[KEY]}:>String), MMAP,               REST)
```

Merkle Tree Aux Functions
-------------------------

```k
    syntax ByteArray ::= #nibbleize ( ByteArray ) [function]
                       | #byteify   ( ByteArray ) [function]
 // --------------------------------------------------------
    rule #nibbleize ( B ) => (      #asByteStack ( B [ 0 ] /Int 16 )[0 .. 1]
                               ++ ( #asByteStack ( B [ 0 ] %Int 16 )[0 .. 1] )
                             ) ++ #nibbleize ( B[1 .. #sizeByteArray(B) -Int 1] )
      requires #sizeByteArray(B) >Int 0

    rule #nibbleize ( B ) => .ByteArray
      requires notBool #sizeByteArray(B) >Int 0

    rule #byteify ( B ) =>    #asByteStack ( B[0] *Int 16 +Int B[1] )[0 .. 1]
                           ++ #byteify ( B[2 .. #sizeByteArray(B) -Int 2] )
      requires #sizeByteArray(B) >Int 0

    rule #byteify ( B ) => .ByteArray
      requires notBool #sizeByteArray(B) >Int 0

    syntax ByteArray ::= #HPEncode ( ByteArray, Int ) [function]
 // ------------------------------------------------------------
    rule #HPEncode ( X, T ) => #asByteStack ( ( HPEncodeAux(T) +Int 1 ) *Int 16 +Int X[0] ) ++ #byteify( X[1 .. #sizeByteArray(X) -Int 1] )
      requires #sizeByteArray(X) %Int 2 =/=Int 0

    rule #HPEncode ( X, T ) => #asByteStack ( HPEncodeAux(T) *Int 16 )[0 .. 1] ++ #byteify( X )
      requires notBool #sizeByteArray(X) %Int 2 =/=Int 0

    syntax Int ::= HPEncodeAux ( Int ) [function]
 // ---------------------------------------------
    rule HPEncodeAux ( X ) => 0 requires         X ==Int 0
    rule HPEncodeAux ( X ) => 2 requires notBool X ==Int 0

    syntax MerkleTree ::= #merkleUpdateBranch ( Map, String, Int, ByteArray, String ) [function]
 // --------------------------------------------------------------------------------------------
    rule #merkleUpdateBranch ( X |-> TREE M, BRANCHVALUE, X, PATH, VALUE )
      => MerkleBranch( M[X <- MerkleUpdate( TREE, PATH, VALUE )], BRANCHVALUE )

    syntax MerkleTree ::= #merkleExtensionBuilder( ByteArray, ByteArray, String, ByteArray, String ) [function]
 // -----------------------------------------------------------------------------------------------------------
    rule #merkleExtensionBuilder( PATH, P1, V1, P2, V2 )
      => #merkleExtensionBuilder( PATH ++ ( #asByteStack( P1[0] )[0 .. 1] )
                                , P1[1 .. #sizeByteArray(P1) -Int 1], V1
                                , P2[1 .. #sizeByteArray(P2) -Int 1], V2
                                )
      requires #sizeByteArray(P1) >Int 0
       andBool #sizeByteArray(P2) >Int 0
       andBool P1[0] ==Int P2[0]

    rule #merkleExtensionBuilder( PATH, P1, V1, P2, V2 )
      => MerkleExtension( PATH, MerkleUpdate( MerkleUpdate( .MerkleBranch, P1, V1 ), P2, V2 ) )
      requires #sizeByteArray(P1) ==Int 0
        orBool #sizeByteArray(P2) ==Int 0
        orBool ( #sizeByteArray(P1) >Int 0
       andBool   #sizeByteArray(P2) >Int 0
       andBool   P1[0] =/=Int P2[0] )

    syntax MerkleTree ::= #merkleExtensionBrancher ( MerkleTree, ByteArray, MerkleTree ) [function]
 // -----------------------------------------------------------------------------------------------
    rule #merkleExtensionBrancher( MerkleBranch(M, VALUE), PATH, EXTTREE )
      => MerkleBranch( M[PATH[0] <- MerkleExtension( PATH[1 .. #sizeByteArray(PATH) -Int 1], EXTTREE )], VALUE )
      requires #sizeByteArray(PATH) >Int 1

    rule #merkleExtensionBrancher( MerkleBranch(M, VALUE), PATH, EXTTREE )
      => MerkleBranch( M[PATH[0] <- EXTTREE], VALUE )
      requires #sizeByteArray(PATH) ==Int 1

    syntax MerkleTree ::= #merkleExtensionSplitter ( ByteArray, ByteArray, MerkleTree, ByteArray, String ) [function]
 // -----------------------------------------------------------------------------------------------------------------
    rule #merkleExtensionSplitter( PATH, P1, TREE, P2, VALUE )
      => #merkleExtensionSplitter( PATH ++ ( #asByteStack( P1[0] )[0 .. 1] )
                                 , P1[1 .. #sizeByteArray(P1) -Int 1], TREE
                                 , P2[1 .. #sizeByteArray(P2) -Int 1], VALUE
                                 )
      requires #sizeByteArray(P1) >Int 0
       andBool #sizeByteArray(P2) >Int 0
       andBool P1[0] ==Int P2[0]

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
```

Tree Root Helper Functions
--------------------------

### Storage Root

```k
    syntax Map ::= #intMap2StorageMap( Map )               [function]
                 | #intMap2StorageMapAux( Map, Map, List ) [function]
 // -----------------------------------------------------------------
    rule #intMap2StorageMap( M ) => #intMap2StorageMapAux( .Map, M, keys_list(M) )

    rule #intMap2StorageMapAux( SMAP, _, .List ) => SMAP
    rule #intMap2StorageMapAux( SMAP, IMAP, ListItem(K) REST )
      => #intMap2StorageMapAux( #padToWidth( 32, #asByteStack(K) ) |-> #rlpEncodeWord({IMAP[K]}:>Int) SMAP, IMAP, REST )
      requires {IMAP[K]}:>Int =/=Int 0

    rule #intMap2StorageMapAux( SMAP, IMAP, ListItem(K) REST )
      => #intMap2StorageMapAux( SMAP, IMAP, REST )
      requires {IMAP[K]}:>Int ==Int 0


    syntax MerkleTree ::= #storageRoot( Map ) [function]
 // ----------------------------------------------------
    rule #storageRoot( STORAGE ) => MerkleUpdateMap( .MerkleTree, #intMap2StorageMap( STORAGE ) )
```

### State Root

```k
    syntax Map ::= "#precompiledContracts" [function]
 // -------------------------------------------------
    rule #precompiledContracts
      => #parseByteStackRaw( Hex2Raw( #unparseData( 1, 20 ) ) ) |-> #emptyContractRLP
         #parseByteStackRaw( Hex2Raw( #unparseData( 2, 20 ) ) ) |-> #emptyContractRLP
         #parseByteStackRaw( Hex2Raw( #unparseData( 3, 20 ) ) ) |-> #emptyContractRLP
         #parseByteStackRaw( Hex2Raw( #unparseData( 4, 20 ) ) ) |-> #emptyContractRLP
         #parseByteStackRaw( Hex2Raw( #unparseData( 5, 20 ) ) ) |-> #emptyContractRLP
         #parseByteStackRaw( Hex2Raw( #unparseData( 6, 20 ) ) ) |-> #emptyContractRLP
         #parseByteStackRaw( Hex2Raw( #unparseData( 7, 20 ) ) ) |-> #emptyContractRLP
         #parseByteStackRaw( Hex2Raw( #unparseData( 8, 20 ) ) ) |-> #emptyContractRLP

    syntax String ::= "#emptyContractRLP" [function]
 // ------------------------------------------------
    rule #emptyContractRLP => #rlpEncodeLength(         #rlpEncodeWord(0)
                                                +String #rlpEncodeWord(0)
                                                +String #rlpEncodeString( Hex2Raw( Keccak256("\x80") ) )
                                                +String #rlpEncodeString( Hex2Raw( Keccak256("") ) )
                                              , 192
                                              )

endmodule
```
