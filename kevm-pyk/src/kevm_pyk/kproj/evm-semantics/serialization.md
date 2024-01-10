Parsing/Unparsing
=================

```k
requires "plugin/krypto.md"
requires "evm-types.md"
requires "json-rpc.md"
```

```k
module SERIALIZATION
    imports KRYPTO
    imports EVM-TYPES
    imports STRING-BUFFER
    imports JSON-EXT
```

Address/Hash Helpers
--------------------

-   `keccak` serves as a wrapper around the `Keccak256` in `KRYPTO`.

```k
    syntax Int ::= keccak ( Bytes ) [function, total, smtlib(smt_keccak)]
 // ---------------------------------------------------------------------
    rule [keccak]: keccak(WS) => #parseHexWord(Keccak256bytes(WS)) [concrete]
```

-   Each `bytes` function serves as a wrapper around the corresponding `KRYPTO` function, but using `Bytes`
    to represent raw byte strings rather than `String`.
```k
    syntax String ::= Keccak256bytes ( Bytes ) [function, total]
                    | Sha256bytes ( Bytes )    [function, total]
                    | RipEmd160bytes ( Bytes ) [function, total]
                    | Blake2Compressbytes ( Bytes ) [function, total]

   syntax Bytes  ::= ECDSARecoverbytes ( Bytes , Int , Bytes , Bytes ) [function, total]
   syntax String ::= ECDSASignbytes ( Bytes, Bytes )                   [function, total]
                   | ECDSAPubKeybytes ( Bytes )                        [function, total]
 // ------------------------------------------------------------------------------------
    rule Keccak256bytes(BS)      => Keccak256(Bytes2String(BS))      [concrete]
    rule Sha256bytes(BS)         => Sha256(Bytes2String(BS))         [concrete]
    rule RipEmd160bytes(BS)      => RipEmd160(Bytes2String(BS))      [concrete]
    rule Blake2Compressbytes(BS) => Blake2Compress(Bytes2String(BS)) [concrete]

    rule ECDSARecoverbytes(BM, V, BR, BS) => String2Bytes(ECDSARecover(Bytes2String(BM), V, Bytes2String(BR), Bytes2String(BS))) [concrete]
    rule ECDSASignbytes(BM, BP) => ECDSASign(Bytes2String(BM), Bytes2String(BP)) [concrete]
    rule ECDSAPubKeybytes(BP) => ECDSAPubKey(Bytes2String(BP))                   [concrete]
```

-   `#newAddr` computes the address of a new account given the address and nonce of the creating account.
-   `#sender` computes the sender of the transaction from its data and signature.
-   `#addrFromPrivateKey` computes the address of an account given its private key

```k
    syntax Int ::= #newAddr ( Int , Int )         [function]
                 | #newAddr ( Int , Int , Bytes ) [function, klabel(#newAddrCreate2)]
 // ---------------------------------------------------------------------------------
    rule [#newAddr]:        #newAddr(ACCT, NONCE) => #addr(#parseHexWord(Keccak256bytes(#rlpEncode([#addrBytes(ACCT), NONCE]))))                                                          [concrete]
    rule [#newAddrCreate2]: #newAddr(ACCT, SALT, INITCODE) => #addr(#parseHexWord(Keccak256bytes(b"\xff" +Bytes #addrBytes(ACCT) +Bytes #wordBytes(SALT) +Bytes #parseByteStack(Keccak256bytes(INITCODE))))) [concrete]

    syntax Account ::= #sender ( TxData , Int , Bytes , Bytes ) [function, klabel(#senderTxData)     ]
                     | #sender ( Bytes  , Int , Bytes , Bytes ) [function, klabel(#senderAux), total ]
                     | #sender ( Bytes )                        [function, klabel(#senderAux2), total]
 // -------------------------------------------------------------------------------------------------
    rule #sender(_:TxData, TW => TW +Int 27, _, _)
      requires TW ==Int 0 orBool TW ==Int 1

    rule #sender(TXDATA, TW, TR, TS)
      => #sender(#parseByteStack(#hashTxData(TXDATA)), TW, TR, TS)
      requires TW =/=Int 0 andBool TW =/=Int 1

    rule #sender(HT, TW, TR, TS) => #sender(ECDSARecoverbytes(HT, TW, TR, TS))

    rule #sender(b"")   => .Account
    rule #sender(BYTES) => #addr(#parseHexWord(Keccak256bytes(BYTES))) requires BYTES =/=K b""

    syntax Int ::= #addrFromPrivateKey ( String ) [function, klabel(addrFromPrivateKey)]
 // ------------------------------------------------------------------------------------
    rule [addrFromPrivateKey]: #addrFromPrivateKey ( KEY ) => #addr( #parseHexWord( Keccak256bytes( #parseByteStack( ECDSAPubKeybytes( #parseByteStack( KEY ) ) ) ) ) ) [concrete]
```

-   `#blockHeaderHash` computes the hash of a block header given all the block data.

```k
    syntax Int ::= #blockHeaderHash( Int , Int , Int , Int , Int , Int , Bytes , Int , Int , Int , Int , Int , Bytes , Int , Int ) [function, klabel(blockHeaderHash), symbol]
                 | #blockHeaderHash(Bytes, Bytes, Bytes, Bytes, Bytes, Bytes, Bytes, Bytes, Bytes, Bytes, Bytes, Bytes, Bytes, Bytes, Bytes) [function, klabel(#blockHashHeaderBytes), symbol]
                 | #blockHeaderHash( Int , Int , Int , Int , Int , Int , Bytes , Int , Int , Int , Int , Int , Bytes , Int , Int , Int) [function, klabel(blockHeaderHashBaseFee), symbol]
                 | #blockHeaderHash(Bytes, Bytes, Bytes, Bytes, Bytes, Bytes, Bytes, Bytes, Bytes, Bytes, Bytes, Bytes, Bytes, Bytes, Bytes, Bytes) [function, klabel(#blockHashHeaderBaseFeeBytes), symbol]
                 | #blockHeaderHash( Int , Int , Int , Int , Int , Int , Bytes , Int , Int , Int , Int , Int , Bytes , Int , Int , Int , Int) [function, klabel(blockHeaderHashWithdrawals), symbol]
                 | #blockHeaderHash(Bytes, Bytes, Bytes, Bytes, Bytes, Bytes, Bytes, Bytes, Bytes, Bytes, Bytes, Bytes, Bytes, Bytes, Bytes, Bytes, Bytes) [function, klabel(#blockHashHeaderWithdrawalsBytes), symbol]
 // ----------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------
    rule #blockHeaderHash(HP:Bytes, HO, HC, HR, HT, HE, HB, HD, HI, HL, HG, HS, HX, HM, HN)
         => #parseHexWord( Keccak256bytes( #rlpEncode( [ HP, HO, HC, HR, HT, HE, HB, HD, HI, HL, HG, HS, HX, HM, HN ] ) ) )

    rule #blockHeaderHash(HP:Int, HO, HC, HR, HT, HE, HB, HD, HI, HL, HG, HS, HX, HM, HN)
         => #parseHexWord( Keccak256bytes( #rlpEncode( [ #wordBytes(HP), #wordBytes(HO), #addrBytes(HC)
                                                  , #wordBytes(HR), #wordBytes(HT), #wordBytes(HE)
                                                  , HB, HD, HI, HL, HG, HS, HX
                                                  , #wordBytes(HM), #padToWidth(8, #asByteStack(HN))
                                                  ]
                                                )
                                    )
                         )

    rule #blockHeaderHash(HP:Bytes, HO, HC, HR, HT, HE, HB, HD, HI, HL, HG, HS, HX, HM, HN, HF)
         => #parseHexWord( Keccak256bytes( #rlpEncode( [ HP, HO, HC, HR, HT, HE, HB, HD, HI, HL, HG, HS, HX, HM, HN, HF ] ) ) )

    rule #blockHeaderHash(HP:Int, HO, HC, HR, HT, HE, HB, HD, HI, HL, HG, HS, HX, HM, HN, HF)
         => #parseHexWord( Keccak256bytes( #rlpEncode( [ #wordBytes(HP), #wordBytes(HO), #addrBytes(HC)
                                                  , #wordBytes(HR), #wordBytes(HT), #wordBytes(HE)
                                                  , HB, HD, HI, HL, HG, HS, HX
                                                  , #wordBytes(HM), #padToWidth(8, #asByteStack(HN))
                                                  , HF
                                                  ]
                                                )
                                    )
                         )

    rule #blockHeaderHash(HP:Bytes, HO, HC, HR, HT, HE, HB, HD, HI, HL, HG, HS, HX, HM, HN, HF, WF)
         => #parseHexWord( Keccak256bytes( #rlpEncode( [ HP, HO, HC, HR, HT, HE, HB, HD, HI, HL, HG, HS, HX, HM, HN, HF, WF ] ) ) )

    rule #blockHeaderHash(HP:Int, HO, HC, HR, HT, HE, HB, HD, HI, HL, HG, HS, HX, HM, HN, HF, WF)
         => #parseHexWord( Keccak256bytes( #rlpEncode( [ #wordBytes(HP), #wordBytes(HO), #addrBytes(HC)
                                                  , #wordBytes(HR), #wordBytes(HT), #wordBytes(HE)
                                                  , HB, HD, HI, HL, HG, HS, HX
                                                  , #wordBytes(HM), #padToWidth(8, #asByteStack(HN))
                                                  , HF , #wordBytes(WF)
                                                  ]
                                                )
                                    )
                         )
```

- `#hashSignedTx` Takes transaction data. Returns the hash of the rlp-encoded transaction with R S and V.

```k
    syntax String ::= #hashSignedTx( Int , Int , Int , Account , Int , Bytes , Int , Bytes , Bytes ) [function]
                    | #hashTxData  ( TxData )                                                        [function]
 // -----------------------------------------------------------------------------------------------------------
    rule #hashSignedTx(TN, TP, TG, TT, TV, TD, TW, TR, TS)
      => Keccak256bytes( #rlpEncode([ TN, TP, TG, #addrBytes(TT), TV, TD, TW, TR, TS ]) )

    rule #hashTxData( TXDATA ) => Keccak256bytes(                #rlpEncodeTxData(TXDATA) )
        requires isLegacyTx    (TXDATA)
    rule #hashTxData( TXDATA ) => Keccak256bytes( b"\x01" +Bytes #rlpEncodeTxData(TXDATA) )
        requires isAccessListTx(TXDATA)
    rule #hashTxData( TXDATA ) => Keccak256bytes( b"\x02" +Bytes #rlpEncodeTxData(TXDATA) )
        requires isDynamicFeeTx(TXDATA)
```

The EVM test-sets are represented in JSON format with hex-encoding of the data and programs.
Here we provide some standard parser/unparser functions for that format.

Parsing
-------

These parsers can interperet hex-encoded strings as `Int`s, `Bytes`s, and `Map`s.

-   `#parseHexWord` interprets a string as a single hex-encoded `Word`.
-   `#parseHexBytes` interprets a string as a hex-encoded stack of bytes.
-   `#alignHexString` makes sure that the length of a (hex)string is even.
-   `#parseByteStack` interprets a string as a hex-encoded stack of bytes, but makes sure to remove the leading "0x".
-   `#parseWordStack` interprets a JSON list as a stack of `Word`.
-   `#parseMap` interprets a JSON key/value object as a map from `Word` to `Word`.
-   `#parseAddr` interprets a string as a 160 bit hex-endcoded address.
-   `#parseAccessListStorageKeys` interprets a JSON list object as a Set, casting each string element as a `Word`.

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

    syntax String ::= #alignHexString ( String ) [function, total]
 // --------------------------------------------------------------
    rule #alignHexString(S) => S             requires         lengthString(S) modInt 2 ==Int 0
    rule #alignHexString(S) => "0" +String S requires notBool lengthString(S) modInt 2 ==Int 0

    syntax Bytes ::= #parseHexBytes     ( String ) [function]
                   | #parseHexBytesAux  ( String ) [function]
                   | #parseByteStack    ( String ) [function, memo]
 // ---------------------------------------------------------
    rule #parseByteStack(S) => #parseHexBytes(replaceAll(S, "0x", ""))

    rule #parseHexBytes(S)  => #parseHexBytesAux(#alignHexString(S))
    rule #parseHexBytesAux("") => .Bytes
    rule #parseHexBytesAux(S)  => Int2Bytes(lengthString(S) /Int 2, String2Base(S, 16), BE)
      requires lengthString(S) >=Int 2

    syntax Map ::= #parseMap ( JSON ) [function]
 // --------------------------------------------
    rule #parseMap( { .JSONs                      } ) => .Map
    rule #parseMap( { _   : (VALUE:String) , REST } ) => #parseMap({ REST })                                                requires #parseHexWord(VALUE) ==K 0
    rule #parseMap( { KEY : (VALUE:String) , REST } ) => #parseMap({ REST }) [ #parseHexWord(KEY) <- #parseHexWord(VALUE) ] requires #parseHexWord(VALUE) =/=K 0

    syntax Int ::= #parseAddr ( String ) [function]
 // -----------------------------------------------
    rule #parseAddr(S) => #addr(#parseHexWord(S))

   syntax List ::= #parseAccessListStorageKeys ( JSONs )        [function]
                 | #parseAccessListStorageKeys ( JSONs , List ) [function, klabel(#parseAccessListStorageKeysAux)]
 // --------------------------------------------------------------------------------------------------------------
    rule #parseAccessListStorageKeys( J                           ) => #parseAccessListStorageKeys(J, .List)
    rule #parseAccessListStorageKeys([S:Bytes, REST], RESULT:List) => #parseAccessListStorageKeys([REST], ListItem(#asWord(S)) RESULT )
    rule #parseAccessListStorageKeys([ .JSONs       ], RESULT:List) => RESULT
```

Unparsing
---------
-   `#padByte` ensures that the `String` interperetation of a `Int` is wide enough.

```k
    syntax String ::= #padByte( String ) [function]
 // -----------------------------------------------
    rule #padByte( S ) => S             requires lengthString(S) ==K 2
    rule #padByte( S ) => "0" +String S requires lengthString(S) ==K 1

    syntax String ::= #unparseQuantity( Int ) [function]
 // ----------------------------------------------------
    rule #unparseQuantity( I ) => "0x" +String Base2String(I, 16)

    syntax String ::= #unparseData      ( Int, Int  ) [function]
                    | #unparseDataBytes ( Bytes )     [function]
 // ------------------------------------------------------------
    rule #unparseData( DATA, LENGTH ) => #unparseDataBytes(#padToWidth(LENGTH,#asByteStack(DATA)))

    rule #unparseDataBytes( DATA ) => replaceFirst(Base2String(#asInteger(#asByteStack(1) +Bytes DATA), 16), "1", "0x")
```

- `#addrBytes` Takes an Account and represents it as a 20-byte wide Bytes (or an empty Bytes for a null address)
- `#wordBytes` Takes an Int and represents it as a 32-byte wide Bytes

```k
    syntax Bytes ::= #addrBytes( Account ) [function]
                   | #wordBytes( Int )     [function]
 // -------------------------------------------------
    rule #addrBytes(.Account) => .Bytes
    rule #addrBytes(ACCT)     => #padToWidth(20, #asByteStack(ACCT)) requires #rangeAddress(ACCT)
    rule #wordBytes(WORD)     => #padToWidth(32, #asByteStack(WORD)) requires #rangeUInt(256, WORD)
```

Recursive Length Prefix (RLP)
=============================

RLP encoding is used extensively for executing the blocks of a transaction.
For details about RLP encoding, see the [YellowPaper Appendix B](http://gavwood.com/paper.pdf).

Encoding
--------

-   `#rlpEncodeInt` RLP encodes an arbitrary precision integer.
-   `#rlpEncodeWord` RLP encodes a 256-bit wide EVM word.
-   `#rlpEncodeAddress` RLP encodes a 160-bit wide Ethereum address (or the null address: .Account).
-   `#rlpEncodeBytes` RLP encodes a Bytes.
-   `#rlpEncodeString` RLP encodes a String. All code points must be less than `U+00FF`, and `U+00HH` is treated as the byte `0xHH`.
-   `#rlpEncode( JSON )` can take a JSON array and make an rlp encoding. It must be a JSON array! JSON objects aren't supported.
    example: `#rlpEncode( [ 0, 1, 1, "", #parseByteStack("0xef880") ] )`

```k
    syntax Bytes ::= #rlpEncodeInt ( Int )              [function]
                   | #rlpEncodeWord ( Int )             [function]
                   | #rlpEncodeAddress ( Account )      [function]
                   | #rlpEncodeString ( String )        [function]
                   | #rlpEncodeBytes ( Bytes )          [function]
                   | #rlpEncode ( JSON )                [function]
                   | #rlpEncode ( JSONs, StringBuffer ) [function, klabel(#rlpEncodeJsonAux)]
 // ------------------------------------------------------------------------------------------
    rule #rlpEncodeInt(0) => b"\x80"
    rule #rlpEncodeInt(WORD) => #asByteStack(WORD) requires WORD >Int 0 andBool WORD <Int 128
    rule #rlpEncodeInt(WORD) => #rlpEncodeBytes(#asByteStack(WORD)) requires WORD >=Int 128

    rule #rlpEncodeWord(WORD) => #rlpEncodeBytes(#wordBytes(WORD))

    rule #rlpEncodeAddress(ACCT) => #rlpEncodeBytes(#addrBytes(ACCT))

    rule #rlpEncodeString(STR) => #rlpEncodeBytes(String2Bytes(STR))

    rule #rlpEncodeBytes(BYTES) => b"\x80"                    requires lengthBytes(BYTES)  <Int 1
    rule #rlpEncodeBytes(BYTES) => BYTES                      requires lengthBytes(BYTES) ==Int 1 andBool #asInteger(substrBytes(BYTES, 0, 1)) <Int 128
    rule #rlpEncodeBytes(BYTES) => #rlpEncodeLength(BYTES, 128) [owise]

    syntax JSON ::= Bytes
    rule #rlpEncode( [ J:JSONs ] ) => #rlpEncodeLength( #rlpEncode(J, .StringBuffer) , 192 )

    rule #rlpEncode( .JSONs                   , BUF ) => String2Bytes(StringBuffer2String(BUF))
    rule #rlpEncode( (J:Int,       REST:JSONs), BUF ) => #rlpEncode(REST, BUF +String Bytes2String(#rlpEncodeInt(J)   ))
    rule #rlpEncode( (J:String,    REST:JSONs), BUF ) => #rlpEncode(REST, BUF +String Bytes2String(#rlpEncodeString(J)))
    rule #rlpEncode( (J:Bytes,     REST:JSONs), BUF ) => #rlpEncode(REST, BUF +String Bytes2String(#rlpEncodeBytes(J) ))
    rule #rlpEncode( ([ J ],       REST:JSONs), BUF ) => #rlpEncode(REST, BUF +String Bytes2String(#rlpEncode([ J ])  ))

    syntax Bytes ::= #rlpEncodeLength ( Bytes , Int )          [function]
                   | #rlpEncodeLength ( Bytes , Int , Bytes ) [function, klabel(#rlpEncodeLengthAux)]
 // ----------------------------------------------------------------------------------------------------
    rule #rlpEncodeLength(BYTES, OFFSET) => #asByteStack(lengthBytes(BYTES) +Int OFFSET) +Bytes BYTES         requires           lengthBytes(BYTES) <Int 56
    rule #rlpEncodeLength(BYTES, OFFSET) => #rlpEncodeLength(BYTES, OFFSET, #asByteStack(lengthBytes(BYTES))) requires notBool ( lengthBytes(BYTES) <Int 56 )
    rule #rlpEncodeLength(BYTES, OFFSET, BL) => #asByteStack(lengthBytes(BL) +Int OFFSET +Int 55) +Bytes BL +Bytes BYTES

    syntax Bytes ::= #rlpEncodeFullAccount( Int, Int, Map, Bytes ) [function]
 // --------------------------------------------------------------------------
    rule [rlpAcct]: #rlpEncodeFullAccount( NONCE, BAL, STORAGE, CODE )
                 => #rlpEncodeLength(        #rlpEncodeInt(NONCE)
                                      +Bytes #rlpEncodeInt(BAL)
                                      +Bytes #rlpEncodeBytes( #parseByteStack( Keccak256bytes( #rlpEncodeMerkleTree( #storageRoot( STORAGE ) ) ) ) )
                                      +Bytes #rlpEncodeBytes( #parseByteStack( Keccak256bytes( CODE ) ) )
                                    , 192
                                    )

    syntax Bytes ::= #rlpEncodeReceipt ( Int , Int , Bytes , List ) [function]
                   | #rlpEncodeLogs    ( List )                     [function]
                   | #rlpEncodeLogsAux ( List, StringBuffer )       [function]
                   | #rlpEncodeTopics  ( List, StringBuffer )       [function]
 // ---------------------------------------------------------------------------
    rule [rlpReceipt]: #rlpEncodeReceipt(RS, RG, RB, RL)
                    => #rlpEncodeLength(        #rlpEncodeInt(RS)
                                         +Bytes #rlpEncodeInt(RG)
                                         +Bytes #rlpEncodeBytes(RB)
                                         +Bytes #rlpEncodeLogs(RL)
                                       , 192
                                       )

    rule #rlpEncodeLogs( LOGS ) => #rlpEncodeLogsAux( LOGS, .StringBuffer )

    rule #rlpEncodeLogsAux( .List, OUT ) => #rlpEncodeLength(String2Bytes(StringBuffer2String(OUT)),192)
    rule #rlpEncodeLogsAux( ( ListItem({ ACCT | TOPICS | DATA }) => .List ) _
                          , ( OUT => OUT +String Bytes2String(
                              #rlpEncodeLength(        #rlpEncodeAddress(ACCT)
                                                +Bytes #rlpEncodeTopics(TOPICS,.StringBuffer)
                                                +Bytes #rlpEncodeBytes(DATA)
                                               , 192
                                               ))
                            )
                          )

    rule #rlpEncodeTopics( .List, OUT ) => #rlpEncodeLength(String2Bytes(StringBuffer2String(OUT)),192)
    rule #rlpEncodeTopics( ( ListItem( X:Int ) => .List ) _
                         , ( OUT => OUT +String Bytes2String( #rlpEncodeWord(X) ) )
                         )

    syntax Bytes ::= #rlpEncodeTxData( TxData ) [function]
 // -------------------------------------------------------
    rule #rlpEncodeTxData( LegacyTxData( TN, TP, TG, TT, TV, TD ) )
      => #rlpEncode( [ TN, TP, TG, #addrBytes(TT), TV, TD ] )

    rule #rlpEncodeTxData( LegacyProtectedTxData( TN, TP, TG, TT, TV, TD, CID ) )
      => #rlpEncode( [ TN, TP, TG, #addrBytes(TT), TV, TD, CID, "", "" ] )

    rule #rlpEncodeTxData( AccessListTxData( TN, TP, TG, TT, TV, TD, CID, [TA] ) )
      => #rlpEncode( [ CID, TN, TP, TG, #addrBytes(TT), TV, TD, [TA] ] )

    rule #rlpEncodeTxData( DynamicFeeTxData(TN, TPF, TM, TG, TT, TV, DATA, CID, [TA]) )
      => #rlpEncode( [ CID, TN, TPF, TM, TG, #addrBytes(TT), TV, DATA, [TA] ] )

    syntax Bytes ::= #rlpEncodeMerkleTree ( MerkleTree ) [function]
 // ----------------------------------------------------------------
    rule #rlpEncodeMerkleTree ( .MerkleTree ) => b"\x80"

    rule #rlpEncodeMerkleTree ( MerkleLeaf ( PATH, VALUE ) )
      => #rlpEncodeLength(        #rlpEncodeBytes( #HPEncode( PATH, 1 ) )
                           +Bytes #rlpEncodeString( VALUE )
                         , 192
                         )

    rule #rlpEncodeMerkleTree ( MerkleExtension ( PATH, TREE ) )
      => #rlpEncodeLength(        #rlpEncodeBytes( #HPEncode( PATH, 0 ) )
                           +Bytes #rlpMerkleH( #rlpEncodeMerkleTree( TREE ) )
                         , 192
                         )

    rule #rlpEncodeMerkleTree ( MerkleBranch ( M , VALUE ) )
      => #rlpEncodeLength(        MerkleMapRLP(M, 0) +Bytes MerkleMapRLP(M, 1)
                           +Bytes MerkleMapRLP(M, 2) +Bytes MerkleMapRLP(M, 3)
                           +Bytes MerkleMapRLP(M, 4) +Bytes MerkleMapRLP(M, 5)
                           +Bytes MerkleMapRLP(M, 6) +Bytes MerkleMapRLP(M, 7)
                           +Bytes MerkleMapRLP(M, 8) +Bytes MerkleMapRLP(M, 9)
                           +Bytes MerkleMapRLP(M,10) +Bytes MerkleMapRLP(M,11)
                           +Bytes MerkleMapRLP(M,12) +Bytes MerkleMapRLP(M,13)
                           +Bytes MerkleMapRLP(M,14) +Bytes MerkleMapRLP(M,15)
                           +Bytes #rlpEncodeString( VALUE )
                         , 192
                         )

    syntax Bytes ::= MerkleMapRLP( Map, Int ) [function]
 // -----------------------------------------------------
    rule MerkleMapRLP(M, I) => #rlpMerkleH( #rlpEncodeMerkleTree( { M[I] orDefault .MerkleTree }:>MerkleTree ) )

    syntax Bytes ::= #rlpMerkleH ( Bytes ) [function,klabel(MerkleRLPAux)]
 // ------------------------------------------------------------------------
    rule #rlpMerkleH ( X ) => #rlpEncodeBytes( #parseByteStack( Keccak256bytes( X ) ) )
      requires lengthBytes(X) >=Int 32

    rule #rlpMerkleH ( X ) => X
      requires notBool lengthBytes(X) >=Int 32
```

Decoding
--------

-   `#rlpDecode` RLP decodes a single `Bytes` into a `JSON`.
-   `#rlpDecodeList` RLP decodes a single `Bytes` into a `JSONs`, interpereting the input as the RLP encoding of a list.

```k
    syntax JSON ::= #rlpDecode(Bytes)               [function]
                  | #rlpDecode(Bytes, LengthPrefix) [function, klabel(#rlpDecodeAux)]
 // ----------------------------------------------------------------------------------
    rule #rlpDecode(BYTES) => #rlpDecode(BYTES, #decodeLengthPrefix(BYTES, 0))
    rule #rlpDecode(BYTES,  #str( LEN, POS)) => substrBytes(BYTES, POS, POS +Int LEN)
    rule #rlpDecode(BYTES, #list(_LEN, POS)) => [#rlpDecodeList(BYTES, POS)]

    syntax JSONs ::= #rlpDecodeList(Bytes, Int)               [function]
                   | #rlpDecodeList(Bytes, Int, LengthPrefix) [function, klabel(#rlpDecodeListAux)]
 // ------------------------------------------------------------------------------------------------
    rule #rlpDecodeList(BYTES, POS) => #rlpDecodeList(BYTES, POS, #decodeLengthPrefix(BYTES, POS)) requires POS <Int lengthBytes(BYTES)
    rule #rlpDecodeList(    _,   _) => .JSONs [owise]
    rule #rlpDecodeList(BYTES, POS, _:LengthPrefixType(L, P)) => #rlpDecode(substrBytes(BYTES, POS, L +Int P)) , #rlpDecodeList(BYTES, L +Int P)

    syntax LengthPrefixType ::= "#str" | "#list"
    syntax LengthPrefix ::= LengthPrefixType "(" Int "," Int ")"
                          | #decodeLengthPrefix ( Bytes , Int )                                [function]
                          | #decodeLengthPrefix ( Bytes , Int , Int )                          [function, klabel(#decodeLengthPrefixAux)]
                          | #decodeLengthPrefixLength ( LengthPrefixType , Bytes , Int , Int ) [function]
                          | #decodeLengthPrefixLength ( LengthPrefixType , Int   , Int , Int ) [function, klabel(#decodeLengthPrefixLengthAux)]
 // --------------------------------------------------------------------------------------------------------------------------------------------
    rule #decodeLengthPrefix(BYTES, START) => #decodeLengthPrefix(BYTES, START, #asWord(substrBytes(BYTES, START, START +Int 1)))

    rule #decodeLengthPrefix(    _, START, B0) => #str(1, START)                                     requires B0 <Int 128
    rule #decodeLengthPrefix(    _, START, B0) => #str(B0 -Int 128, START +Int 1)                    requires B0 >=Int 128 andBool B0 <Int (128 +Int 56)
    rule #decodeLengthPrefix(BYTES, START, B0) => #decodeLengthPrefixLength(#str, BYTES, START, B0)  requires B0 >=Int (128 +Int 56) andBool B0 <Int 192
    rule #decodeLengthPrefix(    _, START, B0) => #list(B0 -Int 192, START +Int 1)                   requires B0 >=Int 192 andBool B0 <Int 192 +Int 56
    rule #decodeLengthPrefix(BYTES, START, B0) => #decodeLengthPrefixLength(#list, BYTES, START, B0) [owise]

    rule #decodeLengthPrefixLength(#str,  BYTES, START, B0) => #decodeLengthPrefixLength(#str,  START, B0 -Int 128 -Int 56 +Int 1, #asWord(substrBytes(BYTES, START +Int 1, START +Int 1 +Int (B0 -Int 128 -Int 56 +Int 1))))
    rule #decodeLengthPrefixLength(#list, BYTES, START, B0) => #decodeLengthPrefixLength(#list, START, B0 -Int 192 -Int 56 +Int 1, #asWord(substrBytes(BYTES, START +Int 1, START +Int 1 +Int (B0 -Int 192 -Int 56 +Int 1))))
    rule #decodeLengthPrefixLength(TYPE, START, LL, L) => TYPE(L, START +Int 1 +Int LL)

    syntax JSONs ::= #rlpDecodeTransaction(Bytes) [function]
 // --------------------------------------------------------
    rule #rlpDecodeTransaction(T) => #range(T, 0, 1), #rlpDecode(#range(T, 1, lengthBytes(T) -Int 1))
```

Merkle Patricia Tree
====================

- Appendix C and D from the Ethereum Yellow Paper
- https://github.com/ethereum/wiki/wiki/Patricia-Tree

```k
    syntax KItem ::= Int | MerkleTree // For testing purposes

    syntax MerkleTree ::= ".MerkleTree"
                        | MerkleBranch    ( Map, String )
                        | MerkleExtension ( Bytes, MerkleTree )
                        | MerkleLeaf      ( Bytes, String )
 // -------------------------------------------------------

    syntax MerkleTree ::= MerkleUpdate ( MerkleTree, String, String ) [function]
                        | MerkleUpdate ( MerkleTree,  Bytes, String ) [function,klabel(MerkleUpdateAux)]
                        | MerklePut    ( MerkleTree,  Bytes, String ) [function]
                        | MerkleDelete ( MerkleTree,  Bytes )         [function]
 // ----------------------------------------------------------------------------
    rule MerkleUpdate ( TREE, S:String, VALUE ) => MerkleUpdate ( TREE, #nibbleize ( String2Bytes( S ) ), VALUE )

    rule MerkleUpdate ( TREE, PATH:Bytes, VALUE ) => MerklePut ( TREE, PATH, VALUE ) requires VALUE =/=String ""
    rule MerkleUpdate ( TREE, PATH:Bytes, ""    ) => MerkleDelete ( TREE, PATH )

    rule MerklePut ( .MerkleTree, PATH:Bytes, VALUE ) => MerkleLeaf ( PATH, VALUE )

    rule MerklePut ( MerkleLeaf ( LEAFPATH, _ ), PATH, VALUE )
      => MerkleLeaf( LEAFPATH, VALUE )
      requires LEAFPATH ==K PATH

    rule MerklePut ( MerkleLeaf ( LEAFPATH, LEAFVALUE ), PATH, VALUE )
      => MerklePut ( MerklePut ( MerkleBranch( .Map, "" ), LEAFPATH, LEAFVALUE ), PATH, VALUE )
      requires lengthBytes( LEAFPATH ) >Int 0
       andBool lengthBytes( PATH ) >Int 0
       andBool LEAFPATH[0] =/=Int PATH[0]

    rule MerklePut ( MerkleLeaf ( LEAFPATH, LEAFVALUE ), PATH, VALUE )
      => #merkleExtensionBuilder( .Bytes, LEAFPATH, LEAFVALUE, PATH, VALUE )
      requires LEAFPATH =/=K PATH
       andBool lengthBytes( LEAFPATH ) >Int 0
       andBool lengthBytes( PATH )     >Int 0
       andBool LEAFPATH[0] ==Int PATH[0]

    rule MerklePut ( MerkleExtension ( EXTPATH, EXTTREE ), PATH, VALUE )
      => MerkleExtension ( EXTPATH, MerklePut ( EXTTREE, .Bytes, VALUE ) )
      requires EXTPATH ==K PATH

    rule MerklePut ( MerkleExtension ( EXTPATH, EXTTREE ), PATH, VALUE )
      => #merkleExtensionBrancher( MerklePut( MerkleBranch( .Map, "" ), PATH, VALUE ), EXTPATH, EXTTREE )
      requires lengthBytes( PATH ) >Int 0
       andBool EXTPATH[0] =/=Int PATH[0]

    rule MerklePut ( MerkleExtension ( EXTPATH, EXTTREE ), PATH, VALUE )
      => #merkleExtensionSplitter( .Bytes, EXTPATH, EXTTREE, PATH, VALUE )
      requires EXTPATH =/=K PATH
       andBool lengthBytes( PATH ) >Int 0
       andBool EXTPATH[0] ==Int PATH[0]

    rule MerklePut ( MerkleBranch( M, _ ), PATH, VALUE )
      => MerkleBranch( M, VALUE )
      requires lengthBytes( PATH ) ==Int 0

    rule MerklePut ( MerkleBranch( M, BRANCHVALUE ), PATH, VALUE )
      => #merkleUpdateBranch ( M, BRANCHVALUE, PATH[0], #range(PATH, 1, lengthBytes(PATH) -Int 1), VALUE )
      requires lengthBytes( PATH ) >Int 0

    rule MerkleDelete( .MerkleTree, _ ) => .MerkleTree

    rule MerkleDelete( MerkleLeaf( LPATH, _V ), PATH ) => .MerkleTree                           requires LPATH ==K  PATH
    rule MerkleDelete( MerkleLeaf( LPATH,  V ), PATH ) => MerkleCheck( MerkleLeaf( LPATH, V ) ) requires LPATH =/=K PATH

    rule MerkleDelete( MerkleExtension( EXTPATH, TREE ), PATH ) => MerkleExtension( EXTPATH, TREE ) requires notBool (lengthBytes(EXTPATH) <=Int lengthBytes(PATH) andBool #range(PATH, 0, lengthBytes(EXTPATH)) ==K EXTPATH)
    rule MerkleDelete( MerkleExtension( EXTPATH, TREE ), PATH )
      => MerkleCheck( MerkleExtension( EXTPATH, MerkleDelete( TREE, #range(PATH, lengthBytes(EXTPATH), lengthBytes(PATH) -Int lengthBytes(EXTPATH)) ) ) )
      requires lengthBytes(EXTPATH) <=Int lengthBytes(PATH) andBool #range(PATH, 0, lengthBytes(EXTPATH)) ==K EXTPATH

    rule MerkleDelete( MerkleBranch( M, _V ), PATH ) => MerkleCheck( MerkleBranch( M, "" ) ) requires lengthBytes(PATH) ==Int 0
    rule MerkleDelete( MerkleBranch( M,  V ), PATH ) => MerkleBranch( M, V )                 requires lengthBytes(PATH) >Int 0 andBool notBool PATH[0] in_keys(M)
    rule MerkleDelete( MerkleBranch( M,  V ), PATH )
      => MerkleCheck( MerkleBranch( M[PATH[0] <- MerkleDelete( {M[PATH[0]]}:>MerkleTree, #range(PATH, 1, lengthBytes(PATH) -Int 1) )], V ) )
      requires lengthBytes(PATH) >Int 0 andBool PATH[0] in_keys(M)

    syntax MerkleTree ::= MerkleCheck( MerkleTree ) [function]
 // ----------------------------------------------------------
    rule MerkleCheck( TREE ) => TREE [owise]

    rule MerkleCheck( MerkleLeaf( _, "" ) => .MerkleTree )

    rule MerkleCheck( MerkleBranch( .Map                   , V  ) => MerkleLeaf( .Bytes, V )                             )
    rule MerkleCheck( MerkleBranch( X |-> T                , "" ) => MerkleExtension( #range(#asByteStack(X), 0, 1), T ) ) requires T =/=K .MerkleTree
    rule MerkleCheck( MerkleBranch( M => #cleanBranchMap(M), _  )                                                        ) requires .MerkleTree in values(M)

    rule MerkleCheck( MerkleExtension( _, .MerkleTree                                      ) => .MerkleTree               )
    rule MerkleCheck( MerkleExtension( P1, MerkleLeaf( P2, V )                             ) => MerkleLeaf( P1 +Bytes P2, V ) )
    rule MerkleCheck( MerkleExtension( P1 => P1 +Bytes P2, MerkleExtension( P2, TREE ) => TREE )                              )
```

- `MerkleUpdateMap` Takes a mapping of `Bytes |-> String` and generates a trie

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
    syntax Bytes ::= #nibbleize ( Bytes ) [function]
                   | #byteify   ( Bytes ) [function]
 // ------------------------------------------------
    rule #nibbleize ( B ) => (          #range( #asByteStack ( B [ 0 ] /Int 16 ), 0, 1 )
                               +Bytes ( #range( #asByteStack ( B [ 0 ] %Int 16 ), 0, 1 ) )
                             ) +Bytes #nibbleize ( #range(B, 1, lengthBytes(B) -Int 1) )
      requires lengthBytes(B) >Int 0

    rule #nibbleize ( B ) => .Bytes requires notBool lengthBytes(B) >Int 0

    rule #byteify ( B ) =>    #range( #asByteStack ( B[0] *Int 16 +Int B[1] ), 0, 1 )
                       +Bytes #byteify ( #range( B, 2, lengthBytes(B) -Int 2 ) )
      requires lengthBytes(B) >Int 0

    rule #byteify ( B ) => .Bytes requires notBool lengthBytes(B) >Int 0

    syntax Bytes ::= #HPEncode ( Bytes, Int ) [function]
 // ----------------------------------------------------
    rule #HPEncode ( X, T ) => #asByteStack ( ( HPEncodeAux(T) +Int 1 ) *Int 16 +Int X[0] ) +Bytes #byteify( #range(X, 1, lengthBytes(X) -Int 1) )
      requires lengthBytes(X) %Int 2 =/=Int 0

    rule #HPEncode ( X, T ) => #range(#asByteStack ( HPEncodeAux(T) *Int 16 ), 0, 1) +Bytes #byteify( X )
      requires notBool lengthBytes(X) %Int 2 =/=Int 0

    syntax Int ::= HPEncodeAux ( Int ) [function]
 // ---------------------------------------------
    rule HPEncodeAux ( X ) => 0 requires         X ==Int 0
    rule HPEncodeAux ( X ) => 2 requires notBool X ==Int 0

    syntax Map ::= #cleanBranchMap    ( Map )            [function]
                 | #cleanBranchMapAux ( Map, List, Set ) [function]
 // ---------------------------------------------------------------
    rule #cleanBranchMap( M ) => #cleanBranchMapAux( M, keys_list(M), .Set )

    rule #cleanBranchMapAux(                   M,                        .List,                      S ) => removeAll( M, S )
    rule #cleanBranchMapAux( X |-> .MerkleTree _, (ListItem(X) => .List) _    , (.Set => SetItem(X)) _ )
    rule #cleanBranchMapAux(                   _, (ListItem(_) => .List) _    ,                      _ ) [owise]

    syntax MerkleTree ::= #merkleUpdateBranch ( Map, String, Int, Bytes, String ) [function]
 // ----------------------------------------------------------------------------------------
    rule #merkleUpdateBranch ( X |-> TREE M, BRANCHVALUE, X, PATH, VALUE )
      => MerkleBranch( M[X <- MerklePut( TREE, PATH, VALUE )], BRANCHVALUE )

    rule #merkleUpdateBranch ( M, BRANCHVALUE, X, PATH, VALUE )
      => MerkleBranch( M[X <- MerkleLeaf( PATH, VALUE )], BRANCHVALUE ) [owise]

    syntax MerkleTree ::= #merkleExtensionBuilder(    Bytes , Bytes , String , Bytes , String ) [function]
                        | #merkleExtensionBuilderAux( Bytes , Bytes , String , Bytes , String ) [function]
 // ------------------------------------------------------------------------------------------------------
    rule #merkleExtensionBuilder(PATH, P1, V1, P2, V2)
      => #merkleExtensionBuilderAux(PATH, P1, V1, P2, V2)
      requires lengthBytes(P1) >Int 0
       andBool lengthBytes(P2) >Int 0

    rule #merkleExtensionBuilder(PATH, P1, V1, P2, V2)
      => MerkleExtension( PATH, MerklePut( MerklePut( MerkleBranch( .Map, "" ), P1, V1 ), P2, V2 ) )
      [owise]

    rule #merkleExtensionBuilderAux( PATH, P1, V1, P2, V2 )
      => #merkleExtensionBuilder( PATH +Bytes (#range(P1, 0, 1))
                                , #range(P1, 1, lengthBytes(P1) -Int 1), V1
                                , #range(P2, 1, lengthBytes(P2) -Int 1), V2
                                )
      requires P1[0] ==Int P2[0]

    rule #merkleExtensionBuilderAux( PATH, P1, V1, P2, V2 )
      => MerkleExtension( PATH, MerklePut( MerklePut( MerkleBranch( .Map, "" ), P1, V1 ), P2, V2 ) )
      [owise]

    syntax MerkleTree ::= #merkleExtensionBrancher ( MerkleTree, Bytes, MerkleTree ) [function]
 // -------------------------------------------------------------------------------------------
    rule #merkleExtensionBrancher( MerkleBranch(M, VALUE), PATH, EXTTREE )
      => MerkleBranch( M[PATH[0] <- MerkleExtension( #range(PATH, 1, lengthBytes(PATH) -Int 1), EXTTREE )], VALUE )
      requires lengthBytes(PATH) >Int 1

    rule #merkleExtensionBrancher( MerkleBranch(M, VALUE), PATH, EXTTREE )
      => MerkleBranch( M[PATH[0] <- EXTTREE], VALUE )
      requires lengthBytes(PATH) ==Int 1

    syntax MerkleTree ::= #merkleExtensionSplitter ( Bytes, Bytes, MerkleTree, Bytes, String ) [function]
 // -----------------------------------------------------------------------------------------------------
    rule #merkleExtensionSplitter( PATH => PATH +Bytes (#range(P1, 0, 1))
                                 , P1   => #range(P1, 1, lengthBytes(P1) -Int 1), _
                                 , P2   => #range(P2, 1, lengthBytes(P2) -Int 1), _
                                 )
      requires lengthBytes(P1) >Int 0
       andBool lengthBytes(P2) >Int 0
       andBool P1[0] ==Int P2[0]

    rule #merkleExtensionSplitter( PATH, P1, TREE, P2, VALUE )
      => MerkleExtension( PATH, #merkleExtensionBrancher( MerklePut( MerkleBranch( .Map, "" ), P2, VALUE ), P1, TREE ) )
      requires lengthBytes(P1) >Int 0
       andBool lengthBytes(P2) >Int 0
       andBool P1[0] =/=Int P2[0]

    rule #merkleExtensionSplitter( PATH, P1, TREE, P2, VALUE )
      => MerkleExtension( PATH, MerklePut( TREE, P2, VALUE ) )
      requires lengthBytes(P1) ==Int 0

    rule #merkleExtensionSplitter( PATH, P1, TREE, P2, VALUE )
      => MerkleExtension( PATH, #merkleExtensionBrancher( MerklePut( MerkleBranch( .Map, "" ), P2, VALUE ), P1, TREE ) )
      requires lengthBytes(P2) ==Int 0
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
      => #intMap2StorageMapAux( #wordBytes(K) |-> #rlpEncodeInt({IMAP[K]}:>Int) SMAP, IMAP, REST )
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
    syntax Map ::= #precompiledAccountsMap   ( Set )       [function]
                 | #precompiledAccountsMapAux( List, Map ) [function]
 // -----------------------------------------------------------------
    rule #precompiledAccountsMap( ACCTS ) => #precompiledAccountsMapAux( Set2List( ACCTS ), .Map )

    rule #precompiledAccountsMapAux( .List, M ) => M
    rule #precompiledAccountsMapAux( (ListItem( ACCT ) => .List) _, M => M[#parseByteStack ( #unparseData( ACCT, 20 ) ) <- #emptyContractRLP] )

    syntax Bytes ::= "#emptyContractRLP" [function]
 // ------------------------------------------------
    rule #emptyContractRLP => #rlpEncodeLength(        #rlpEncodeInt(0)
                                                +Bytes #rlpEncodeInt(0)
                                                +Bytes #rlpEncodeBytes( #parseByteStack( Keccak256bytes(b"\x80") ) )
                                                +Bytes #rlpEncodeBytes( #parseByteStack( Keccak256bytes(b"") ) )
                                              , 192
                                              )
endmodule
```
