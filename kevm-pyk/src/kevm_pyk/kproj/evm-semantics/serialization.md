Parsing/Unparsing
=================

```k
requires "plugin/krypto.md"
requires "evm-types.md"
requires "json.md"
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
    syntax MInt{256} ::= keccakMInt256 ( Bytes ) [function]
 // -------------------------------------------------------
    rule keccakMInt256(WS) => Bytes2MInt(padLeftBytes(Keccak256raw(WS), 32, 0))::MInt{256}
```

-   `#newAddr` computes the address of a new account given the address and nonce of the creating account.

```k
    syntax Int ::= #newAddr ( Int , Int )         [symbol(newAddr), total, function]
                 | #newAddr ( Int , Int , Bytes ) [symbol(newAddrCreate2), total, function]
 // --------------------------------------------------------------------------------
    rule [#newAddr]:        #newAddr(ACCT, NONCE) => #addr(#parseHexWord(Keccak256(#rlpEncode([#addrBytes(ACCT), NONCE]))))                                                                        [concrete]
    rule [#newAddrCreate2]: #newAddr(ACCT, SALT, INITCODE) => #addr(#parseHexWord(Keccak256(b"\xff" +Bytes #addrBytes(ACCT) +Bytes #wordBytes(SALT) +Bytes #parseByteStack(Keccak256(INITCODE))))) [concrete]

    syntax MInt{256} ::= #newAddrMInt256 ( MInt{256} , MInt{256} )         [function]
                       | #newAddrMInt256 ( MInt{256} , MInt{256} , Bytes ) [function]
 // ---------------------------------------------------------------------------------
    rule #newAddrMInt256(ACCT, NONCE) => Int2MInt(#newAddr(MInt2Unsigned(ACCT), MInt2Unsigned(NONCE)))::MInt{256}
    rule #newAddrMInt256(ACCT, SALT, INITCODE) => Int2MInt(#newAddr(MInt2Unsigned(ACCT), MInt2Unsigned(SALT), INITCODE))::MInt{256}
```

- `#sender` computes the sender of the transaction from its data and signature.
- `sender` is used by the `ecrec` precompile and does not need to adapt the parameters.

```k
    syntax Account ::= #sender ( Bytes  , Int , Bytes , Bytes )       [function, symbol(senderBytes), total]
                     | #sender ( Bytes )                              [function, symbol(senderReturn)      ]
 // --------------------------------------------------------------------------------------------------------
    rule [sender]: #sender(HT, TW, TR, TS) => #sender(ECDSARecover(HT, TW, TR, TS))

    rule #sender(b"")   => .Account
    rule #sender(BYTES) => #addr(#parseHexWord(Keccak256(BYTES))) requires BYTES =/=K b""
```

The EVM test-sets are represented in JSON format with hex-encoding of the data and programs.
Here we provide some standard parser/unparser functions for that format.

Parsing
-------

These parsers can interpret hex-encoded strings as `Int`s, `Bytes`s, and `Map`s.

-   `#parseHexWord` interprets a string as a single hex-encoded `Word`.
-   `#parseHexBytes` interprets a string as a hex-encoded stack of bytes.
-   `#alignHexString` makes sure that the length of a (hex)string is even.
-   `#parseByteStack` interprets a string as a hex-encoded stack of bytes, but makes sure to remove the leading "0x".

```k
    syntax Int ::= #parseWord    ( String ) [symbol(#parseWord), function]
                 | #parseHexWord ( String ) [symbol(#parseHexWord), function]
 // -------------------------------------------------------------------------
    rule #parseHexWord("")   => 0
    rule #parseHexWord("0x") => 0
    rule #parseHexWord(S)    => String2Base(replaceAll(S, "0x", ""), 16) requires (S =/=String "") andBool (S =/=String "0x")

    rule #parseWord("") => 0
    rule #parseWord(S)  => #parseHexWord(S) requires lengthString(S) >=Int 2 andBool substrString(S, 0, 2) ==String "0x"
    rule #parseWord(S)  => String2Int(S) [owise]

    syntax String ::= #alignHexString ( String ) [symbol(#alignHexString), function, total]
 // ---------------------------------------------------------------------------------------
    rule #alignHexString(S) => S             requires         lengthString(S) modInt 2 ==Int 0
    rule #alignHexString(S) => "0" +String S requires notBool lengthString(S) modInt 2 ==Int 0

    syntax Bytes ::= #parseHexBytes     ( String ) [symbol(parseHexBytes), function]
                   | #parseHexBytesAux  ( String ) [symbol(parseHexBytesAux), function]
                   | #parseByteStack    ( String ) [symbol(parseByteStack), function, memo]
 // ---------------------------------------------------------------------------------------
    rule #parseByteStack(S) => #parseHexBytes(replaceAll(S, "0x", ""))
    rule #parseHexBytes(S)  => #parseHexBytesAux(#alignHexString(S))

    rule #parseHexBytesAux("") => .Bytes
    rule #parseHexBytesAux(S)  => Int2Bytes(lengthString(S) /Int 2, String2Base(S, 16), BE) requires lengthString(S) >=Int 2
```

Unparsing
---------

- `#addrBytes` Takes an Account and represents it as a 20-byte wide Bytes (or an empty Bytes for a null address)
- `#wordBytes` Takes an Int and represents it as a 32-byte wide Bytes

```k
    syntax Bytes ::= #addrBytes ( Account ) [symbol(#addrBytes), function]
                   | #wordBytes ( Int )     [symbol(#wordBytes), function]
 // ----------------------------------------------------------------------
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
    syntax Bytes ::= #rlpEncodeInt ( Int )              [symbol(#rlpEncodeInt    ), function]
                   | #rlpEncodeWord ( Int )             [symbol(#rlpEncodeWord   ), function]
                   | #rlpEncodeAddress ( Account )      [symbol(#rlpEncodeAddress), function]
                   | #rlpEncodeString ( String )        [symbol(#rlpEncodeString ), function]
                   | #rlpEncodeBytes ( Bytes )          [symbol(#rlpEncodeBytes  ), function]
                   | #rlpEncode ( JSON )                [symbol(#rlpEncode       ), function]
                   | #rlpEncode ( JSONs, StringBuffer ) [symbol(#rlpEncodeJsonAux), function]
 // -----------------------------------------------------------------------------------------
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

    syntax Bytes ::= #rlpEncodeLength ( Bytes , Int )         [symbol(#rlpEncodeLength), function]
                   | #rlpEncodeLength ( Bytes , Int , Bytes ) [symbol(#rlpEncodeLengthAux), function]
 // -------------------------------------------------------------------------------------------------
    rule #rlpEncodeLength(BYTES, OFFSET) => #asByteStack(lengthBytes(BYTES) +Int OFFSET) +Bytes BYTES         requires           lengthBytes(BYTES) <Int 56
    rule #rlpEncodeLength(BYTES, OFFSET) => #rlpEncodeLength(BYTES, OFFSET, #asByteStack(lengthBytes(BYTES))) requires notBool ( lengthBytes(BYTES) <Int 56 )
    rule #rlpEncodeLength(BYTES, OFFSET, BL) => #asByteStack(lengthBytes(BL) +Int OFFSET +Int 55) +Bytes BL +Bytes BYTES

endmodule
```
