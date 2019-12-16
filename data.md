EVM Words
=========

```k
requires "krypto.k"
requires "evm-types.k"
requires "json.k"
requires "serialization.k"
```

```k
module EVM-DATA
    imports KRYPTO
    imports EVM-TYPES
    imports SERIALIZATION
    imports STRING-BUFFER
    imports MAP-SYMBOLIC
    imports COLLECTIONS
    imports JSON
```

```{.k .concrete .bytes}
    imports BYTES
```

-   `keccak` serves as a wrapper around the `Keccak256` in `KRYPTO`.

```k
    syntax Int ::= keccak ( ByteArray ) [function, smtlib(smt_keccak)]
 // ------------------------------------------------------------------
    rule [keccak]: keccak(WS) => #parseHexWord(Keccak256(#unparseByteStack(WS)))
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
    rule [#lookup.some]: #lookup( (KEY |-> VAL) M, KEY ) => VAL
    rule [#lookup.none]: #lookup(               M, KEY ) => 0 requires notBool KEY in_keys(M)
```

```k
endmodule
```
