Implementation of Execution Layer Requests
------------------------------------------
```k
requires "serialization.md"
```

```k
module EVM-REQUESTS
    imports SERIALIZATION
```

A `requests` object consists of a `request_type` byte prepended to an opaque byte array `request_data`.
The `request_data` contains zero or more encoded request objects.
```
requests = request_type ++ request_data
```
Each request type will define its own requests object with its own `request_data` format.

In order to compute the commitment, an intermediate hash list is first built by hashing all non-empty requests elements of the block requests list.
Items with empty `request_data` are excluded, i.e. the intermediate list skips requests items which contain only the `request_type` (1 byte) and nothing else.

```k
    syntax Int ::= #computeRequestsHash(List) [function, symbol(#computeRequestsHash)]
 // ----------------------------------------------------------------------------------
    rule #computeRequestsHash(RS) => #parseHexWord(Sha256(#computeRequestsHashIntermediate(RS)))

    syntax Bytes ::= #computeRequestsHashIntermediate(List)        [function, symbol(#computeRequestsHashIntermediate)]
                   | #computeRequestsHashIntermediate(List, Bytes) [function, symbol(#computeRequestsHashIntermediateAux)]
 // ----------------------------------------------------------------------------------------------------------------------
    rule #computeRequestsHashIntermediate(RS) => #computeRequestsHashIntermediate(RS, .Bytes)
    rule #computeRequestsHashIntermediate(.List, ACC) => ACC
    rule #computeRequestsHashIntermediate(ListItem(R) RS, ACC) => #computeRequestsHashIntermediate(RS, ACC)
      requires lengthBytes(R) <=Int 1
    rule #computeRequestsHashIntermediate(ListItem(R) RS, ACC) => #computeRequestsHashIntermediate(RS, ACC +Bytes Sha256raw(R))
      requires lengthBytes(R) >Int 1
```

Deposit Requests
----------------
The structure denoting the new deposit request consists of the following fields:

1. `pubkey: Bytes48`
2. `withdrawal_credentials: Bytes32`
3. `amount: uint64`
4. `signature: Bytes96`
5. `index: uint64`

```k
    syntax Int ::= "DEPOSIT_REQUEST_TYPE"         [macro]
                 | "DEPOSIT_EVENT_LENGTH"         [macro]
                 | "DEPOSIT_CONTRACT_ADDRESS"     [alias]
                 | "DEPOSIT_EVENT_SIGNATURE_HASH" [alias]
 // -----------------------------------------------------
    rule DEPOSIT_REQUEST_TYPE => 0
    rule DEPOSIT_CONTRACT_ADDRESS => #parseAddr("0x00000000219ab540356cbb839cbe05303d7705fa")
    rule DEPOSIT_EVENT_SIGNATURE_HASH => #parseWord("0x649bbc62d0e31342afea4e5cd82d4049e7e1ee912fc0889aa790803be39038c5")
    rule DEPOSIT_EVENT_LENGTH => 576

    syntax Int ::= "PUBKEY_OFFSET"                [macro]
                 | "WITHDRAWAL_CREDENTIALS_OFFSET"[macro]
                 | "AMOUNT_OFFSET"                [macro]
                 | "SIGNATURE_OFFSET"             [macro]
                 | "INDEX_OFFSET"                 [macro]
                 | "PUBKEY_SIZE"                  [macro]
                 | "WITHDRAWAL_CREDENTIALS_SIZE"  [macro]
                 | "AMOUNT_SIZE"                  [macro]
                 | "SIGNATURE_SIZE"               [macro]
                 | "INDEX_SIZE"                   [macro]
 // -----------------------------------------------------
    rule PUBKEY_OFFSET                 => 160
    rule WITHDRAWAL_CREDENTIALS_OFFSET => 256
    rule AMOUNT_OFFSET                 => 320
    rule SIGNATURE_OFFSET              => 384
    rule INDEX_OFFSET                  => 512
    rule PUBKEY_SIZE                   => 48
    rule WITHDRAWAL_CREDENTIALS_SIZE   => 32
    rule AMOUNT_SIZE                   => 8
    rule SIGNATURE_SIZE                => 96
    rule INDEX_SIZE                    => 8
```



```k
    syntax Bytes ::= #extractDepositData ( Bytes ) [function, symbol(#extractDepositData)]
 // --------------------------------------------------------------------------------------
    rule #extractDepositData(DATA) => substrBytes(DATA, PUBKEY_OFFSET +Int 32, PUBKEY_OFFSET +Int 32 +Int PUBKEY_SIZE)
                               +Bytes substrBytes(DATA, WITHDRAWAL_CREDENTIALS_OFFSET +Int 32, WITHDRAWAL_CREDENTIALS_OFFSET +Int 32 +Int WITHDRAWAL_CREDENTIALS_SIZE)
                               +Bytes substrBytes(DATA, AMOUNT_OFFSET +Int 32, AMOUNT_OFFSET +Int 32 +Int AMOUNT_SIZE)
                               +Bytes substrBytes(DATA, SIGNATURE_OFFSET +Int 32, SIGNATURE_OFFSET +Int 32 +Int SIGNATURE_SIZE)
                               +Bytes substrBytes(DATA, INDEX_OFFSET +Int 32, INDEX_OFFSET +Int 32 +Int INDEX_SIZE)

    syntax Bool ::= #isValidDepositEventData ( Bytes ) [function, symbol(#isValidDepositEventData), total]
 // ------------------------------------------------------------------------------------------------------
    rule #isValidDepositEventData(DATA) => true
      requires lengthBytes(DATA) ==Int DEPOSIT_EVENT_LENGTH
       andBool Bytes2Int(substrBytes(DATA, 0, 32), BE, Unsigned) ==Int PUBKEY_OFFSET
       andBool Bytes2Int(substrBytes(DATA, 32, 64), BE, Unsigned) ==Int WITHDRAWAL_CREDENTIALS_OFFSET
       andBool Bytes2Int(substrBytes(DATA, 64, 96), BE, Unsigned) ==Int AMOUNT_OFFSET
       andBool Bytes2Int(substrBytes(DATA, 96, 128), BE, Unsigned) ==Int SIGNATURE_OFFSET
       andBool Bytes2Int(substrBytes(DATA, 128, 160), BE, Unsigned) ==Int INDEX_OFFSET
       andBool Bytes2Int(substrBytes(DATA, PUBKEY_OFFSET, PUBKEY_OFFSET +Int 32), BE, Unsigned) ==Int PUBKEY_SIZE
       andBool Bytes2Int(substrBytes(DATA, WITHDRAWAL_CREDENTIALS_OFFSET, WITHDRAWAL_CREDENTIALS_OFFSET +Int 32), BE, Unsigned) ==Int WITHDRAWAL_CREDENTIALS_SIZE
       andBool Bytes2Int(substrBytes(DATA, AMOUNT_OFFSET, AMOUNT_OFFSET +Int 32), BE, Unsigned) ==Int AMOUNT_SIZE
       andBool Bytes2Int(substrBytes(DATA, SIGNATURE_OFFSET, SIGNATURE_OFFSET +Int 32), BE, Unsigned) ==Int SIGNATURE_SIZE
       andBool Bytes2Int(substrBytes(DATA, INDEX_OFFSET, INDEX_OFFSET +Int 32), BE, Unsigned) ==Int INDEX_SIZE

    rule #isValidDepositEventData(_) => false [owise]
```

```k
endmodule
```