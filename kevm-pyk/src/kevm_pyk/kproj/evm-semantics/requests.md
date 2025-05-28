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

Address constants:
- `DEPOSIT_CONTRACT_ADDRESS (0x00000000219ab540356cbb839cbe05303d7705fa)` : Predeployed contract for deposits.
- `WITHDRAWAL_REQUEST_PREDEPLOY_ADDRESS (0x00000961Ef480Eb55e80D19ad83579A64c007002)`: Predeployed contract for validator withdrawal requests (EIP-7002)
- `CONSOLIDATION_REQUEST_PREDEPLOY_ADDRESS (0x0000BBdDc7CE488642fb579f8B00f3a590007251)`: Predeployed contract for stake consolidation requests

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

    syntax Int ::= "DEPOSIT_EVENT_SIGNATURE_HASH"            [alias]
                 | "WITHDRAWAL_REQUEST_PREDEPLOY_ADDRESS"    [alias]
                 | "CONSOLIDATION_REQUEST_PREDEPLOY_ADDRESS" [alias]
 // ----------------------------------------------------------------
    rule DEPOSIT_CONTRACT_ADDRESS                => 44667813780391404145283579356374304250
    rule WITHDRAWAL_REQUEST_PREDEPLOY_ADDRESS    => 817336022611862939366240017674853872070658
    rule CONSOLIDATION_REQUEST_PREDEPLOY_ADDRESS => 16365465459783978374881923886502306505585233

    syntax Bytes ::= "DEPOSIT_REQUEST_TYPE"       [macro]
                   | "WITHDRAWAL_REQUEST_TYPE"    [macro]
                   | "CONSOLIDATION_REQUEST_TYPE" [macro]
 // -----------------------------------------------------
    rule DEPOSIT_REQUEST_TYPE => b"\x00"
    rule WITHDRAWAL_REQUEST_TYPE => b"\x01"
    rule CONSOLIDATION_REQUEST_TYPE => b"\x02"
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
    syntax Int ::= "DEPOSIT_EVENT_LENGTH"     [macro]
                 | "DEPOSIT_CONTRACT_ADDRESS" [alias]
 // -------------------------------------------------
    rule DEPOSIT_EVENT_SIGNATURE_HASH => 45506446345753628416285423056165511379837572639148407563471291220684748896453
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
       andBool #asWord(substrBytes(DATA, 0, 32)) ==Int PUBKEY_OFFSET
       andBool #asWord(substrBytes(DATA, 32, 64)) ==Int WITHDRAWAL_CREDENTIALS_OFFSET
       andBool #asWord(substrBytes(DATA, 64, 96)) ==Int AMOUNT_OFFSET
       andBool #asWord(substrBytes(DATA, 96, 128)) ==Int SIGNATURE_OFFSET
       andBool #asWord(substrBytes(DATA, 128, 160)) ==Int INDEX_OFFSET
       andBool #asWord(substrBytes(DATA, PUBKEY_OFFSET, PUBKEY_OFFSET +Int 32)) ==Int PUBKEY_SIZE
       andBool #asWord(substrBytes(DATA, WITHDRAWAL_CREDENTIALS_OFFSET, WITHDRAWAL_CREDENTIALS_OFFSET +Int 32)) ==Int WITHDRAWAL_CREDENTIALS_SIZE
       andBool #asWord(substrBytes(DATA, AMOUNT_OFFSET, AMOUNT_OFFSET +Int 32)) ==Int AMOUNT_SIZE
       andBool #asWord(substrBytes(DATA, SIGNATURE_OFFSET, SIGNATURE_OFFSET +Int 32)) ==Int SIGNATURE_SIZE
       andBool #asWord(substrBytes(DATA, INDEX_OFFSET, INDEX_OFFSET +Int 32)) ==Int INDEX_SIZE

    rule #isValidDepositEventData(_) => false [owise]
```

```k
endmodule
```