EVM-Specific ERC20 Specification
================================

We present a refinement of ERC20-K that specifies its detailed behaviors in EVM level.

In addition to the high-level ERC20 logic specified in ERC20-K, the EVM-level specification captures EVM-specific details such as gas consumption, data layout in storage, ABI encoding, byte representation of the program, and arithmetic overflows.

We present the low-level specification in a succinct form using the abstractions introduced in the module [VERIFICATION](../../verification.md).

### Call data

The ABI call abstraction allows to specify the call data in a function call notation:

```
#abiCallData("transfer", #address(TO), #uint256(VALUE))
```

instead of specifying the underlying byte array:

```
F1 : F2 : F3 : F4 : T1 : ... : T32 : V1 : ... : V32
```

where `F1 : F2 : F3 : F4` is the byte-array representation of 2835717307, the hash value of the function signature ABI encoding, `T1 : ... : T32` is the byte-array representation of `TO`, and `V1 : ... : V32` is the one of `VALUE`.

### Local memory

The memory abstraction allows to specify the local memory as a map over words instead of byte-arrays.

For example, we succinctly specify that a return value `1` is stored in a return address `RET_ADDR`:

```
.Map[ RET_ADDR := #asByteStackInWidth(1, 32) ]
```

instead of specifying the underlying byte-array:

```
.Map[ RET_ADDR      := 0  ]
    [ RET_ADDR + 1  := 0  ]
    ...
    [ RET_ADDR + 31 := 1 ]
```

### Storage

The storage accommodates permanent data such as the `balances` map.

A map is laid out in the storage where the map entries are scattered over the entire storage space for which the hash of each key is used to determine the location.

The detailed mechanism of calculating the location varies by compilers. In Viper, for example, `map[key1][key2]` is stored at the location:

```
hash(hash(pos(map)) + key1) + key2
```

where `pos(map)` is the position of `map` in the program, and `+` is the addition modulo `2^256`, while in Solidity, it is stored at:

```
hash(key2 ++ hash(key1 ++ pos(map)))
```

where `++` is the byte-array concatenation.


### Gas consumption

Regarding the gas consumption, the maximum gas amount is specified ensuring that the program does not consume more gas than the limit.

The verifier proves that the gas consumption is less than the provided limit, and also reports the exact amount of gas consumed during the execution. Indeed, it reports a set of the amounts since the gas consumption varies depending on the context (i.e., the input parameter values and the state of the storage).





totalSupply
-----------

```{.k .erc20-spec .hkg-spec}
[totalSupply]
```

`<k>` cell specifies that the execution eventually reaches RETURN instruction meaning that the program will successfully terminate. The RETURN instruction says that a 32-byte return value will be stored in the memory at the location RET_ADDR.

```{.k .erc20-spec .hkg-spec}
k: #execute => (RETURN RET_ADDR:Int 32 ~> _)

callData: #abiCallData("totalSupply", .TypedArgs)
```

`<localMem>` cell specifies that the local memory is empty in the beginning, but in the end, it will contain some contents including the return value `TOTAL`, the total supply.

The other entries are represented by the wildcard symbol `_`, meaning that they are not relevant to the correctness.

```{.k .erc20-spec .hkg-spec}
localMem:
      .Map
    =>
    (
      .Map[ RET_ADDR := #asByteStackInWidth(TOTAL, 32) ]
      _:Map
    )
```

`<gas>` cell specifies the maximum gas amount. Here we give a loose upper-bound for the demonstration purpose. In practice, one should set a reasonable amount of the gas limit to see if the program does not consume too much gas ensuring no gas leakage.

```{.k .erc20-spec .hkg-spec}
gas:
    /* G */ 100000 => _
```

`<log>` cell specifies that no log is generated during the execution.

```{.k .erc20-spec .hkg-spec}
log:
    /* _ */ .List
```

`<refund>` cell specifies that no gas is refunded. Note that it does not mean it consumes all the provided gas. The gas refund happens only for some situation, e.g., re-claiming (i.e., garbage-collecting) unused storage entries.

```{.k .erc20-spec .hkg-spec}
refund:
    /* _ */ 0
```

`<storage>` cell specifies that the value of `totaySupply` is `TOTAL` and other entries are not relevant (could be arbitrary values).

```{.k .erc20-spec .hkg-spec}
storage:
    #hashedLocation({lang}, {pos(totalsupply)}, .IntList) |-> TOTAL
    _:Map
```

The side-condition specifies both the minimum and the maximum values of the symbolic values based on their types.

```{.k .erc20-spec .hkg-spec}
requires:
    andBool 0 <=Int TOTAL     andBool TOTAL     <Int (2 ^Int 256)

epilogue:
```




balanceOf
---------

The specification of `balanceOf` is similar to that of `totalSupply`.

```{.k .erc20-spec .hkg-spec}
[balanceOf]

k: #execute => (RETURN RET_ADDR:Int 32 ~> _)

callData: #abiCallData("balanceOf", #address(OWNER))

localMem:
      .Map
    =>
    (
      .Map[ RET_ADDR := #asByteStackInWidth(BAL, 32) ]
      _:Map
    )

gas:
    /* G */ 100000 => _

log:
    /* _ */ .List

refund:
    /* _ */ 0
```

`<storage>` cell specifies that the value of `balances[OWNER]` is `BAL`, which is in our interest.

```{.k .erc20-spec .hkg-spec}
storage:
    #hashedLocation({lang}, {pos(balances)}, OWNER) |-> BAL
    _:Map

requires:
    andBool 0 <=Int OWNER     andBool OWNER     <Int (2 ^Int 160)
    andBool 0 <=Int BAL       andBool BAL       <Int (2 ^Int 256)

epilogue:
```

allowance
---------

The specification of `allowance` is similar to that of `totalSupply` as well.

```{.k .erc20-spec .hkg-spec}
[allowance]

k: #execute => (RETURN RET_ADDR:Int 32 ~> _)

callData: #abiCallData("allowance", #address(OWNER), #address(SPENDER))

localMem:
      .Map
    =>
    (
      .Map[ RET_ADDR := #asByteStackInWidth(ALLOWANCE, 32) ]
      _:Map
    )

gas:
    /* G */ 100000 => _

log:
    /* _ */ .List

refund:
    /* _ */ 0
```

`<storage>` cell specifies that the value of `allowances[OWNER][SPENDER]` is `ALLOWANCE`.

```{.k .erc20-spec .hkg-spec}
storage:
    #hashedLocation({lang}, {pos(allowances)}, OWNER SPENDER) |-> ALLOWANCE
    _:Map

requires:
    andBool 0 <=Int OWNER     andBool OWNER     <Int (2 ^Int 160)
    andBool 0 <=Int SPENDER   andBool SPENDER   <Int (2 ^Int 160)
    andBool 0 <=Int ALLOWANCE andBool ALLOWANCE <Int (2 ^Int 256)

epilogue:
```


approve
-------

```{.k .erc20-spec .hkg-spec}
[approve]

k: #execute => (RETURN RET_ADDR:Int 32 ~> _)

callData: #abiCallData("approve", #address(SPENDER), #uint256(VALUE))

localMem:
      .Map
    =>
    (
      .Map[ RET_ADDR := #asByteStackInWidth(RET_VAL, 32) ]
      _:Map
    )

gas:
    /* G */ 100000 => _
```

`<log>` cell specifies that an event log is generated during the execution.

The log message contains the account ID of the current contract, the hash of the signature of event Approval, the account ID who calls this contract, the SPENDER account ID, and the approved VALUE.

```{.k .erc20-spec .hkg-spec}
log:
      /* _ */
    (
      .List
    =>
      ListItem({ ACCT_ID
               | #parseHexWord(Keccak256(#generateSignature("Approval", #address(CALLER_ID), #address(SPENDER), #uint256(VALUE))))
               : CALLER_ID
               : SPENDER
               : .WordStack
               | #asByteStackInWidth(VALUE, 32)
               })
    )
```

`<refund>` cell specifies that a refund may be issued. This function will refund a gas if the allowance value is 0 while the previous value is greater than 0, re-claiming the corresponding entry of the storage.

Note that, however, we have not specified the refund detail since it is not essential for the functional correctness.

```{.k .erc20-spec .hkg-spec}
refund:
    /* _ */ 0 => _ /* TODO: more detail */
```

`<storage>` cell specifies that the value of `allowances[CALLER_ID][SPENDER]` will be updated to `VALUE` after the execution.

```{.k .erc20-spec .hkg-spec}
storage:
    #hashedLocation({lang}, {pos(allowances)}, CALLER_ID SPENDER) |-> (_:Int => VALUE)
    _:Map
```

Unlike the ERC20-K specification, we do not specify the case when `VALUE` is less than 0 because it is not possible --- the `VALUE` parameter is declared as the type of *unsigned* 256-bit integer.

Indeed, the ABI call mechanism will reject a call to this function if the `VALUE` is negative, which is out of the scope of the EVM-level specification.

```{.k .erc20-spec .hkg-spec}
requires:
    andBool 0 <=Int SPENDER   andBool SPENDER   <Int (2 ^Int 160)
    andBool 0 <=Int VALUE     andBool VALUE     <Int (2 ^Int 256)
    andBool RET_VAL ==Int 1

epilogue:
    // NOTE: negative VALUE is not possible since it is of `num256` type
```




transfer
--------

```{.k .erc20-spec .hkg-spec}
[transfer]

callData: #abiCallData("transfer", #address(TO_ID), #uint256(VALUE))

gas:
    /* G */ 100000 => _
```

`transfer` function admits two types of behaviors:
- succeeds in transferring the value and returns true (i.e., 1)
- fails to transfer due to the arithmetic overflow and throws an exception

We present two specifications, one for each case.

### Case of success

```{.k .erc20-spec .hkg-spec}
[transfer-success]

k: #execute => (RETURN RET_ADDR:Int 32 ~> _)

localMem:
      .Map
    =>
    (
      .Map[ RET_ADDR := #asByteStackInWidth(RET_VAL, 32) ]
      _:Map
    )

```

`<log>` cell specifies that it generates an event log of type `Transfer`.

```{.k .erc20-spec .hkg-spec}
log:
      /* _ */
    (
      .List
    =>
      ListItem({ ACCT_ID
               | #parseHexWord(Keccak256(#generateSignature("Transfer", #address(CALLER_ID), #address(TO_ID), #uint256(VALUE))))
               : CALLER_ID
               : TO_ID
               : .WordStack
               | #asByteStackInWidth(VALUE, 32)
               })
    )

refund:
    /* _ */ 0 => _ /* TODO: more detail */

requires:
    andBool 0 <=Int TO_ID     andBool TO_ID     <Int (2 ^Int 160)
    andBool 0 <=Int VALUE     andBool VALUE     <Int (2 ^Int 256)
    andBool 0 <=Int BAL_FROM  andBool BAL_FROM  <Int (2 ^Int 256)
    andBool 0 <=Int BAL_TO    andBool BAL_TO    <Int (2 ^Int 256)
    andBool RET_VAL ==Int 1

epilogue:
    // NOTE: negative VALUE is not possible since it is of `num256` type
```

There are two sub-cases depending on whether the caller is equal to the recipient. 

#### Sub-case 1: the caller `CALLER_ID` is different from the recipient `TO_ID`.

```{.k .erc20-spec .hkg-spec}
[transfer-success-1]
```

`<storage>` cell specifies that the amount of `VALUE` is transferred from `balances[CALLER_ID]` to `balances[TO_ID]`.

```{.k .erc20-spec .hkg-spec}
storage:
    #hashedLocation({lang}, {pos(balances)}, CALLER_ID) |-> (BAL_FROM => BAL_FROM -Int VALUE)
    #hashedLocation({lang}, {pos(balances)}, TO_ID)     |-> (BAL_TO   => BAL_TO   +Int VALUE)
    _:Map

+requires:
    andBool CALLER_ID =/=Int TO_ID
```

The side-condition ensures that no arithmetic overflow happens.

```{.k .erc20-spec}
    andBool VALUE <=Int BAL_FROM
    andBool BAL_TO +Int VALUE <Int (2 ^Int 256) // viper overflow check: (VALUE ==Int 0 xorBool BAL_TO +Word VALUE >Int BAL_TO)
```

TODO: HKG

```{.k .hkg-spec}
    andBool VALUE <=Int BAL_FROM
    andBool VALUE >Int 0
```

#### Sub-case 2: the caller `CALLER_ID` is equal to the recipient `TO_ID`.

```{.k .erc20-spec .hkg-spec}
[transfer-success-2]
```

`<storage>` cell specifies that `balances[CALLER_ID]` is not changed since the value is transferred to himself.

```{.k .erc20-spec .hkg-spec}
storage:
    #hashedLocation({lang}, {pos(balances)}, CALLER_ID) |-> BAL_FROM
    _:Map

+requires:
    andBool CALLER_ID ==Int TO_ID
```

The side-condition ensures that no arithmetic overflow happens.

```{.k .erc20-spec}
    andBool VALUE <=Int BAL_FROM
```

TODO: HKG

```{.k .hkg-spec}
    andBool VALUE <=Int BAL_FROM
    andBool VALUE >Int 0
```



### Case of failure

```{.k .erc20-spec .hkg-spec}
[transfer-failure]
```

`<k>` cell specifies that an exception will be thrown for the failure case.

```{.k .erc20-spec}
k: #execute => #exception
```

TODO:

```{.k .hkg-spec}
k: #execute => (RETURN RET_ADDR:Int 32 ~> _)
```

The local memory is not relevant at all in this case.

```{.k .erc20-spec}
localMem:
    .Map => _:Map
```

TODO: HKG

```{.k .hkg-spec}
localMem:
      .Map
    =>
    (
      .Map[ RET_ADDR := #asByteStackInWidth(RET_VAL, 32) ]
      _:Map
    )
```

No log will be generated.

```{.k .erc20-spec .hkg-spec}
log:
    /* _ */ .List

refund:
    /* _ */ 0 => _ /* TODO: more detail */

requires:
    andBool 0 <=Int TO_ID     andBool TO_ID     <Int (2 ^Int 160)
    andBool 0 <=Int VALUE     andBool VALUE     <Int (2 ^Int 256)
    andBool 0 <=Int BAL_FROM  andBool BAL_FROM  <Int (2 ^Int 256)
    andBool 0 <=Int BAL_TO    andBool BAL_TO    <Int (2 ^Int 256)
```

TODO: HKG:

```{.k .hkg-spec}
    andBool RET_VAL ==Int 0
```

```{.k .erc20-spec .hkg-spec}
epilogue:
    // TODO: properly consider exception preserving the input status
    //       using CALL GCAP ACCTTO VALUE ARGSTART ARGWIDTH RETSTART RETWIDTH

    // NOTE: negative VALUE is not possible since it is of `num256` type
```

There are two sub-cases as well depending on whether the caller is equal to the recipient. 

#### Sub-case 1: the caller `CALLER_ID` is different from the recipient `TO_ID`.

```{.k .erc20-spec .hkg-spec}
[transfer-failure-1]

storage:
    #hashedLocation({lang}, {pos(balances)}, CALLER_ID) |-> (BAL_FROM => _)
    #hashedLocation({lang}, {pos(balances)}, TO_ID)     |->  BAL_TO
    _:Map

+requires:
    andBool CALLER_ID =/=Int TO_ID
```

The side-condition causing the arithmetic overflows, i.e., the negation of that of the success case (sub-case 1):

```{.k .erc20-spec}
    andBool ( VALUE >Int BAL_FROM
     orBool   BAL_TO +Int VALUE >=Int (2 ^Int 256) ) // viper overflow check: ( VALUE =/=Int 0 andBool BAL_TO +Word VALUE <Int BAL_TO )
```

TODO: HKG:

```{.k .hkg-spec}
[transfer-failure-1-a]

+requires:
    andBool VALUE >Int BAL_FROM

[transfer-failure-1-b]

+requires:
    andBool VALUE <=Int 0
```




#### Sub-case 2: the caller `CALLER_ID` is equal to the recipient `TO_ID`.

```{.k .erc20-spec .hkg-spec}
[transfer-failure-2]

storage:
    #hashedLocation({lang}, {pos(balances)}, CALLER_ID) |-> BAL_FROM
    _:Map

+requires:
    andBool CALLER_ID ==Int TO_ID
```

The side-condition causing the arithmetic overflows, i.e., the negation of that of the success case (sub-case 2):

```{.k .erc20-spec}
    andBool VALUE >Int BAL_FROM
```

TODO: HKG:

```{.k .hkg-spec}
[transfer-failure-2-a]

+requires:
    andBool VALUE >Int BAL_FROM

[transfer-failure-2-b]

+requires:
    andBool VALUE <=Int 0
```




transferFrom
------------

The specification of `transferFrom` is similar to that of `transfer`.

```{.k .erc20-spec .hkg-spec}
[transferFrom]
callData: #abiCallData("transferFrom", #address(FROM_ID), #address(TO_ID), #uint256(VALUE))

gas:
    /* G */ 100000 => _
```

### Case of success

```{.k .erc20-spec .hkg-spec}
[transferFrom-success]

k: #execute => (RETURN RET_ADDR:Int 32 ~> _)

localMem:
      .Map
    =>
    (
      .Map[ RET_ADDR := #asByteStackInWidth(RET_VAL, 32) ]
      _:Map
    )

log:
      /* _ */
    (
      .List
    =>
      ListItem({ ACCT_ID
               | #parseHexWord(Keccak256(#generateSignature("Transfer", #address(FROM_ID), #address(TO_ID), #uint256(VALUE))))
               : FROM_ID
               : TO_ID
               : .WordStack
               | #asByteStackInWidth(VALUE, 32)
               })
    )

refund:
    /* _ */ 0 => _ /* TODO: more detail */

requires:
    andBool 0 <=Int FROM_ID   andBool FROM_ID   <Int (2 ^Int 160)
    andBool 0 <=Int TO_ID     andBool TO_ID     <Int (2 ^Int 160)
    andBool 0 <=Int VALUE     andBool VALUE     <Int (2 ^Int 256)
    andBool 0 <=Int BAL_FROM  andBool BAL_FROM  <Int (2 ^Int 256)
    andBool 0 <=Int BAL_TO    andBool BAL_TO    <Int (2 ^Int 256)
    andBool 0 <=Int ALLOW     andBool ALLOW     <Int (2 ^Int 256)
    andBool RET_VAL ==Int 1

epilogue:
    // NOTE: negative VALUE is not possible since it is of `num256` type
```

#### Sub-case 1: the sender `FROM_ID` is different from the recipient `TO_ID`.

```{.k .erc20-spec .hkg-spec}
[transferFrom-success-1]
```

`<storage>` cell specifies that the amount of `VALUE` will be transferred from `balances[FROM_ID]` to `balances[TO_ID]`, and the amount is deducted from `allowances[FROM_ID][CALLER_ID]` correspondingly.

```{.k .erc20-spec .hkg-spec}
storage:
    #hashedLocation({lang}, {pos(balances)},   FROM_ID)           |-> (BAL_FROM => BAL_FROM -Int VALUE)
    #hashedLocation({lang}, {pos(balances)},   TO_ID)             |-> (BAL_TO   => BAL_TO   +Int VALUE)
    #hashedLocation({lang}, {pos(allowances)}, FROM_ID CALLER_ID) |-> (ALLOW    => ALLOW    -Int VALUE)
    _:Map

+requires:
    andBool FROM_ID =/=Int TO_ID
```

TODO: ERC20

```{.k .erc20-spec}
    andBool VALUE <=Int BAL_FROM
    andBool BAL_TO +Int VALUE <Int (2 ^Int 256) // viper overflow check: (VALUE ==Int 0 xorBool BAL_TO +Word VALUE >Int BAL_TO)
    andBool VALUE <=Int ALLOW
```

TODO: HKG

```{.k .hkg-spec}
    andBool VALUE <=Int BAL_FROM
    andBool VALUE <=Int ALLOW
    andBool VALUE >Int 0
```

#### Sub-case 2: the sender `FROM_ID` is equal to the recipient `TO_ID`.

```{.k .erc20-spec .hkg-spec}
[transferFrom-success-2]

storage:
    #hashedLocation({lang}, {pos(balances)},   FROM_ID)           |-> BAL_FROM
    #hashedLocation({lang}, {pos(allowances)}, FROM_ID CALLER_ID) |-> (ALLOW => ALLOW -Int VALUE)
    _:Map

+requires:
    andBool FROM_ID ==Int TO_ID
```

TODO:

```{.k .erc20-spec}
    andBool VALUE <=Int BAL_FROM
    andBool VALUE <=Int ALLOW
```

TODO:

```{.k .hkg-spec}
    andBool VALUE <=Int BAL_FROM
    andBool VALUE <=Int ALLOW
    andBool VALUE >Int 0
```

### Case of failure

```{.k .erc20-spec .hkg-spec}
[transferFrom-failure]
```

```{.k .erc20-spec}
k: #execute => #exception
```

TODO:

```{.k .hkg-spec}
k: #execute => (RETURN RET_ADDR:Int 32 ~> _)
```

```{.k .erc20-spec}
localMem:
    .Map => _:Map
```

TODO: HKG

```{.k .hkg-spec}
localMem:
      .Map
    =>
    (
      .Map[ RET_ADDR := #asByteStackInWidth(RET_VAL, 32) ]
      _:Map
    )
```

```{.k .erc20-spec .hkg-spec}
log:
    /* _ */ .List

refund:
    /* _ */ 0 => _ /* TODO: more detail */

requires:
    andBool 0 <=Int FROM_ID   andBool FROM_ID   <Int (2 ^Int 160)
    andBool 0 <=Int TO_ID     andBool TO_ID     <Int (2 ^Int 160)
    andBool 0 <=Int VALUE     andBool VALUE     <Int (2 ^Int 256)
    andBool 0 <=Int BAL_FROM  andBool BAL_FROM  <Int (2 ^Int 256)
    andBool 0 <=Int BAL_TO    andBool BAL_TO    <Int (2 ^Int 256)
    andBool 0 <=Int ALLOW     andBool ALLOW     <Int (2 ^Int 256)
```

TODO: HKG:

```{.k .hkg-spec}
    andBool RET_VAL ==Int 0
```

```{.k .erc20-spec .hkg-spec}
epilogue:
    // TODO: properly consider exception preserving the input status
    //       using CALL GCAP ACCTTO VALUE ARGSTART ARGWIDTH RETSTART RETWIDTH

    // NOTE: negative VALUE is not possible since it is of `num256` type
```

#### Sub-case 1: the sender `FROM_ID` is different from the recipient `TO_ID`.

```{.k .erc20-spec .hkg-spec}
[transferFrom-failure-1]
storage:
    #hashedLocation({lang}, {pos(balances)},   FROM_ID)           |-> (BAL_FROM => _)  // BAL_FROM
    #hashedLocation({lang}, {pos(balances)},   TO_ID)             |-> (BAL_TO   => _)  // BAL_TO  
    #hashedLocation({lang}, {pos(allowances)}, FROM_ID CALLER_ID) |-> ALLOW
    _:Map

+requires:
    andBool FROM_ID =/=Int TO_ID
```

We split the sub-case 1 into another three sub-cases: one for each disjunct of the side-condition causing the arithmetic overflows, due to a limitation of the current K verifier that we are fixing.

Note that the sub-cases are to be disjoined (i.e, OR'ed) to represent the complete specification.

```{.k .erc20-spec}
[transferFrom-failure-1-a]
+requires:
    andBool VALUE >Int BAL_FROM

[transferFrom-failure-1-b]
+requires:
    andBool BAL_TO +Int VALUE >=Int (2 ^Int 256) // viper overflow check: ( VALUE =/=Int 0 andBool BAL_TO +Word VALUE <Int BAL_TO )

[transferFrom-failure-1-c]
+requires:
    andBool VALUE >Int ALLOW
```

TODO:

```{.k .hkg-spec}
[transferFrom-failure-1-a]
+requires:
    andBool VALUE >Int BAL_FROM

[transferFrom-failure-1-b]
+requires:
    andBool VALUE >Int ALLOW

[transferFrom-failure-1-c]
+requires:
    andBool VALUE <=Int 0
```


#### Sub-case 2: the sender `FROM_ID` is equal to the recipient `TO_ID`.

```{.k .erc20-spec .hkg-spec}
[transferFrom-failure-2]

storage:
    #hashedLocation({lang}, {pos(balances)},   FROM_ID)           |-> BAL_FROM
    #hashedLocation({lang}, {pos(allowances)}, FROM_ID CALLER_ID) |-> ALLOW
    _:Map

+requires:
    andBool FROM_ID ==Int TO_ID
```

TODO:

```{.k .erc20-spec}
    andBool ( VALUE >Int BAL_FROM
     orBool   VALUE >Int ALLOW )
```

TODO:

```{.k .hkg-spec}
[transferFrom-failure-2-a]
+requires:
    andBool VALUE >Int BAL_FROM

[transferFrom-failure-2-b]
+requires:
    andBool VALUE >Int ALLOW

[transferFrom-failure-2-c]
+requires:
    andBool VALUE <=Int 0
```





```{.k .viper-pgm}
[DEFAULT]
lang: "Viper"
pos(balances): 0
pos(allowances): 1
pos(totalsupply): 2
code: "0x600035601c52740100000000000000000000000000000000000000006020526f7fffffffffffffffffffffffffffffff6040527fffffffffffffffffffffffffffffffff8000000000000000000000000000000060605274012a05f1fffffffffffffffffffffffffdabf41c006080527ffffffffffffffffffffffffed5fa0e000000000000000000000000000000000060a05263d0e30db06000511415610168573460008112585761014052336101605261016051600060c052602060c02001546101405161016051600060c052602060c020015401116101405115176100e657600080fd5b6101405161016051600060c052602060c02001540161016051600060c052602060c020015560025461014051600254011161014051151761012657600080fd5b610140516002540160025561014051610180526101605160007fddf252ad1be2c89b69c2b068fc378daa952ba7f163c4a11628f55a4df523b3ef6020610180a3005b632e1a7d4d6000511415610260576020600461014037341561018957600080fd5b33610160526101405161016051600060c052602060c020015410156101ad57600080fd5b6101405161016051600060c052602060c02001540361016051600060c052602060c02001556101405160025410156101e457600080fd5b61014051600254036002556000600060006000600160605161014051806040519013585780919012585702610160516000f161021f57600080fd5b61014051610180526000610160517fddf252ad1be2c89b69c2b068fc378daa952ba7f163c4a11628f55a4df523b3ef6020610180a3600160005260206000f3005b6318160ddd600051141561028657341561027957600080fd5b60025460005260206000f3005b6370a0823160005114156102cd57602060046101403734156102a757600080fd5b60043560205181101558575061014051600060c052602060c020015460005260206000f3005b63a9059cbb60005114156103e057604060046101403734156102ee57600080fd5b60043560205181101558575033610180526101605161018051600060c052602060c0200154101561031e57600080fd5b6101605161018051600060c052602060c02001540361018051600060c052602060c020015561014051600060c052602060c02001546101605161014051600060c052602060c0200154011161016051151761037857600080fd5b6101605161014051600060c052602060c02001540161014051600060c052602060c0200155610160516101a05261014051610180517fddf252ad1be2c89b69c2b068fc378daa952ba7f163c4a11628f55a4df523b3ef60206101a0a3600160005260206000f3005b6323b872dd6000511415610559576060600461014037341561040157600080fd5b600435602051811015585750602435602051811015585750336101a0526101a05161014051600160c052602060c0200160c052602060c02001546101c0526101805161014051600060c052602060c0200154101561045e57600080fd5b6101805161014051600060c052602060c02001540361014051600060c052602060c020015561016051600060c052602060c02001546101805161016051600060c052602060c020015401116101805115176104b857600080fd5b6101805161016051600060c052602060c02001540161016051600060c052602060c0200155610180516101c05110156104f057600080fd5b610180516101c051036101a05161014051600160c052602060c0200160c052602060c0200155610180516101e05261016051610140517fddf252ad1be2c89b69c2b068fc378daa952ba7f163c4a11628f55a4df523b3ef60206101e0a3600160005260206000f3005b63095ea7b360005114156105ef576040600461014037341561057a57600080fd5b6004356020518110155857503361018052610160516101405161018051600160c052602060c0200160c052602060c0200155610160516101a05261014051610180517f8c5be1e5ebec7d5bd14f71427d1e84f3dd0314c0f7b2291e5b200ac8c7c3b92560206101a0a3600160005260206000f3005b63dd62ed3e600051141561064f576040600461014037341561061057600080fd5b6004356020518110155857506024356020518110155857506101605161014051600160c052602060c0200160c052602060c020015460005260206000f3005b"
```

```{.k .hkg-pgm}
[DEFAULT]
lang: "Solidity"
pos(totalsupply): 0
pos(balances): 1
pos(allowances): 2
code: "0x60606040526004361061006d576000357c0100000000000000000000000000000000000000000000000000000000900463ffffffff168063095ea7b31461007257806323b872dd146100cc57806370a0823114610145578063a9059cbb14610192578063dd62ed3e146101ec575b600080fd5b341561007d57600080fd5b6100b2600480803573ffffffffffffffffffffffffffffffffffffffff16906020019091908035906020019091905050610258565b604051808215151515815260200191505060405180910390f35b34156100d757600080fd5b61012b600480803573ffffffffffffffffffffffffffffffffffffffff1690602001909190803573ffffffffffffffffffffffffffffffffffffffff1690602001909190803590602001909190505061034a565b604051808215151515815260200191505060405180910390f35b341561015057600080fd5b61017c600480803573ffffffffffffffffffffffffffffffffffffffff169060200190919050506105c6565b6040518082815260200191505060405180910390f35b341561019d57600080fd5b6101d2600480803573ffffffffffffffffffffffffffffffffffffffff1690602001909190803590602001909190505061060f565b604051808215151515815260200191505060405180910390f35b34156101f757600080fd5b610242600480803573ffffffffffffffffffffffffffffffffffffffff1690602001909190803573ffffffffffffffffffffffffffffffffffffffff16906020019091905050610778565b6040518082815260200191505060405180910390f35b600081600260003373ffffffffffffffffffffffffffffffffffffffff1673ffffffffffffffffffffffffffffffffffffffff16815260200190815260200160002060008573ffffffffffffffffffffffffffffffffffffffff1673ffffffffffffffffffffffffffffffffffffffff168152602001908152602001600020819055508273ffffffffffffffffffffffffffffffffffffffff163373ffffffffffffffffffffffffffffffffffffffff167f8c5be1e5ebec7d5bd14f71427d1e84f3dd0314c0f7b2291e5b200ac8c7c3b925846040518082815260200191505060405180910390a36001905092915050565b600081600160008673ffffffffffffffffffffffffffffffffffffffff1673ffffffffffffffffffffffffffffffffffffffff1681526020019081526020016000205410158015610417575081600260008673ffffffffffffffffffffffffffffffffffffffff1673ffffffffffffffffffffffffffffffffffffffff16815260200190815260200160002060003373ffffffffffffffffffffffffffffffffffffffff1673ffffffffffffffffffffffffffffffffffffffff1681526020019081526020016000205410155b80156104235750600082115b156105ba5781600160008673ffffffffffffffffffffffffffffffffffffffff1673ffffffffffffffffffffffffffffffffffffffff1681526020019081526020016000206000828254039250508190555081600160008573ffffffffffffffffffffffffffffffffffffffff1673ffffffffffffffffffffffffffffffffffffffff1681526020019081526020016000206000828254019250508190555081600260008673ffffffffffffffffffffffffffffffffffffffff1673ffffffffffffffffffffffffffffffffffffffff16815260200190815260200160002060003373ffffffffffffffffffffffffffffffffffffffff1673ffffffffffffffffffffffffffffffffffffffff168152602001908152602001600020600082825403925050819055508273ffffffffffffffffffffffffffffffffffffffff168473ffffffffffffffffffffffffffffffffffffffff167fddf252ad1be2c89b69c2b068fc378daa952ba7f163c4a11628f55a4df523b3ef846040518082815260200191505060405180910390a3600190506105bf565b600090505b9392505050565b6000600160008373ffffffffffffffffffffffffffffffffffffffff1673ffffffffffffffffffffffffffffffffffffffff168152602001908152602001600020549050919050565b600081600160003373ffffffffffffffffffffffffffffffffffffffff1673ffffffffffffffffffffffffffffffffffffffff16815260200190815260200160002054101580156106605750600082115b1561076d5781600160003373ffffffffffffffffffffffffffffffffffffffff1673ffffffffffffffffffffffffffffffffffffffff1681526020019081526020016000206000828254039250508190555081600160008573ffffffffffffffffffffffffffffffffffffffff1673ffffffffffffffffffffffffffffffffffffffff168152602001908152602001600020600082825401925050819055508273ffffffffffffffffffffffffffffffffffffffff163373ffffffffffffffffffffffffffffffffffffffff167fddf252ad1be2c89b69c2b068fc378daa952ba7f163c4a11628f55a4df523b3ef846040518082815260200191505060405180910390a360019050610772565b600090505b92915050565b6000600260008473ffffffffffffffffffffffffffffffffffffffff1673ffffffffffffffffffffffffffffffffffffffff16815260200190815260200160002060008373ffffffffffffffffffffffffffffffffffffffff1673ffffffffffffffffffffffffffffffffffffffff168152602001908152602001600020549050929150505600a165627a7a723058207e0ec45a8f499af74c964dd2887d82a5b0f9522a60a1df3f107bddccf74118470029"
```

Specification Template
----------------------

```{.k .tmpl}
module {module}-SPEC
  imports ETHEREUM-SIMULATION

  rule
    <k> {k} </k>
    <exit-code> 1 </exit-code>
    <mode> NORMAL </mode>
    <schedule> DEFAULT </schedule> // TODO: pick a right one
    <analysis> /* _ */ .Map </analysis>

    <ethereum>
      <evm>
        <output> /* _ */ .WordStack </output>
        <memoryUsed> 0 => _ </memoryUsed>
        <callDepth> /* CALL_DEPTH */ 0 </callDepth> // TODO: check if <= 1024
        <callStack> /* _ */ .List => _ </callStack>
        <interimStates> /* _ */ .List </interimStates>
        <substateStack> /* _ */ .List </substateStack>
        <callLog> /* _ */ .Set </callLog>

        <txExecState>
          <program> #asMapOpCodes(#dasmOpCodes(#parseByteStack({code}), DEFAULT)) </program>
          <programBytes> #parseByteStack({code}) </programBytes>

          <id> ACCT_ID </id> // contract owner
          <caller> CALLER_ID </caller> // who called this contract; in the begining, origin

          <callData> {calldata} </callData>

          <callValue> 0 </callValue>
          <wordStack> .WordStack => _ </wordStack>
          <localMem>
            {localmem}
          </localMem>
          <pc> 0 => _ </pc>
          <gas> {gas} </gas> // NOTE: user provided
          <previousGas> _ => _ </previousGas>

          <static> false </static> // NOTE: non-static call
        </txExecState>

        <substate>
          <selfDestruct> /* _ */ .Set </selfDestruct>
          <log>
            {log}
          </log>
          <refund> {refund} </refund>
        </substate>

        <gasPrice> _ </gasPrice>
        <origin> ORIGIN_ID </origin> // who fires tx

        <previousHash> _ </previousHash>
        <ommersHash> _ </ommersHash>
        <coinbase> _ </coinbase>
        <stateRoot> _ </stateRoot>
        <transactionsRoot> _ </transactionsRoot>
        <receiptsRoot> _ </receiptsRoot>
        <logsBloom> _ </logsBloom>
        <difficulty> _ </difficulty>
        <number> _ </number>
        <gasLimit> _ </gasLimit>
        <gasUsed> _ </gasUsed>
        <timestamp> _ </timestamp>
        <extraData> _ </extraData>
        <mixHash> _ </mixHash>
        <blockNonce> _ </blockNonce>

        <ommerBlockHeaders> _ </ommerBlockHeaders>
        <blockhash> _ </blockhash>
      </evm>

      <network>
        <activeAccounts> ACCT_ID |-> false /* _ */ </activeAccounts>

        <accounts>
          <account>
            <acctID> ACCT_ID </acctID>
            <balance> _ </balance>
            <code> #parseByteStack({code}) </code>
            <storage>
              {storage}
            </storage>
            <nonce> _ </nonce>
          </account>
          /* _ */
        </accounts>

        <txOrder> _ </txOrder>
        <txPending> _ </txPending>
        <messages> /* _ */ .Bag </messages>
      </network>
    </ethereum>
    requires 0 <=Int ACCT_ID   andBool ACCT_ID   <Int (2 ^Int 160)
     andBool 0 <=Int CALLER_ID andBool CALLER_ID <Int (2 ^Int 160)
     andBool 0 <=Int ORIGIN_ID andBool ORIGIN_ID <Int (2 ^Int 160)
     {requires}

{epilogue}

  // to avoid unnecessary case split
  rule <k> LT W0 W1 => bool2int(W0  <Int W1) ~> #push ... </k> [trusted]
  rule <k> GT W0 W1 => bool2int(W0  >Int W1) ~> #push ... </k> [trusted]
  rule <k> EQ W0 W1 => bool2int(W0 ==Int W1) ~> #push ... </k> [trusted]
  rule <k> ISZERO W => bool2int(W  ==Int 0 ) ~> #push ... </k> [trusted]

endmodule
```
