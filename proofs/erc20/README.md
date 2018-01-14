EVM-Specific ERC20 Specification
================================

We present a refinement of ERC20-K that specifies all of its detailed behaviors in EVM level.

In addition to the high-level ERC20 logic specified in ERC20-K, the EVM-level specification specifies EVM-specific details such as gas consumption, data layout in local memory and storage, ABI encoding, byte representation of the program, and arithmetic overflows.

We present the low-level specification in a succinct form using the abstractions introduced in [VERIFICATION module](../../verification.md).

### Call data

The ABI call abstraction allows to specify the call data as a usual function call expression:

```
#abiCallData("balanceOf", #address(OWNER))
```

instead of specifying the actual byte array:

```
F1 : F2 : F3 : F4 : O1 : ... : O32
```

where `F1 : F2 : F3 : F4` is the byte-array representation of 1889567281, a hash value of the function signature ABI encoding, and `O1 : ... : O32` is the byte-array representation of `OWNER`, the argument.

### Local memory

The memory abstraction allows to specify the local memory as a map over words instead of byte-arrays.

For example, we specify that the return value `BAL` is stored in the return address `RET_ADDR` succinctly:

```
.Map[ RET_ADDR := #asByteStackInWidth(BAL, 32) ]
```

instead of specifying the actual byte-array:

```
.Map[ RET_ADDR      := BAL0  ]
    [ RET_ADDR + 1  := BAL1  ]
    ...
    [ RET_ADDR + 31 := BAL31 ]
```

### Storage

The storage specifies permanent data such as `totalSupply` value, `balance` map, and `allowance` map.

The map is stored in a way that the map entries are scattered over the entire storage space where the hash of each key is used to determine the location.

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

The verifier not only proves the gas limit, but also reports the exact amount of gas consumed during the execution. Indeed, it reports a set of the amounts since the gas consumption varies depending on the context (i.e., input parameters and the state of the storage).





totalSupply
-----------

```
[DEFAULT]
```

`<k>` cell specifies that the execution eventually reaches RETURN instruction meaning that the program will successfully finish the execution. The RETURN instruction says that a 32-byte return value will be stored in the memory at the location RET_ADDR.

```
k: #execute => (RETURN RET_ADDR:Int 32 ~> _)

callData: #abiCallData("totalSupply", .TypedArgs)
```

`<localMem>` cell specifies that the local memory is empty in the beginning, but in the end it will contain some contents including the return value `TOTAL`, the total supply.

The other entries are captured by the wildcard symbol `_`, meaning that they are not relevant for the functional correctness.

```
localMem:
      .Map
    =>
    (
      .Map[ RET_ADDR := #asByteStackInWidth(TOTAL, 32) ]
      _:Map
    )
```

For the demonstration purpose, we give a loose upper-bound of the maximum gas amount. In practice, one should set a reasonable amount of the gas limit to see if the program does not consume too much gas ensuring no gas leakage.

```
gas:
    /* G */ 100000 => _
```

No log is generated.

```
log:
    /* _ */ .List
```

It does not refund any gas. Note that it does not mean it consumes all the provided gas. The gas refund happens for some situation, e.g., re-claiming the unused storage entries by storing 0.

```
refund:
    /* _ */ 0
```

`<storage>` cell specifies that the value of `totaySupply` is `TOTAL` and other entries are not relevant (could be arbitrary values). Note that `pos(totalSupply)` is 2.

```
storage:
    2 |-> TOTAL
    _:Map
```

The side condition specifies both the minimum and the maximum values of the symbolic values based on their types.

```
requires:
    andBool 0 <=Int TOTAL     andBool TOTAL     <Int (2 ^Int 256)

epilogue:
```




balanceOf
---------

The specification of `balanceOf` is similar to that of `totalSupply`.

```
[DEFAULT]

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

`<storage>` cell specifies that the value of `balance[OWNER]` is `BAL` which will be returned. Note that `pos(balance)` is 0.

```
storage:
    sha3(0) +Word OWNER |-> BAL
    _:Map

requires:
    andBool 0 <=Int OWNER     andBool OWNER     <Int (2 ^Int 160)
    andBool 0 <=Int BAL       andBool BAL       <Int (2 ^Int 256)

epilogue:
```

allowance
---------

The specification of `allowance` is similar to that of `totalSupply` as well.

```
[DEFAULT]

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

`<storage>` cell specifies that the value of `allowance[OWNER][SPENDER]` is `ALLOWANCE` which will be returned. Note that `pos(allowance)` is 1.

```
storage:
    sha3(sha3(1) +Word OWNER) +Word SPENDER |-> ALLOWANCE
    _:Map

requires:
    andBool 0 <=Int OWNER     andBool OWNER     <Int (2 ^Int 160)
    andBool 0 <=Int SPENDER   andBool SPENDER   <Int (2 ^Int 160)
    andBool 0 <=Int ALLOWANCE andBool ALLOWANCE <Int (2 ^Int 256)

epilogue:
```


approve
-------

```
[DEFAULT]

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

It generates a event log when succeeds.

ERC20 declares two types of events: Approval and Transfer.

The log message contains the account ID of the current contract, the hash of the event signature, the account ID who calls this contract, the SPENDER account ID, and the approved VALUE.

```
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

This function may issue a refund. It will refund a gas if the allowance value is 0 while the previous value is greater than 0, re-claiming the corresponding entry of the storage.

Note that, however, we do not specify the refund detail simply because we do not think it is critical to verify the functional correctness of approve function.

```
refund:
    /* _ */ 0 => _ /* TODO: more detail */

storage:
    sha3(sha3(1) +Word CALLER_ID) +Word SPENDER |-> (_:Int => VALUE)
    _:Map

requires:
    andBool 0 <=Int SPENDER   andBool SPENDER   <Int (2 ^Int 160)
    andBool 0 <=Int VALUE     andBool VALUE     <Int (2 ^Int 256)
    andBool RET_VAL ==Int 1

epilogue:
    // NOTE: negative VALUE is not possible since it is of `num256` type
```




transfer
--------

`transfer` function has two types of behaviors:
- succeeds in transferring the value and returns true (i.e., 1)
- fails to transfer due to the arithmetic overflow and throws an exception

We present two specifications, one for each case.

### transfer suceess

```
[DEFAULT]

k: #execute => (RETURN RET_ADDR:Int 32 ~> _)

callData: #abiCallData("transfer", #address(TO_ID), #uint256(VALUE))

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

It generates an event log of type `Transfer`.

```
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

epilogue:
    // NOTE: negative VALUE is not possible since it is of `num256` type
```

Two sub-cases.

Case 1:

```
[1]

storage:
    sha3(0) +Word CALLER_ID |-> (BAL_FROM => BAL_FROM -Int VALUE)
    sha3(0) +Word TO_ID     |-> (BAL_TO   => BAL_TO   +Int VALUE)
    _:Map

requires:
    andBool 0 <=Int TO_ID     andBool TO_ID     <Int (2 ^Int 160)
    andBool 0 <=Int VALUE     andBool VALUE     <Int (2 ^Int 256)
    andBool 0 <=Int BAL_FROM  andBool BAL_FROM  <Int (2 ^Int 256)
    andBool 0 <=Int BAL_TO    andBool BAL_TO    <Int (2 ^Int 256)
```

When the caller account is different from the receiver account.

```
    andBool CALLER_ID =/=Int TO_ID
```

The side-condition ensuring no arithmetic overflow.

```
    andBool VALUE <=Int BAL_FROM
    andBool BAL_TO +Int VALUE <Int (2 ^Int 256) // viper overflow check: (VALUE ==Int 0 xorBool BAL_TO +Word VALUE >Int BAL_TO)
```

It returns true.

```
    andBool RET_VAL ==Int 1
```

Case 2:

```
[2]

storage:
    sha3(0) +Word CALLER_ID |-> BAL_FROM
    _:Map

requires:
    andBool 0 <=Int TO_ID     andBool TO_ID     <Int (2 ^Int 160)
    andBool 0 <=Int VALUE     andBool VALUE     <Int (2 ^Int 256)
    andBool 0 <=Int BAL_FROM  andBool BAL_FROM  <Int (2 ^Int 256)
```

When the caller account is the same with the receiver account, i.e., transferring money to himself.


```
    andBool CALLER_ID ==Int TO_ID
    andBool VALUE <=Int BAL_FROM
    andBool RET_VAL ==Int 1
```



### transfer failure

```
[DEFAULT]
```

When failed, it throws an exception.

```
k: #execute => #exception

callData: #abiCallData("transfer", #address(TO_ID), #uint256(VALUE))
```

The local memory is not relevant at all.

```
localMem:
    .Map => _:Map

gas:
    /* G */ 100000 => _
```

No log is generated when failed.

```
log:
    /* _ */ .List

refund:
    /* _ */ 0 => _ /* TODO: more detail */

epilogue:
    // TODO: properly consider exception preserving the input status
    //       using CALL GCAP ACCTTO VALUE ARGSTART ARGWIDTH RETSTART RETWIDTH

    // NOTE: negative VALUE is not possible since it is of `num256` type

[1]

storage:
    sha3(0) +Word CALLER_ID |-> (BAL_FROM => _)
    sha3(0) +Word TO_ID     |->  BAL_TO
    _:Map

requires:
    andBool 0 <=Int TO_ID     andBool TO_ID     <Int (2 ^Int 160)
    andBool 0 <=Int VALUE     andBool VALUE     <Int (2 ^Int 256)
    andBool 0 <=Int BAL_FROM  andBool BAL_FROM  <Int (2 ^Int 256)
    andBool 0 <=Int BAL_TO    andBool BAL_TO    <Int (2 ^Int 256)
    andBool CALLER_ID =/=Int TO_ID
```

Negation of the side-condition of that of the success case (sub-case 1):

```
    andBool ( VALUE >Int BAL_FROM
     orBool   BAL_TO +Int VALUE >=Int (2 ^Int 256) ) // viper overflow check: ( VALUE =/=Int 0 andBool BAL_TO +Word VALUE <Int BAL_TO )

[2]

storage:
    sha3(0) +Word CALLER_ID |-> BAL_FROM
    _:Map

requires:
    andBool 0 <=Int TO_ID     andBool TO_ID     <Int (2 ^Int 160)
    andBool 0 <=Int VALUE     andBool VALUE     <Int (2 ^Int 256)
    andBool 0 <=Int BAL_FROM  andBool BAL_FROM  <Int (2 ^Int 256)
    andBool 0 <=Int BAL_TO    andBool BAL_TO    <Int (2 ^Int 256)
    andBool CALLER_ID ==Int TO_ID
```

Negation of the side-condition of that of the success case (sub-case 2):

```
    andBool VALUE >Int BAL_FROM
```


transferFrom
------------

transferFrom specification is similar to that of transfer.

### transferFrom success

```
[DEFAULT]

k: #execute => (RETURN RET_ADDR:Int 32 ~> _)

callData: #abiCallData("transferFrom", #address(FROM_ID), #address(TO_ID), #uint256(VALUE))

localMem:
      .Map
    =>
    (
      .Map[ RET_ADDR := #asByteStackInWidth(RET_VAL, 32) ]
      _:Map
    )

gas:
    /* G */ 100000 => _

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

epilogue:
    // NOTE: negative VALUE is not possible since it is of `num256` type

[1]
```

Three entries are updated: `balance[FROM_ID], balance[TO_ID], allowance[FROM_ID][CALLER_ID]`

```
storage:
    sha3(0) +Word FROM_ID |-> (BAL_FROM => BAL_FROM -Int VALUE)
    sha3(0) +Word TO_ID   |-> (BAL_TO   => BAL_TO   +Int VALUE)
    sha3(sha3(1) +Word FROM_ID) +Word CALLER_ID |-> (ALLOW => ALLOW -Int VALUE)
    _:Map

requires:
    andBool 0 <=Int FROM_ID   andBool FROM_ID   <Int (2 ^Int 160)
    andBool 0 <=Int TO_ID     andBool TO_ID     <Int (2 ^Int 160)
    andBool 0 <=Int VALUE     andBool VALUE     <Int (2 ^Int 256)
    andBool 0 <=Int BAL_FROM  andBool BAL_FROM  <Int (2 ^Int 256)
    andBool 0 <=Int BAL_TO    andBool BAL_TO    <Int (2 ^Int 256)
    andBool 0 <=Int ALLOW     andBool ALLOW     <Int (2 ^Int 256)
    andBool FROM_ID =/=Int TO_ID
    andBool VALUE <=Int BAL_FROM
    andBool BAL_TO +Int VALUE <Int (2 ^Int 256) // viper overflow check: (VALUE ==Int 0 xorBool BAL_TO +Word VALUE >Int BAL_TO)
    andBool VALUE <=Int ALLOW
    andBool RET_VAL ==Int 1

[2]

storage:
    sha3(0) +Word FROM_ID |-> BAL_FROM
    sha3(sha3(1) +Word FROM_ID) +Word CALLER_ID |-> (ALLOW => ALLOW -Int VALUE)
    _:Map

requires:
    andBool 0 <=Int FROM_ID   andBool FROM_ID   <Int (2 ^Int 160)
    andBool 0 <=Int TO_ID     andBool TO_ID     <Int (2 ^Int 160)
    andBool 0 <=Int VALUE     andBool VALUE     <Int (2 ^Int 256)
    andBool 0 <=Int BAL_FROM  andBool BAL_FROM  <Int (2 ^Int 256)
    andBool 0 <=Int ALLOW     andBool ALLOW     <Int (2 ^Int 256)
    andBool FROM_ID ==Int TO_ID
    andBool VALUE <=Int BAL_FROM
    andBool VALUE <=Int ALLOW
    andBool RET_VAL ==Int 1
```

### transferFrom failure

```
[DEFAULT]

k: #execute => #exception

callData: #abiCallData("transferFrom", #address(FROM_ID), #address(TO_ID), #uint256(VALUE))

localMem:
    .Map => _:Map

gas:
    /* G */ 100000 => _

log:
    /* _ */ .List

refund:
    /* _ */ 0 => _ /* TODO: more detail */

epilogue:
    // TODO: properly consider exception preserving the input status
    //       using CALL GCAP ACCTTO VALUE ARGSTART ARGWIDTH RETSTART RETWIDTH

    // NOTE: negative VALUE is not possible since it is of `num256` type
```


We split the sub-case 1 into three cases: one for each disjunct of the arithmetic overflow condition, due to a limitation of the current k prover that we are working on fixing.

In terms of the faithfulness of the specification, it is identical to the unsplitted version, but it takes more time to verify.

Note that the sub-cases are supposed to be OR'ed to present the overall specification.

```
[1a]

storage:
    sha3(0) +Word FROM_ID |-> (BAL_FROM => _)  // BAL_FROM
    sha3(0) +Word TO_ID   |-> (BAL_TO   => _)  // BAL_TO  
    sha3(sha3(1) +Word FROM_ID) +Word CALLER_ID |-> ALLOW
    _:Map

requires:
    andBool 0 <=Int FROM_ID   andBool FROM_ID   <Int (2 ^Int 160)
    andBool 0 <=Int TO_ID     andBool TO_ID     <Int (2 ^Int 160)
    andBool 0 <=Int VALUE     andBool VALUE     <Int (2 ^Int 256)
    andBool 0 <=Int BAL_FROM  andBool BAL_FROM  <Int (2 ^Int 256)
    andBool 0 <=Int BAL_TO    andBool BAL_TO    <Int (2 ^Int 256)
    andBool 0 <=Int ALLOW     andBool ALLOW     <Int (2 ^Int 256)
    andBool FROM_ID =/=Int TO_ID
    andBool VALUE >Int BAL_FROM
  //andBool BAL_TO +Int VALUE >=Int (2 ^Int 256) // viper overflow check: ( VALUE =/=Int 0 andBool BAL_TO +Word VALUE <Int BAL_TO )
  //andBool VALUE >Int ALLOW

[1b]

storage:
    sha3(0) +Word FROM_ID |-> (BAL_FROM => _)  // BAL_FROM  or  BAL_FROM -Int VALUE
    sha3(0) +Word TO_ID   |-> (BAL_TO   => _)  // BAL_TO
    sha3(sha3(1) +Word FROM_ID) +Word CALLER_ID |-> ALLOW
    _:Map

requires:
    andBool 0 <=Int FROM_ID   andBool FROM_ID   <Int (2 ^Int 160)
    andBool 0 <=Int TO_ID     andBool TO_ID     <Int (2 ^Int 160)
    andBool 0 <=Int VALUE     andBool VALUE     <Int (2 ^Int 256)
    andBool 0 <=Int BAL_FROM  andBool BAL_FROM  <Int (2 ^Int 256)
    andBool 0 <=Int BAL_TO    andBool BAL_TO    <Int (2 ^Int 256)
    andBool 0 <=Int ALLOW     andBool ALLOW     <Int (2 ^Int 256)
    andBool FROM_ID =/=Int TO_ID
  //andBool VALUE >Int BAL_FROM
    andBool BAL_TO +Int VALUE >=Int (2 ^Int 256) // viper overflow check: ( VALUE =/=Int 0 andBool BAL_TO +Word VALUE <Int BAL_TO )
  //andBool VALUE >Int ALLOW

[1c]

storage:
    sha3(0) +Word FROM_ID |-> (BAL_FROM => _)  // BAL_FROM  or  BAL_FROM -Int VALUE
    sha3(0) +Word TO_ID   |-> (BAL_TO   => _)  // BAL_TO    or  BAL_TO   +Int VALUE
    sha3(sha3(1) +Word FROM_ID) +Word CALLER_ID |-> ALLOW
    _:Map

requires:
    andBool 0 <=Int FROM_ID   andBool FROM_ID   <Int (2 ^Int 160)
    andBool 0 <=Int TO_ID     andBool TO_ID     <Int (2 ^Int 160)
    andBool 0 <=Int VALUE     andBool VALUE     <Int (2 ^Int 256)
    andBool 0 <=Int BAL_FROM  andBool BAL_FROM  <Int (2 ^Int 256)
    andBool 0 <=Int BAL_TO    andBool BAL_TO    <Int (2 ^Int 256)
    andBool 0 <=Int ALLOW     andBool ALLOW     <Int (2 ^Int 256)
    andBool FROM_ID =/=Int TO_ID
  //andBool VALUE >Int BAL_FROM
  //andBool BAL_TO +Int VALUE >=Int (2 ^Int 256) // viper overflow check: ( VALUE =/=Int 0 andBool BAL_TO +Word VALUE <Int BAL_TO )
    andBool VALUE >Int ALLOW

[2]

storage:
    sha3(0) +Word FROM_ID |-> BAL_FROM
    sha3(sha3(1) +Word FROM_ID) +Word CALLER_ID |-> ALLOW
    _:Map

requires:
    andBool 0 <=Int FROM_ID   andBool FROM_ID   <Int (2 ^Int 160)
    andBool 0 <=Int TO_ID     andBool TO_ID     <Int (2 ^Int 160)
    andBool 0 <=Int VALUE     andBool VALUE     <Int (2 ^Int 256)
    andBool 0 <=Int BAL_FROM  andBool BAL_FROM  <Int (2 ^Int 256)
    andBool 0 <=Int ALLOW     andBool ALLOW     <Int (2 ^Int 256)
    andBool FROM_ID ==Int TO_ID
    andBool ( VALUE >Int BAL_FROM
     orBool   VALUE >Int ALLOW )
```













