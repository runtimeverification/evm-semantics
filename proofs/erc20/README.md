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

```
[DEFAULT]
```

`<k>` cell specifies that the execution eventually reaches RETURN instruction meaning that the program will successfully terminate. The RETURN instruction says that a 32-byte return value will be stored in the memory at the location RET_ADDR.

```
k: #execute => (RETURN RET_ADDR:Int 32 ~> _)

callData: #abiCallData("totalSupply", .TypedArgs)
```

`<localMem>` cell specifies that the local memory is empty in the beginning, but in the end, it will contain some contents including the return value `TOTAL`, the total supply.

The other entries are represented by the wildcard symbol `_`, meaning that they are not relevant to the correctness.

```
localMem:
      .Map
    =>
    (
      .Map[ RET_ADDR := #asByteStackInWidth(TOTAL, 32) ]
      _:Map
    )
```

`<gas>` cell specifies the maximum gas amount. Here we give a loose upper-bound for the demonstration purpose. In practice, one should set a reasonable amount of the gas limit to see if the program does not consume too much gas ensuring no gas leakage.

```
gas:
    /* G */ 100000 => _
```

`<log>` cell specifies that no log is generated during the execution.

```
log:
    /* _ */ .List
```

`<refund>` cell specifies that no gas is refunded. Note that it does not mean it consumes all the provided gas. The gas refund happens only for some situation, e.g., re-claiming (i.e., garbage-collecting) unused storage entries.

```
refund:
    /* _ */ 0
```

`<storage>` cell specifies that the value of `totaySupply` is `TOTAL` and other entries are not relevant (could be arbitrary values). Note that `pos(totalSupply) = 2`.

```
storage:
    2 |-> TOTAL
    _:Map
```

The side-condition specifies both the minimum and the maximum values of the symbolic values based on their types.

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

`<storage>` cell specifies that the value of `balances[OWNER]` is `BAL`, which is in our interest. Note that `pos(balances) = 0`.

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

`<storage>` cell specifies that the value of `allowances[OWNER][SPENDER]` is `ALLOWANCE`, where `pos(allowances) = 1`.

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

`<log>` cell specifies that an event log is generated during the execution.

The log message contains the account ID of the current contract, the hash of the signature of event Approval, the account ID who calls this contract, the SPENDER account ID, and the approved VALUE.

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

`<refund>` cell specifies that a refund may be issued. This function will refund a gas if the allowance value is 0 while the previous value is greater than 0, re-claiming the corresponding entry of the storage.

Note that, however, we have not specified the refund detail since it is not essential for the functional correctness.

```
refund:
    /* _ */ 0 => _ /* TODO: more detail */
```

`<storage>` cell specifies that the value of `allowances[CALLER_ID][SPENDER]` will be updated to `VALUE` after the execution.

```
storage:
    sha3(sha3(1) +Word CALLER_ID) +Word SPENDER |-> (_:Int => VALUE)
    _:Map
```

Unlike the ERC20-K specification, we do not specify the case when `VALUE` is less than 0 because it is not possible --- the `VALUE` parameter is declared as the type of *unsigned* 256-bit integer.

Indeed, the ABI call mechanism will reject a call to this function if the `VALUE` is negative, which is out of the scope of the EVM-level specification.

```
requires:
    andBool 0 <=Int SPENDER   andBool SPENDER   <Int (2 ^Int 160)
    andBool 0 <=Int VALUE     andBool VALUE     <Int (2 ^Int 256)
    andBool RET_VAL ==Int 1

epilogue:
    // NOTE: negative VALUE is not possible since it is of `num256` type
```




transfer
--------

`transfer` function admits two types of behaviors:
- succeeds in transferring the value and returns true (i.e., 1)
- fails to transfer due to the arithmetic overflow and throws an exception

We present two specifications, one for each case.

### Case of success

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

`<log>` cell specifies that it generates an event log of type `Transfer`.

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

There are two sub-cases depending on whether the caller is equal to the recipient. 

#### Sub-case 1: the caller `CALLER_ID` is different from the recipient `TO_ID`.

```
[1]
```

`<storage>` cell specifies that the amount of `VALUE` is transferred from `balances[CALLER_ID]` to `balances[TO_ID]`.

```
storage:
    sha3(0) +Word CALLER_ID |-> (BAL_FROM => BAL_FROM -Int VALUE)
    sha3(0) +Word TO_ID     |-> (BAL_TO   => BAL_TO   +Int VALUE)
    _:Map

requires:
    andBool 0 <=Int TO_ID     andBool TO_ID     <Int (2 ^Int 160)
    andBool 0 <=Int VALUE     andBool VALUE     <Int (2 ^Int 256)
    andBool 0 <=Int BAL_FROM  andBool BAL_FROM  <Int (2 ^Int 256)
    andBool 0 <=Int BAL_TO    andBool BAL_TO    <Int (2 ^Int 256)
    andBool CALLER_ID =/=Int TO_ID
```

The side-condition ensures that no arithmetic overflow happens.

```
    andBool VALUE <=Int BAL_FROM
    andBool BAL_TO +Int VALUE <Int (2 ^Int 256) // viper overflow check: (VALUE ==Int 0 xorBool BAL_TO +Word VALUE >Int BAL_TO)
    andBool RET_VAL ==Int 1
```

#### Sub-case 2: the caller `CALLER_ID` is equal to the recipient `TO_ID`.

```
[2]
```

`<storage>` cell specifies that `balances[CALLER_ID]` is not changed since the value is transferred to himself.

```
storage:
    sha3(0) +Word CALLER_ID |-> BAL_FROM
    _:Map

requires:
    andBool 0 <=Int TO_ID     andBool TO_ID     <Int (2 ^Int 160)
    andBool 0 <=Int VALUE     andBool VALUE     <Int (2 ^Int 256)
    andBool 0 <=Int BAL_FROM  andBool BAL_FROM  <Int (2 ^Int 256)
    andBool CALLER_ID ==Int TO_ID
```

The side-condition ensures that no arithmetic overflow happens.

```
    andBool VALUE <=Int BAL_FROM
    andBool RET_VAL ==Int 1
```



### Case of failure

```
[DEFAULT]
```

`<k>` cell specifies that an exception will be thrown for the failure case.

```
k: #execute => #exception

callData: #abiCallData("transfer", #address(TO_ID), #uint256(VALUE))
```

The local memory is not relevant at all in this case.

```
localMem:
    .Map => _:Map

gas:
    /* G */ 100000 => _
```

No log will be generated.

```
log:
    /* _ */ .List

refund:
    /* _ */ 0 => _ /* TODO: more detail */

epilogue:
    // TODO: properly consider exception preserving the input status
    //       using CALL GCAP ACCTTO VALUE ARGSTART ARGWIDTH RETSTART RETWIDTH

    // NOTE: negative VALUE is not possible since it is of `num256` type
```

There are two sub-cases as well depending on whether the caller is equal to the recipient. 

#### Sub-case 1: the caller `CALLER_ID` is different from the recipient `TO_ID`.

```
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

The side-condition causing the arithmetic overflows, i.e., the negation of that of the success case (sub-case 1):

```
    andBool ( VALUE >Int BAL_FROM
     orBool   BAL_TO +Int VALUE >=Int (2 ^Int 256) ) // viper overflow check: ( VALUE =/=Int 0 andBool BAL_TO +Word VALUE <Int BAL_TO )
```

#### Sub-case 2: the caller `CALLER_ID` is equal to the recipient `TO_ID`.

```
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

The side-condition causing the arithmetic overflows, i.e., the negation of that of the success case (sub-case 2):

```
    andBool VALUE >Int BAL_FROM
```


transferFrom
------------

The specification of `transferFrom` is similar to that of `transfer`.

### Case of success

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
```

#### Sub-case 1: the sender `FROM_ID` is different from the recipient `TO_ID`.

```
[1]
```

`<storage>` cell specifies that the amount of `VALUE` will be transferred from `balances[FROM_ID]` to `balances[TO_ID]`, and the amount is deducted from `allowances[FROM_ID][CALLER_ID]` correspondingly.

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
```

#### Sub-case 2: the sender `FROM_ID` is equal to the recipient `TO_ID`.

```
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

### Case of failure

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

#### Sub-case 1: the sender `FROM_ID` is different from the recipient `TO_ID`.

We split the sub-case 1 into another three sub-cases: one for each disjunct of the side-condition causing the arithmetic overflows, due to a limitation of the current K verifier that we are fixing.

Note that the sub-cases are to be disjoined (i.e, OR'ed) to represent the complete specification.

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
```

#### Sub-case 2: the sender `FROM_ID` is equal to the recipient `TO_ID`.

```
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
