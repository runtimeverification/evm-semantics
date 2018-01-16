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

```{.k .totalSupply}
[DEFAULT]
```

`<k>` cell specifies that the execution eventually reaches RETURN instruction meaning that the program will successfully terminate. The RETURN instruction says that a 32-byte return value will be stored in the memory at the location RET_ADDR.


balanceOf
---------

The specification of `balanceOf` is similar to that of `totalSupply`.

```{.k .balanceOf}
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

`<storage>` cell specifies that the value of `balances[OWNER]` is `BAL`, which is in our interest. Note that `pos(balances) = 1`.

```{.k .balanceOf}
storage:
	keccak(#asByteStackInWidth(OWNER, 32) ++ #asByteStackInWidth(1, 32)) |-> BAL:Int
    _:Map

requires:
     andBool 0 <=Int OWNER     andBool OWNER     <Int (2 ^Int 160)
     andBool 0 <=Int BAL       andBool BAL       <Int (2 ^Int 256)

epilogue:
```

allowance
---------

The specification of `allowance` is similar to that of `totalSupply` as well.

```{.k .allowance}
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

`<storage>` cell specifies that the value of `allowances[OWNER][SPENDER]` is `ALLOWANCE`, where `pos(allowances) = 2`.

```{.k .allowance}
storage:
    keccak(#asByteStackInWidth(SPENDER, 32) ++ #asByteStackInWidth(keccak(#asByteStackInWidth(OWNER, 32) ++ #asByteStackInWidth(2, 32)), 32)) |-> ALLOWANCE
    _:Map

requires:
    andBool 0 <=Int OWNER     andBool OWNER     <Int (2 ^Int 160)
    andBool 0 <=Int SPENDER   andBool SPENDER   <Int (2 ^Int 160)
    andBool 0 <=Int ALLOWANCE andBool ALLOWANCE <Int (2 ^Int 256)

epilogue:
```


approve
-------

```{.k .approve}
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

```{.k .approve}
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

```{.k .approve}
refund:
    /* _ */ 0 => _ /* TODO: more detail */
```

`<storage>` cell specifies that the value of `allowances[CALLER_ID][SPENDER]` will be updated to `VALUE` after the execution.

```{.k .approve}
storage:
      keccak(#asByteStackInWidth(SPENDER, 32) ++ #asByteStackInWidth(keccak(#asByteStackInWidth(CALLER_ID, 32) ++ #asByteStackInWidth(2, 32)), 32)) |-> (_:Int => VALUE)
      _:Map
```

Unlike the ERC20-K specification, we do not specify the case when `VALUE` is less than 0 because it is not possible --- the `VALUE` parameter is declared as the type of *unsigned* 256-bit integer.

Indeed, the ABI call mechanism will reject a call to this function if the `VALUE` is negative, which is out of the scope of the EVM-level specification.

```{.k .approve}
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

```{.k .transfer-success}
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

```{.k .transfer-success}
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
    // NOTE: unlike the vyper erc20, overflow isn't treated as an exception in HKG.
```

There are two sub-cases depending on whether the caller is equal to the recipient.
#### Sub-case 1: the caller `CALLER_ID` is different from the recipient `TO_ID`.

```{.k .transfer-success}
[1]
```

`<storage>` cell specifies that the amount of `VALUE` is transferred from `balances[CALLER_ID]` to `balances[TO_ID]`.

```{.k .transfer-success}
storage:
      keccak(#asByteStackInWidth(CALLER_ID, 32) ++ #padToWidth(32, #asByteStackInWidth(1, 32))) |-> (BAL_FROM => BAL_FROM -Word VALUE)
      keccak(#asByteStackInWidth(TO_ID, 32)     ++ #padToWidth(32, #asByteStackInWidth(1, 32))) |-> (BAL_TO   => BAL_TO +Word VALUE)
      _:Map

requires:
    andBool 0 <=Int TO_ID     andBool TO_ID     <Int (2 ^Int 160)
    andBool 0 <Int VALUE      andBool VALUE     <Int (2 ^Int 256)
    andBool 0 <=Int BAL_FROM  andBool BAL_FROM  <Int (2 ^Int 256)
    andBool 0 <=Int BAL_TO    andBool BAL_TO    <Int (2 ^Int 256)
    andBool CALLER_ID =/=Int TO_ID
    andBool VALUE <=Int BAL_FROM
    andBool RET_VAL ==Int 1
```

#### Sub-case 2: the caller `CALLER_ID` is equal to the recipient `TO_ID`.

```{.k .transfer-success}
[2]
```

`<storage>` cell specifies that `balances[CALLER_ID]` is not changed since the value is transferred to himself.

```{.k .transfer-success}
storage:
      keccak(#asByteStackInWidth(CALLER_ID, 32) ++ #padToWidth(32, #asByteStackInWidth(1, 32))) |-> BAL_FROM
      _:Map

requires:
    andBool 0 <=Int TO_ID     andBool TO_ID     <Int (2 ^Int 160)
    andBool 0 <Int VALUE      andBool VALUE     <Int (2 ^Int 256)
    andBool 0 <=Int BAL_FROM  andBool BAL_FROM  <Int (2 ^Int 256)
    andBool CALLER_ID ==Int TO_ID
    andBool VALUE <=Int BAL_FROM
    andBool RET_VAL ==Int 1
```

### Case of failure

```{.k .transfer-failure}
[DEFAULT]

k: #execute => (RETURN RET_ADDR:Int 32 ~> _)

callData: #abiCallData("transfer", #address(TO_ID), #uint256(VALUE))
```

The local memory is not relevant at all in this case.

```{.k .transfer-failure}
localMem:
    .Map
        =>
    .Map[ RET_ADDR := #asByteStackInWidth(RET_VAL, 32) ]
    _:Map

gas:
    /* G */ 100000 => _
```

No log will be generated.

```{.k .transfer-failure}
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
Furthermore, the hkg implementation in solidity doesn't alllow 0 value transfers, which we consider separately for each of the subcases.

#### Sub-case 1a: the caller `CALLER_ID` is different from the recipient `TO_ID` and `VALUE` > 0.

```{.k .transfer-failure}
[1a]

storage:
    keccak(#asByteStackInWidth(CALLER_ID, 32) ++ #padToWidth(32, #asByteStackInWidth(1, 32))) |-> BAL_FROM
    keccak(#asByteStackInWidth(TO_ID, 32) ++ #padToWidth(32, #asByteStackInWidth(1, 32))) |-> BAL_TO
    _:Map

requires:
    andBool 0 <=Int TO_ID     andBool TO_ID     <Int (2 ^Int 160)
    andBool 0 <Int VALUE      andBool VALUE     <Int (2 ^Int 256)
    andBool 0 <=Int BAL_FROM  andBool BAL_FROM  <Int (2 ^Int 256)
    andBool 0 <=Int BAL_TO    andBool BAL_TO    <Int (2 ^Int 256)
    andBool CALLER_ID =/=Int TO_ID
    andBool VALUE >Int BAL_FROM
    andBool RET_VAL ==Int 0
```

#### Sub-case 1b: the caller `CALLER_ID` is different from the recipient `TO_ID` and `VALUE` == 0.

```{.k .transfer-failure}
[1b]

storage:
    keccak(#asByteStackInWidth(CALLER_ID, 32) ++ #padToWidth(32, #asByteStackInWidth(1, 32))) |-> BAL_FROM
    keccak(#asByteStackInWidth(TO_ID, 32) ++ #padToWidth(32, #asByteStackInWidth(1, 32))) |-> BAL_TO
    _:Map

requires:
    andBool 0 <=Int TO_ID     andBool TO_ID     <Int (2 ^Int 160)
    andBool 0 <=Int BAL_FROM  andBool BAL_FROM  <Int (2 ^Int 256)
    andBool 0 <=Int BAL_TO    andBool BAL_TO    <Int (2 ^Int 256)
    andBool CALLER_ID =/=Int TO_ID
    andBool 0 ==Int VALUE
    andBool RET_VAL ==Int 0
```


#### Sub-case 2a: the caller `CALLER_ID` is equal to the recipient `TO_ID` and `VALUE` > 0.

```{.k .transfer-failure}
[2a]

storage:
    keccak(#asByteStackInWidth(CALLER_ID, 32) ++ #padToWidth(32, #asByteStackInWidth(1, 32))) |-> BAL_FROM
    _:Map

requires:
    andBool 0 <=Int TO_ID     andBool TO_ID     <Int (2 ^Int 160)
    andBool 0 <Int VALUE      andBool VALUE     <Int (2 ^Int 256)
    andBool 0 <=Int BAL_FROM  andBool BAL_FROM  <Int (2 ^Int 256)
    andBool 0 <=Int BAL_TO    andBool BAL_TO    <Int (2 ^Int 256)
    andBool CALLER_ID ==Int TO_ID
    andBool VALUE >Int BAL_FROM
    andBool RET_VAL ==Int 0
```
#### Sub-case 2b: the caller `CALLER_ID` is equal to the recipient `TO_ID` and `VALUE` == 0.

```{.k .transfer-failure}
[2b]

storage:
    keccak(#asByteStackInWidth(CALLER_ID, 32) ++ #padToWidth(32, #asByteStackInWidth(1, 32))) |-> BAL_FROM
    _:Map

requires:
    andBool 0 <=Int TO_ID     andBool TO_ID     <Int (2 ^Int 160)
    andBool 0 <=Int BAL_FROM  andBool BAL_FROM  <Int (2 ^Int 256)
    andBool 0 <=Int BAL_TO    andBool BAL_TO    <Int (2 ^Int 256)
    andBool CALLER_ID ==Int TO_ID
    andBool VALUE >Int BAL_FROM
    andBool 0 ==Int VALUE
    andBool RET_VAL ==Int 0
```



transferFrom
------------

The specification of `transferFrom` is similar to that of `transfer`.

### Case of success

```{.k .transferFrom-success}
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
    // NOTE: Unlike vyper ERC 20, HKG doesn't treat overflow as an exception

```

#### Sub-case 1: the sender `FROM_ID` is different from the recipient `TO_ID`.

```{.k .transferFrom-success}
[1]
```

`<storage>` cell specifies that the amount of `VALUE` will be transferred from `balances[FROM_ID]` to `balances[TO_ID]`, and the amount is deducted from `allowances[FROM_ID][CALLER_ID]` correspondingly.

```{.k .transferFrom-success}
storage:
    keccak(#asByteStackInWidth(FROM_ID, 32)   ++ #asByteStackInWidth(1, 32)) |-> (BAL_FROM => BAL_FROM -Word VALUE)
    keccak(#asByteStackInWidth(TO_ID, 32)     ++ #asByteStackInWidth(1, 32)) |-> (BAL_TO   => BAL_TO   +Word VALUE)
    keccak(#asByteStackInWidth(CALLER_ID, 32) ++ #asByteStackInWidth(keccak(#asByteStackInWidth(FROM_ID, 32) ++ #asByteStackInWidth(2, 32)), 32)) |-> (ALLOW => ALLOW -Word VALUE)
    _:Map

requires:
    andBool 0 <=Int FROM_ID   andBool FROM_ID   <Int (2 ^Int 160)
    andBool 0 <=Int TO_ID     andBool TO_ID     <Int (2 ^Int 160)
    andBool 0 <Int VALUE      andBool VALUE     <Int (2 ^Int 256)
    andBool 0 <=Int BAL_FROM  andBool BAL_FROM  <Int (2 ^Int 256)
    andBool 0 <=Int BAL_TO    andBool BAL_TO    <Int (2 ^Int 256)
    andBool 0 <=Int ALLOW     andBool ALLOW     <Int (2 ^Int 256)
    andBool FROM_ID =/=Int TO_ID
    andBool VALUE <=Int BAL_FROM
    andBool VALUE <=Int ALLOW
    andBool RET_VAL ==Int 1
```

#### Sub-case 2: the sender `FROM_ID` is equal to the recipient `TO_ID`.

```{.k .transferFrom-success}
[2]

storage:
  keccak(#asByteStackInWidth(FROM_ID, 32)   ++ #asByteStackInWidth(1, 32)) |-> BAL_FROM
  keccak(#asByteStackInWidth(CALLER_ID, 32) ++ #asByteStackInWidth(keccak(#asByteStackInWidth(FROM_ID, 32) ++ #asByteStackInWidth(2, 32)), 32)) |-> (ALLOW => ALLOW -Word VALUE)
  _:Map

requires:
     andBool 0 <=Int FROM_ID   andBool FROM_ID   <Int (2 ^Int 160)
     andBool 0 <=Int TO_ID     andBool TO_ID     <Int (2 ^Int 160)
     andBool 0 <Int VALUE      andBool  VALUE    <Int (2 ^Int 256)
     andBool 0 <=Int BAL_FROM  andBool BAL_FROM  <Int (2 ^Int 256)
     andBool 0 <=Int BAL_TO    andBool BAL_TO    <Int (2 ^Int 256)
     andBool 0 <=Int ALLOW     andBool ALLOW     <Int (2 ^Int 256)
     andBool FROM_ID ==Int TO_ID
     andBool VALUE <=Int BAL_FROM
     andBool VALUE <=Int ALLOW
     andBool RET_VAL ==Int 1
```

### Case of failure

```{.k .transferFrom-failure}
[DEFAULT]

k: #execute => (RETURN RET_ADDR:Int 32 ~> _)

callData: #abiCallData("transferFrom", #address(FROM_ID), #address(TO_ID), #uint256(VALUE))

localMem:
    .Map => .Map[ RET_ADDR := #asByteStackInWidth(RET_VAL, 32) ] _:Map

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

We split the sub-case 1 into another three sub-cases:
    1) `VAL` > `BAL_FROM`
    2) `VAL` > `ALLOWANCE`
    3) `VAL` == 0  (Specific Solidity ERC 20)

Note that the sub-cases are to be disjoined (i.e, OR'ed) to represent the complete specification.

```{.k .transferFrom-failure}
[1a]

storage:
    keccak(#asByteStackInWidth(FROM_ID, 32)   ++ #asByteStackInWidth(1, 32)) |-> BAL_FROM
    keccak(#asByteStackInWidth(TO_ID, 32)     ++ #asByteStackInWidth(1, 32)) |-> BAL_TO
    keccak(#asByteStackInWidth(CALLER_ID, 32) ++ #asByteStackInWidth(keccak(#asByteStackInWidth(FROM_ID, 32) ++ #asByteStackInWidth(2, 32)), 32)) |-> ALLOW
    _:Map

requires:
    andBool 0 <=Int FROM_ID   andBool FROM_ID   <Int (2 ^Int 160)
    andBool 0 <=Int TO_ID     andBool TO_ID     <Int (2 ^Int 160)
    andBool 0 <Int VALUE     andBool  VALUE     <Int (2 ^Int 256)
    andBool 0 <=Int BAL_FROM  andBool BAL_FROM  <Int (2 ^Int 256)
    andBool 0 <=Int BAL_TO    andBool BAL_TO    <Int (2 ^Int 256)
    andBool 0 <=Int ALLOW     andBool ALLOW     <Int (2 ^Int 256)
    andBool FROM_ID =/=Int TO_ID
    andBool VALUE     >Int BAL_FROM
    andBool RET_VAL ==Int 0
```

```{.k .transferFrom-failure}
[1b]

storage:
    keccak(#asByteStackInWidth(FROM_ID, 32)   ++ #asByteStackInWidth(1, 32)) |-> BAL_FROM
    keccak(#asByteStackInWidth(TO_ID, 32)     ++ #asByteStackInWidth(1, 32)) |-> BAL_TO
    keccak(#asByteStackInWidth(CALLER_ID, 32) ++ #asByteStackInWidth(keccak(#asByteStackInWidth(FROM_ID, 32) ++ #asByteStackInWidth(2, 32)), 32)) |-> ALLOW
    _:Map

requires:
     andBool 0 <=Int FROM_ID   andBool FROM_ID   <Int (2 ^Int 160)
     andBool 0 <=Int TO_ID     andBool TO_ID     <Int (2 ^Int 160)
     andBool 0 <Int VALUE     andBool  VALUE     <Int (2 ^Int 256)
     andBool 0 <=Int BAL_FROM  andBool BAL_FROM  <Int (2 ^Int 256)
     andBool 0 <=Int BAL_TO    andBool BAL_TO    <Int (2 ^Int 256)
     andBool 0 <=Int ALLOW     andBool ALLOW     <Int (2 ^Int 256)
     andBool FROM_ID =/=Int TO_ID
     andBool VALUE     >Int ALLOW
     andBool RET_VAL ==Int 0
```

Extra Solidity Exception Case When `VAL == 0`. Using

```{.k .transferFrom-failure}
[1c]

storage:
    keccak(#asByteStackInWidth(FROM_ID, 32)   ++ #asByteStackInWidth(1, 32)) |-> BAL_FROM
    keccak(#asByteStackInWidth(TO_ID, 32)     ++ #asByteStackInWidth(1, 32)) |-> BAL_TO
    keccak(#asByteStackInWidth(CALLER_ID, 32) ++ #asByteStackInWidth(keccak(#asByteStackInWidth(FROM_ID, 32) ++ #asByteStackInWidth(2, 32)), 32)) |-> ALLOW
    _:Map

requires:
     andBool 0 <=Int FROM_ID   andBool FROM_ID   <Int (2 ^Int 160)
     andBool 0 <=Int TO_ID     andBool TO_ID     <Int (2 ^Int 160)
     andBool 0 ==Int VALUE
     andBool 0 <=Int BAL_FROM  andBool BAL_FROM  <Int (2 ^Int 256)
     andBool 0 <=Int BAL_TO    andBool BAL_TO    <Int (2 ^Int 256)
     andBool 0 <=Int ALLOW     andBool ALLOW     <Int (2 ^Int 256)
     andBool FROM_ID =/=Int TO_ID
     andBool RET_VAL ==Int 0
```

#### Sub-case 2: the sender `FROM_ID` is equal to the recipient `TO_ID`. The sub-cases
are the same as for `transferFrom-failure1`

```{.k .transferFrom-failure}
[2a]

storage:
  keccak(#asByteStackInWidth(FROM_ID, 32)   ++ #asByteStackInWidth(1, 32)) |-> BAL_FROM
  keccak(#asByteStackInWidth(CALLER_ID, 32) ++ #asByteStackInWidth(keccak(#asByteStackInWidth(FROM_ID, 32) ++ #asByteStackInWidth(2, 32)), 32)) |-> ALLOW
  _:Map

requires:
     andBool 0 <=Int FROM_ID   andBool FROM_ID   <Int (2 ^Int 160)
     andBool 0 <=Int TO_ID     andBool TO_ID     <Int (2 ^Int 160)
     andBool 0 <Int VALUE     andBool  VALUE     <Int (2 ^Int 256)
     andBool 0 <=Int BAL_FROM  andBool BAL_FROM  <Int (2 ^Int 256)
     andBool 0 <=Int BAL_TO    andBool BAL_TO    <Int (2 ^Int 256)
     andBool 0 <=Int ALLOW     andBool ALLOW     <Int (2 ^Int 256)
     andBool FROM_ID ==Int TO_ID
     andBool VALUE    >Int BAL_FROM
     andBool RET_VAL ==Int 0
```

```{.k .transferFrom-failure}
[2b]

storage:
  keccak(#asByteStackInWidth(FROM_ID, 32)   ++ #asByteStackInWidth(1, 32)) |-> BAL_FROM
  keccak(#asByteStackInWidth(CALLER_ID, 32) ++ #asByteStackInWidth(keccak(#asByteStackInWidth(FROM_ID, 32) ++ #asByteStackInWidth(2, 32)), 32)) |-> ALLOW
  _:Map

requires:
     andBool 0 <=Int FROM_ID   andBool FROM_ID   <Int (2 ^Int 160)
     andBool 0 <=Int TO_ID     andBool TO_ID     <Int (2 ^Int 160)
     andBool 0 <Int VALUE     andBool  VALUE     <Int (2 ^Int 256)
     andBool 0 <=Int BAL_FROM  andBool BAL_FROM  <Int (2 ^Int 256)
     andBool 0 <=Int BAL_TO    andBool BAL_TO    <Int (2 ^Int 256)
     andBool 0 <=Int ALLOW     andBool ALLOW     <Int (2 ^Int 256)
     andBool FROM_ID ==Int TO_ID
     andBool VALUE    >Int ALLOW
     andBool RET_VAL ==Int 0
```

```{.k .transferFrom-failure}
[2c]

storage:
  keccak(#asByteStackInWidth(FROM_ID, 32)   ++ #asByteStackInWidth(1, 32)) |-> BAL_FROM
  keccak(#asByteStackInWidth(CALLER_ID, 32) ++ #asByteStackInWidth(keccak(#asByteStackInWidth(FROM_ID, 32) ++ #asByteStackInWidth(2, 32)), 32)) |-> ALLOW
  _:Map

requires:
     andBool 0 <=Int FROM_ID   andBool FROM_ID   <Int (2 ^Int 160)
     andBool 0 <=Int TO_ID     andBool TO_ID     <Int (2 ^Int 160)
     andBool 0 ==Int VALUE
     andBool 0 <=Int BAL_FROM  andBool BAL_FROM  <Int (2 ^Int 256)
     andBool 0 <=Int BAL_TO    andBool BAL_TO    <Int (2 ^Int 256)
     andBool 0 <=Int ALLOW     andBool ALLOW     <Int (2 ^Int 256)
     andBool FROM_ID ==Int TO_ID
     andBool RET_VAL ==Int 0
```

Specification Template
----------------------

```{.k .tmpl}
module {MODULE}-SPEC
  imports ETHEREUM-SIMULATION

  rule
    <k>         {K}          </k>
    <exit-code> 1            </exit-code>
    <mode>      NORMAL       </mode>
    <schedule>  DEFAULT      </schedule>
    <analysis>  /* _ */ .Map </analysis>

    <ethereum>
      <evm>
        <output>        /* _ */ .WordStack </output>
        <memoryUsed>    0 => _             </memoryUsed>
        <callDepth>     /* CALL_DEPTH */ 0 </callDepth>
        <callStack>     /* _ */ .List => _ </callStack>
        <interimStates> /* _ */ .List      </interimStates>
        <substateStack> /* _ */ .List      </substateStack>
        <callLog>       /* _ */ .Set       </callLog>

        <txExecState>
          <program>      %HKG_Program      </program>
          <programBytes> %HKG_ProgramBytes </programBytes>

          <id>        ACCT_ID         </id>
          <caller>    CALLER_ID       </caller>

          <callData>  {CALLDATA}      </callData>

          <callValue> 0               </callValue>
          <wordStack> .WordStack => _ </wordStack>
          <localMem>
            {LOCALMEM}
          </localMem>
          <pc>          0 => _ </pc>
          <gas>         {GAS}  </gas>
          <previousGas> _ => _ </previousGas>

          <static>      false  </static>
        </txExecState>

        <substate>
          <selfDestruct> /* _ */ .Set </selfDestruct>
          <log>          {LOG}        </log>
          <refund>       {REFUND}     </refund>
        </substate>

        <gasPrice>          _         </gasPrice>
        <origin>            ORIGIN_ID </origin>

        <previousHash>      _         </previousHash>
        <ommersHash>        _         </ommersHash>
        <coinbase>          _         </coinbase>
        <stateRoot>         _         </stateRoot>
        <transactionsRoot>  _         </transactionsRoot>
        <receiptsRoot>      _         </receiptsRoot>
        <logsBloom>         _         </logsBloom>
        <difficulty>        _         </difficulty>
        <number>            _         </number>
        <gasLimit>          _         </gasLimit>
        <gasUsed>           _         </gasUsed>
        <timestamp>         _         </timestamp>
        <extraData>         _         </extraData>
        <mixHash>           _         </mixHash>
        <blockNonce>        _         </blockNonce>

        <ommerBlockHeaders> _         </ommerBlockHeaders>
        <blockhash>         _         </blockhash>
      </evm>

      <network>
        <activeAccounts> ACCT_ID |-> false /* _ */ </activeAccounts>

        <accounts>
          <account>
            <acctID>  ACCT_ID           </acctID>
            <balance> _                 </balance>
            <code>    %HKG_ProgramBytes </code>
            <storage>
              {STORAGE}
            </storage>
            <nonce>   _                 </nonce>
          </account>
          /* _ */
        </accounts>

        <txOrder>   _            </txOrder>
        <txPending> _            </txPending>
        <messages>  /* _ */ .Bag </messages>
      </network>
    </ethereum>

    requires 0 <=Int ACCT_ID   andBool ACCT_ID   <Int (2 ^Int 160)
    andBool 0 <=Int CALLER_ID andBool CALLER_ID <Int (2 ^Int 160)
    andBool 0 <=Int ORIGIN_ID andBool ORIGIN_ID <Int (2 ^Int 160)
    {REQUIRES}

    {EPILOGUE}

    // to avoid unnecessary case split
    rule <k> LT W0 W1 => bool2int(W0  <Int W1) ~> #push ... </k> [trusted]
    rule <k> GT W0 W1 => bool2int(W0  >Int W1) ~> #push ... </k> [trusted]
    rule <k> EQ W0 W1 => bool2int(W0 ==Int W1) ~> #push ... </k> [trusted]
    rule <k> ISZERO W => bool2int(W  ==Int 0 ) ~> #push ... </k> [trusted]

endmodule
```
