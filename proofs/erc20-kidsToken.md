EVM-Specific ERC20 Specification
================================

We present a refinement of ERC20-K that specifies its detailed behaviors in EVM level.

In addition to the high-level ERC20 logic specified in ERC20-K, the EVM-level specification captures EVM-specific details such as gas consumption, data layout in storage, ABI encoding, byte representation of the program, and arithmetic overflows.

Abstractions
------------

We present the low-level specification in a succinct form using the abstractions introduced in the module [VERIFICATION](../../verification.md). The abstraction also makes the specification language-agnostic, meaning that it can be used for multiple programs that are compiled from different surface languages.

### Call Data

The ABI call abstraction allows to specify the call data in a function call notation. It specifies the function name and the (symbolic) arguments along with their types. For example, the following abstraction represents a data that encodes a call to the `transfer` function with two arguments: `TO`, the receiver account address of type `address` (an 160-bit unsigned integer), and `VALUE`, the value to transfer of type `unit256` (an 256-bit unsigned integer).

```
#abiCallData("transfer", #address(TO), #uint256(VALUE))
```

The above term is supposed to be desugared into the following byte array:

```
F1 : F2 : F3 : F4 : T1 : ... : T32 : V1 : ... : V32
```

where `F1 : F2 : F3 : F4` is the byte-array representation of 2835717307, the hash value of the function signature ABI encoding, `T1 : ... : T32` is the byte-array representation of the first argument `TO`, and `V1 : ... : V32` is the one of the second argument `VALUE`.

### Local Memory

The memory abstraction allows to specify the local memory as a map over words instead of byte-arrays.

For example, we succinctly specify that a return value `1` is stored in a return address `RET_ADDR`:

```
.Map[ RET_ADDR := #asByteStackInWidth(1, 32) ]
```

instead of specifying directly the underlying byte-array:

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

where `pos(map)` is the position of `map` appearing in the program, and `+` is the addition modulo `2^256`, while in Solidity, it is stored at:

```
hash(key2 ++ hash(key1 ++ pos(map)))
```

where `++` is the byte-array concatenation.

The hashed location abstraction allows to uniformly specify the locations in a form parameterized by the underlying compilers. For example, the location of `map[key1][key2]` can be specified as follows, where `{lang}` is a place-holder to be replaced by the name of the compiler.

```
#hashedLocation({lang}, pos(map), key1 key2)
```

This abstraction makes the specification independent of the underlying compilers, enabling it to be reused for differently compiled programs.


### Gas Consumption

Regarding the gas consumption of the program, the maximum gas amount is specified to ensure that the program does not consume more gas than the limit.

The verifier proves that the actual gas consumption is less than the provided limit, and also reports the exact amount of gas consumed during the execution. Indeed, it reports a set of the amounts since the gas consumption varies depending on the context (i.e., the input parameter values and the state of the storage). This provides the most precise gas analysis.



We present the specification for each function defined in the ERC20 standard. Here we focus on explaining the EVM-specific detailed behaviors, referring to the ERC20-K specification for the high-level logic.


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

`<localMem>` cell specifies that the local memory is empty in the beginning, but in the end, it will contain some contents including the return value `TOTAL`, the total supply of the tokens.

The other entries are represented by the wildcard symbol `_`, meaning that they are not relevant to the functional correctness of the program.

```{.k .erc20-spec .hkg-spec}
localMem:
      .Map
    =>
    (
      .Map[ RET_ADDR := #asByteStackInWidth(TOTAL, 32) ]
      _:Map
    )
```

`<gas>` cell specifies the maximum gas amount. Here we give a loose upper-bound for the demonstration purpose. In practice, one should set a reasonable amount of the gas limit to see if the program does not consume too much gas (i.e., no gas leakage).

```{.k .erc20-spec .hkg-spec}
gas: {gascap} => _
```

`<log>` cell specifies that no log is generated during the execution.

```{.k .erc20-spec .hkg-spec}
log: _
```

`<refund>` cell specifies that no gas is refunded. Note that it does not mean it consumes all the provided gas. The gas refund is different from returning the remaining gas after the execution. It is another notion to capture some specific gas refund events that happen, for example, when an unused storage entry is re-claimed (i.e., garbage-collected). The following specification ensures that no such event happens during the execution of the current function.

```{.k .erc20-spec .hkg-spec}
refund: _
```

`<storage>` cell specifies that the value of `totaySupply` is `TOTAL` and other entries are not relevant (and could be arbitrary values). Specifying the irrelevant entries implicitly expresses the non-interference property. That is, the total supply value will be returned regardless of what the other entires of the storage are. This representation of the irrelevant part is used throughout the entire specification, ensuring one of the principal security properties.

```{.k .erc20-spec .hkg-spec}
storage:
    #hashedLocation({lang}, {pos(totalsupply)}, .IntList) |-> TOTAL
    _:Map
```

The side-condition specifies the range of symbolic values based on their types.

```{.k .erc20-spec .hkg-spec}
requires:
    andBool 0 <=Int TOTAL     andBool TOTAL     <Int (2 ^Int 256)

comments:
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

gas: {gascap} => _

log: _

refund: _
```

`<storage>` cell specifies that the value of `balances[OWNER]` is `BAL`, which will be returned as described in `<localMem>` cell.

```{.k .erc20-spec .hkg-spec}
storage:
    #hashedLocation({lang}, {pos(balances)}, OWNER) |-> BAL
    _:Map

requires:
    andBool 0 <=Int OWNER     andBool OWNER     <Int (2 ^Int 160)
    andBool 0 <=Int BAL       andBool BAL       <Int (2 ^Int 256)

comments:
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

gas: {gascap} => _

log: _

refund: _
```

`<storage>` cell specifies that the value of `allowances[OWNER][SPENDER]` is `ALLOWANCE`, which will be returned as described in `<localMem>` cell.

```{.k .erc20-spec .hkg-spec}
storage:
    #hashedLocation({lang}, {pos(allowances)}, OWNER SPENDER) |-> ALLOWANCE
    _:Map

requires:
    andBool 0 <=Int OWNER     andBool OWNER     <Int (2 ^Int 160)
    andBool 0 <=Int SPENDER   andBool SPENDER   <Int (2 ^Int 160)
    andBool 0 <=Int ALLOWANCE andBool ALLOWANCE <Int (2 ^Int 256)

comments:
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
      .Map[ RET_ADDR := #asByteStackInWidth(1, 32) ]
      _:Map
    )

gas: {gascap} => _
```

`<log>` cell specifies that an event log is generated during the execution.

The log message contains the account ID of the current contract, the hash of the signature of event Approval, the account ID who calls this contract, the SPENDER account ID, and the approved VALUE. `#generateSignature` is a syntactic sugar, used to define the ABI call abstraction as well, that generates the event signature to be hashed.

```{.k .erc20-spec .hkg-spec}
log:
      _:List
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

Note that, however, we have not specified the refund detail since it is not essential for the functional correctness. We can specify that upon request.

```{.k .erc20-spec .hkg-spec}
refund: _ => _
```

`<storage>` cell specifies that the value of `allowances[CALLER_ID][SPENDER]` will be updated to `VALUE` after the execution.

```{.k .erc20-spec .hkg-spec}
storage:
    #hashedLocation({lang}, {pos(allowances)}, CALLER_ID SPENDER) |-> (OLDVALUE:Int => VALUE)
    _:Map
```

Unlike the ERC20-K specification, we do not specify the case when `VALUE` is less than 0 because it is not possible --- the `VALUE` parameter is of type `uint256`, an *unsigned* 256-bit integer.

Indeed, the ABI call mechanism will reject a call to this function if the `VALUE` is negative, which is out of the scope of the EVM-level specification since it happens in the network level outside the EVM execution.

```{.k .erc20-spec .hkg-spec}
requires:
    andBool 0 <=Int SPENDER   andBool SPENDER   <Int (2 ^Int 160)
    andBool 0 <=Int VALUE     andBool VALUE     <Int (2 ^Int 256)
    andBool 0 <=Int OLDVALUE  andBool OLDVALUE  <Int (2 ^Int 256)
    andBool notBool (VALUE =/=Int 0 andBool OLDVALUE =/=Int 0)

comments:
    // NOTE: negative VALUE is not possible since it is of `num256` type
```




transfer
--------

`transfer` function transfers the amount of VALUE from the caller to the account TO_ID.

```{.k .erc20-spec .hkg-spec}
[transfer]

callData: #abiCallData("transfer", #address(TO_ID), #uint256(VALUE))

gas: {gascap} => _
```

`transfer` function admits two types of behaviors: it either
- succeeds in transferring the value and returns true (i.e., 1), or
- fails due to the arithmetic overflow and throws an exception.

We present two specifications, one for each case.

### transfer success

```{.k .erc20-spec .hkg-spec}
[transfer-success]

k: #execute => (RETURN RET_ADDR:Int 32 ~> _)

localMem:
      .Map
    =>
    (
      .Map[ RET_ADDR := #asByteStackInWidth(1, 32) ]
      _:Map
    )

```

`<log>` cell specifies that it generates an event log of type `Transfer`.

```{.k .erc20-spec .hkg-spec}
log:
      _:List
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

refund: _ => _

requires:
    andBool 0 <=Int TO_ID     andBool TO_ID     <Int (2 ^Int 160)
    andBool 0 <=Int VALUE     andBool VALUE     <Int (2 ^Int 256)
    andBool 0 <=Int BAL_FROM  andBool BAL_FROM  <Int (2 ^Int 256)
    andBool 0 <=Int BAL_TO    andBool BAL_TO    <Int (2 ^Int 256)

comments:
    // NOTE: negative VALUE is not possible since it is of `num256` type
```

There are two sub-cases depending on whether the caller is equal to the recipient.

#### transfer success: sub-case 1: the caller `CALLER_ID` is different from the recipient `TO_ID`.

```{.k .erc20-spec .hkg-spec}
[transfer-success-1]
```

`<storage>` cell specifies that the amount of `VALUE` is transferred from `balances[CALLER_ID]` to `balances[TO_ID]`.

```{.k .erc20-spec .hkg-spec}
storage:
    #hashedLocation({lang}, {pos(balances)}, CALLER_ID) |-> (BAL_FROM => BAL_FROM -Int VALUE)
```

```{.k .erc20-spec}
    #hashedLocation({lang}, {pos(balances)}, TO_ID)     |-> (BAL_TO   => BAL_TO   +Int VALUE)
```

##### HKG-specific:
On the other hand, HKG token allows the additional overflow, “wrapping around” the balance if it is more than `2^256`, which is very unlikely but still a questionable behavior. See the difference where `+Word`, the addition modulo `2^256`, is used instead of `+Int`, the mathematical, arbitrary precision integer addition.

```{.k .hkg-spec}
    #hashedLocation({lang}, {pos(balances)}, TO_ID)     |-> (BAL_TO   => BAL_TO  +Int VALUE)
```

```{.k .erc20-spec .hkg-spec}
    _:Map

+requires:
    andBool CALLER_ID =/=Int TO_ID
```

The side-condition ensures that no arithmetic overflow happens.

```{.k .erc20-spec}
    andBool VALUE <=Int BAL_FROM
    andBool BAL_TO +Int VALUE <Int (2 ^Int 256) // viper overflow check: (VALUE ==Int 0 xorBool BAL_TO +Word VALUE >Int BAL_TO)
```

##### HKG-specific:
As mentioned earlier, HKG token does not check the overflow thus we have no side-condition for that. Instead, HKG token does not allow the zero value to be requested to transfer, which is questionable though, and we have the side-condition for that.

```{.k .hkg-spec}
    andBool VALUE <=Int BAL_FROM
    andBool VALUE >Int 0
    andBool BAL_TO +Int VALUE <Int (2 ^Int 256)
```


#### transfer success: sub-case 2: the caller `CALLER_ID` is equal to the recipient `TO_ID`.

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

The side-condition ensures that no arithmetic overflow (precisely underflow in this case) happens.

```{.k .erc20-spec}
    andBool VALUE <=Int BAL_FROM
```

##### HKG-specific:
As in the sub-case 1, HKG token requires having the additional side-condition of VALUE’s being greater than 0.

```{.k .hkg-spec}
    andBool VALUE <=Int BAL_FROM
    andBool VALUE >Int 0
    andBool BAL_FROM +Int VALUE <Int (2 ^Int 256)
```



### transfer failure

```{.k .erc20-spec .hkg-spec}
[transfer-failure]
```

`<k>` cell specifies that an exception will be thrown in the failure case.

Thus, the local memory is not relevant at all in this case.

```{.k .erc20-spec}
k: #execute => #exception

localMem: .Map => _:Map
```

##### HKG-specific:
HKG token does not throw the exception, but returns false in the failure case. Strictly speaking, this is still compliant with the ERC20 standard since the standard says that the `transfer` function “should” throw an exception for the failure, but not “must” do.

`<localMem>` cell says that it returns 0, i.e., false.

```{.k .hkg-spec}
k: #execute => (RETURN RET_ADDR:Int 32 ~> _)

localMem:
      .Map
    =>
    (
      .Map[ RET_ADDR := #asByteStackInWidth(0, 32) ]
      _:Map
    )
```

No log will be generated.

```{.k .erc20-spec .hkg-spec}
log: _

refund: _ => _

requires:
    andBool 0 <=Int TO_ID     andBool TO_ID     <Int (2 ^Int 160)
    andBool 0 <=Int VALUE     andBool VALUE     <Int (2 ^Int 256)
    andBool 0 <=Int BAL_FROM  andBool BAL_FROM  <Int (2 ^Int 256)
    andBool 0 <=Int BAL_TO    andBool BAL_TO    <Int (2 ^Int 256)

comments:
    // TODO: properly consider exception preserving the input status
    //       using CALL GCAP ACCTTO VALUE ARGSTART ARGWIDTH RETSTART RETWIDTH

    // NOTE: negative VALUE is not possible since it is of `num256` type
```

There are two sub-cases as well depending on whether the caller is equal to the recipient.

#### transfer failure: sub-case 1: the caller `CALLER_ID` is different from the recipient `TO_ID`.

```{.k .erc20-spec .hkg-spec}
[transfer-failure-1]

storage:
    #hashedLocation({lang}, {pos(balances)}, CALLER_ID) |-> (BAL_FROM => _)
    #hashedLocation({lang}, {pos(balances)}, TO_ID)     |->  BAL_TO
    _:Map

+requires:
    andBool CALLER_ID =/=Int TO_ID
```

The side-condition causing the arithmetic overflows, i.e., the negation of that of the success case (transfer success, sub-case 1):

```{.k .erc20-spec}
    andBool ( VALUE >Int BAL_FROM
     orBool   BAL_TO +Int VALUE >=Int (2 ^Int 256) ) // viper overflow check: ( VALUE =/=Int 0 andBool BAL_TO +Word VALUE <Int BAL_TO )
```

##### HKG-specific:
As in the success case, HKG token requires the different side-condition for the failure.

We split this case into another two sub-cases: one for each disjunct of the side-condition causing the failure, due to a limitation of the current K verifier that we are currently fixing.

Note that the sub-cases are to be disjoined (i.e, OR'ed) to represent the original side-condition.

```{.k .hkg-spec}
    andBool ( VALUE >Int BAL_FROM
     orBool   VALUE <=Int 0
     orBool   BAL_TO +Int VALUE >=Int (2 ^Int 256) )
```




#### transfer failure: sub-case 2: the caller `CALLER_ID` is equal to the recipient `TO_ID`.

```{.k .erc20-spec .hkg-spec}
[transfer-failure-2]

storage:
    #hashedLocation({lang}, {pos(balances)}, CALLER_ID) |-> BAL_FROM
    _:Map

+requires:
    andBool CALLER_ID ==Int TO_ID
```

The side-condition causing the arithmetic overflows, i.e., the negation of that of the success case (transfer success, sub-case 2):

```{.k .erc20-spec}
    andBool VALUE >Int BAL_FROM
```

##### HKG-specific:
As in the previous case, HKG token requires the different side-condition for the failure.

```{.k .hkg-spec}
    andBool ( VALUE >Int BAL_FROM
     orBool   VALUE <=Int 0
     orBool   BAL_FROM +Int VALUE >=Int (2 ^Int 256) )
```




transferFrom
------------

The specification of `transferFrom` is similar to that of `transfer`.

`transferFrom` function transfers the amount of VALUE from the (possibly remote) account FROM_ID to the account TO_ID provided that the caller is authorized to do so by the account FROM_ID.

```{.k .erc20-spec .hkg-spec}
[transferFrom]
callData: #abiCallData("transferFrom", #address(FROM_ID), #address(TO_ID), #uint256(VALUE))

gas: {gascap} => _
```

### transferFrom success

```{.k .erc20-spec .hkg-spec}
[transferFrom-success]

k: #execute => (RETURN RET_ADDR:Int 32 ~> _)

localMem:
      .Map
    =>
    (
      .Map[ RET_ADDR := #asByteStackInWidth(1, 32) ]
      _:Map
    )

log:
      _:List
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

refund: _ => _

requires:
    andBool 0 <=Int FROM_ID   andBool FROM_ID   <Int (2 ^Int 160)
    andBool 0 <=Int TO_ID     andBool TO_ID     <Int (2 ^Int 160)
    andBool 0 <=Int VALUE     andBool VALUE     <Int (2 ^Int 256)
    andBool 0 <=Int BAL_FROM  andBool BAL_FROM  <Int (2 ^Int 256)
    andBool 0 <=Int BAL_TO    andBool BAL_TO    <Int (2 ^Int 256)
    andBool 0 <=Int ALLOW     andBool ALLOW     <Int (2 ^Int 256)

comments:
    // NOTE: negative VALUE is not possible since it is of `num256` type
```

#### transferFrom success: sub-case 1: the sender `FROM_ID` is different from the recipient `TO_ID`.

```{.k .erc20-spec .hkg-spec}
[transferFrom-success-1]
```

`<storage>` cell specifies that the amount of `VALUE` will be transferred from `balances[FROM_ID]` to `balances[TO_ID]`, and the amount is deducted from `allowances[FROM_ID][CALLER_ID]` correspondingly.

```{.k .erc20-spec .hkg-spec}
storage:
    #hashedLocation({lang}, {pos(balances)},   FROM_ID)           |-> (BAL_FROM => BAL_FROM -Int VALUE)
```

```{.k .erc20-spec}
    #hashedLocation({lang}, {pos(balances)},   TO_ID)             |-> (BAL_TO   => BAL_TO   +Int VALUE)
```

##### HKG-specific:
As in `transfer` function, HKG token “wraps around” the balance without checking the additional overflow. See the difference between `+Int` and `+Word` in the above and the below.

```{.k .hkg-spec}
    #hashedLocation({lang}, {pos(balances)},   TO_ID)             |-> (BAL_TO   => BAL_TO  +Word VALUE)
```

```{.k .erc20-spec .hkg-spec}
    #hashedLocation({lang}, {pos(allowances)}, FROM_ID CALLER_ID) |-> (ALLOW    => ALLOW    -Int VALUE)
    _:Map

+requires:
    andBool FROM_ID =/=Int TO_ID
```

The side-condition that avoids the overflows.

```{.k .erc20-spec}
    andBool VALUE <=Int BAL_FROM
    andBool BAL_TO +Int VALUE <Int (2 ^Int 256) // viper overflow check: (VALUE ==Int 0 xorBool BAL_TO +Word VALUE >Int BAL_TO)
    andBool VALUE <=Int ALLOW
```

##### HKG-specific:
As in `transfer` function, it does not check the additional overflow but rejects the zero value to be transferred.

```{.k .hkg-spec}
    andBool VALUE <=Int BAL_FROM
    andBool VALUE <=Int ALLOW
    andBool VALUE >Int 0
    andBool BAL_TO +Int VALUE <Int (2 ^Int 256)
```

#### transferFrom success: sub-case 2: the sender `FROM_ID` is equal to the recipient `TO_ID`.

```{.k .erc20-spec .hkg-spec}
[transferFrom-success-2]

storage:
    #hashedLocation({lang}, {pos(balances)},   FROM_ID)           |-> BAL_FROM
    #hashedLocation({lang}, {pos(allowances)}, FROM_ID CALLER_ID) |-> (ALLOW => ALLOW -Int VALUE)
    _:Map

+requires:
    andBool FROM_ID ==Int TO_ID
```

The side-condition that avoids the overflows:

```{.k .erc20-spec}
    andBool VALUE <=Int BAL_FROM
    andBool VALUE <=Int ALLOW
```

##### HKG-specific:
The different side-condition for HKG token:

```{.k .hkg-spec}
    andBool VALUE <=Int BAL_FROM
    andBool VALUE <=Int ALLOW
    andBool VALUE >Int 0
    andBool BAL_FROM +Int VALUE <Int (2 ^Int 256)
```

### transferFrom failure

```{.k .erc20-spec .hkg-spec}
[transferFrom-failure]
```

```{.k .erc20-spec}
k: #execute => #exception

localMem: .Map => _:Map
```

##### HKG-specific:
As in `transfer`, HKG token returns false in the failure case.

```{.k .hkg-spec}
k: #execute => (RETURN RET_ADDR:Int 32 ~> _)

localMem:
      .Map
    =>
    (
      .Map[ RET_ADDR := #asByteStackInWidth(0, 32) ]
      _:Map
    )
```

```{.k .erc20-spec .hkg-spec}
log: _

refund: _ => _

requires:
    andBool 0 <=Int FROM_ID   andBool FROM_ID   <Int (2 ^Int 160)
    andBool 0 <=Int TO_ID     andBool TO_ID     <Int (2 ^Int 160)
    andBool 0 <=Int VALUE     andBool VALUE     <Int (2 ^Int 256)
    andBool 0 <=Int BAL_FROM  andBool BAL_FROM  <Int (2 ^Int 256)
    andBool 0 <=Int BAL_TO    andBool BAL_TO    <Int (2 ^Int 256)
    andBool 0 <=Int ALLOW     andBool ALLOW     <Int (2 ^Int 256)

comments:
    // TODO: properly consider exception preserving the input status
    //       using CALL GCAP ACCTTO VALUE ARGSTART ARGWIDTH RETSTART RETWIDTH

    // NOTE: negative VALUE is not possible since it is of `num256` type
```

#### transferFrom failure: sub-case 1: the sender `FROM_ID` is different from the recipient `TO_ID`.

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

##### HKG-specific:
The different side-condition for HKG token:

```{.k .hkg-spec}
    andBool ( VALUE >Int BAL_FROM
     orBool   VALUE >Int ALLOW
     orBool   VALUE <=Int 0
     orBool   BAL_TO +Int VALUE >=Int (2 ^Int 256) )
```


#### transferFrom failure: sub-case 2: the sender `FROM_ID` is equal to the recipient `TO_ID`.

```{.k .erc20-spec .hkg-spec}
[transferFrom-failure-2]

storage:
    #hashedLocation({lang}, {pos(balances)},   FROM_ID)           |-> BAL_FROM
    #hashedLocation({lang}, {pos(allowances)}, FROM_ID CALLER_ID) |-> ALLOW
    _:Map

+requires:
    andBool FROM_ID ==Int TO_ID
```

The side-condition causing the failure:

```{.k .erc20-spec}
    andBool ( VALUE >Int BAL_FROM
     orBool   VALUE >Int ALLOW )
```

##### HKG-specific:
The different side-condition for HKG token:

```{.k .hkg-spec}
   andBool ( VALUE >Int BAL_FROM
    orBool   VALUE >Int ALLOW
    orBool   VALUE <=Int 0 
    orBool   BAL_FROM +Int VALUE >=Int (2 ^Int 256))
```




Program Specification
---------------------

The above specification is parameterized by program-specific details consisting of the language compiler, `pos`, the position map for each global (i.e., storage) variables, and the compiled EVM bytecode.

We present two ERC20 token contracts: a Viper official ERC20 token and HKG token.

### Viper ERC20 Token

Shipped with the official Viper language compiler distribution, an ERC20 token, written in Viper by Phil Daian, is proved w.r.t. the above ERC20 specification, indicating that it faithfully conforms to the ERC20 standard.

We took the Viper source code from https://github.com/ethereum/vyper/tree/master/examples/tokens/ERC20_solidity_compatible, and compiled it down to EVM bytecode using the official Viper compiler 0.0.2 (of the commit id bf6ed1bfde2071ee2d5fdd6fbe1c09cf3bec44f2).

Specifically, the `code` is obtained by running the following command:
```
$ viper -f bytecode_runtime examples/tokens/ERC20_solidity_compatible/ERC20.v.py
```

```{.k .viper-pgm}
[DEFAULT]
lang: "Viper"
pos(balances): 0
pos(allowances): 1
pos(totalsupply): 2
code: "0x600035601c52740100000000000000000000000000000000000000006020526f7fffffffffffffffffffffffffffffff6040527fffffffffffffffffffffffffffffffff8000000000000000000000000000000060605274012a05f1fffffffffffffffffffffffffdabf41c006080527ffffffffffffffffffffffffed5fa0e000000000000000000000000000000000060a05263d0e30db06000511415610168573460008112585761014052336101605261016051600060c052602060c02001546101405161016051600060c052602060c020015401116101405115176100e657600080fd5b6101405161016051600060c052602060c02001540161016051600060c052602060c020015560025461014051600254011161014051151761012657600080fd5b610140516002540160025561014051610180526101605160007fddf252ad1be2c89b69c2b068fc378daa952ba7f163c4a11628f55a4df523b3ef6020610180a3005b632e1a7d4d6000511415610260576020600461014037341561018957600080fd5b33610160526101405161016051600060c052602060c020015410156101ad57600080fd5b6101405161016051600060c052602060c02001540361016051600060c052602060c02001556101405160025410156101e457600080fd5b61014051600254036002556000600060006000600160605161014051806040519013585780919012585702610160516000f161021f57600080fd5b61014051610180526000610160517fddf252ad1be2c89b69c2b068fc378daa952ba7f163c4a11628f55a4df523b3ef6020610180a3600160005260206000f3005b6318160ddd600051141561028657341561027957600080fd5b60025460005260206000f3005b6370a0823160005114156102cd57602060046101403734156102a757600080fd5b60043560205181101558575061014051600060c052602060c020015460005260206000f3005b63a9059cbb60005114156103e057604060046101403734156102ee57600080fd5b60043560205181101558575033610180526101605161018051600060c052602060c0200154101561031e57600080fd5b6101605161018051600060c052602060c02001540361018051600060c052602060c020015561014051600060c052602060c02001546101605161014051600060c052602060c0200154011161016051151761037857600080fd5b6101605161014051600060c052602060c02001540161014051600060c052602060c0200155610160516101a05261014051610180517fddf252ad1be2c89b69c2b068fc378daa952ba7f163c4a11628f55a4df523b3ef60206101a0a3600160005260206000f3005b6323b872dd6000511415610559576060600461014037341561040157600080fd5b600435602051811015585750602435602051811015585750336101a0526101a05161014051600160c052602060c0200160c052602060c02001546101c0526101805161014051600060c052602060c0200154101561045e57600080fd5b6101805161014051600060c052602060c02001540361014051600060c052602060c020015561016051600060c052602060c02001546101805161016051600060c052602060c020015401116101805115176104b857600080fd5b6101805161016051600060c052602060c02001540161016051600060c052602060c0200155610180516101c05110156104f057600080fd5b610180516101c051036101a05161014051600160c052602060c0200160c052602060c0200155610180516101e05261016051610140517fddf252ad1be2c89b69c2b068fc378daa952ba7f163c4a11628f55a4df523b3ef60206101e0a3600160005260206000f3005b63095ea7b360005114156105ef576040600461014037341561057a57600080fd5b6004356020518110155857503361018052610160516101405161018051600160c052602060c0200160c052602060c0200155610160516101a05261014051610180517f8c5be1e5ebec7d5bd14f71427d1e84f3dd0314c0f7b2291e5b200ac8c7c3b92560206101a0a3600160005260206000f3005b63dd62ed3e600051141561064f576040600461014037341561061057600080fd5b6004356020518110155857506024356020518110155857506101605161014051600160c052602060c0200160c052602060c020015460005260206000f3005b"
gascap: 100000
```

### Hacker Gold (HKG) Token

The HKG token is an implementation of the ERC20 specification written in Solidity.
The token became a [topic of discussion](https://www.ethnews.com/ethercamps-hkg-token-has-a-bug-and-needs-to-be-reissued) when a subtle vulnerability leads to a reissue.
The token had been originally audited by [Zeppelin](https://zeppelin.solutions/security-audits), and was deemed secure.

Specifically, the typographical error in the [HKG Token Solidity source](https://github.com/ether-camp/virtual-accelerator/issues/8) code came in the form of an `=+` statement being used in place of the desired `+=` when updating a receiver's balance during a transfer.
While typographically similar, these statements are semantically very different, with the former being equivalent to a simple `=` (the second plus saying that the expression following should be treated as positive) and the latter desugaring to add the right-hand quantity to the existing value in the variable on the left-hand side of the expression.
In testing, this error was missed, as the first balance updated would always work (with balance `=+` value being semantically equivalent to balance `+=` value when the balance is 0, in both cases assigning `value` to `balance`).
Even with the full decision or branch coverage in testing, multiple transfers on the same account can be entirely omitted in a way that is difficult to notice through human review.

We took the HKG source code from https://github.com/ether-camp/virtual-accelerator/blob/master/contracts/StandardToken.sol, where we inlined the following import
```
import "TokenInterface.sol";
```
by replacing it with the code from https://github.com/ether-camp/virtual-accelerator/blob/master/contracts/TokenInterface.sol, and compiled it to EVM using Remix Solidity IDE (of the version soljson-v0.4.19+commit.c4cbbb05).

The Solidity source code can be found in [proofs/solidity/hkg-token-correct.sol](proofs/solidity/hkg-token-correct.sol).

```{.k .hkg-pgm}
[DEFAULT]
lang: "Solidity"
pos(balances): 1
pos(allowances): 2
pos(totalsupply): 5
code: "0x6060604052600436106100e6576000357c0100000000000000000000000000000000000000000000000000000000900463ffffffff16806306fdde0314610915578063095ea7b3146109a35780630dcf4b8f146109fd57806318160ddd14610a2657806323b872dd14610a4f578063313ce56714610ac857806364acdb7714610af757806370a0823114610b0c5780638f58099614610b5957806395d89b4114610b6e57806398b01fe314610bfc578063a9059cbb14610c25578063c59d484714610c7f578063da040c0f14610cc1578063dd62ed3e14610cee578063e58fc54c14610d5a575b600080600080600060149054906101000a900460ff16151561010757600080fd5b60003414156101155761090f565b6000809054906101000a900473ffffffffffffffffffffffffffffffffffffffff1673ffffffffffffffffffffffffffffffffffffffff166108fc349081150290604051600060405180830381858888f19350505050151561017657600080fd5b34600360008282540192505081905550606434029350662386f26fc100003410151561084c57600354840193506003414342600060405160200152604051808473ffffffffffffffffffffffffffffffffffffffff1673ffffffffffffffffffffffffffffffffffffffff166c01000000000000000000000000028152601401838152602001828152602001935050505060206040518083038160008661646e5a03f1151561022457600080fd5b5050604051516c0100000000000000000000000002925060007f01000000000000000000000000000000000000000000000000000000000000000283600060148110151561026e57fe5b1a7f0100000000000000000000000000000000000000000000000000000000000000027effffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff1916141561084b5760007f01000000000000000000000000000000000000000000000000000000000000000260807f01000000000000000000000000000000000000000000000000000000000000000284600160148110151561031057fe5b1a7f010000000000000000000000000000000000000000000000000000000000000002167effffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff19161415610363576000610366565b60015b60007f01000000000000000000000000000000000000000000000000000000000000000260407f0100000000000000000000000000000000000000000000000000000000000000028560016014811015156103bd57fe5b1a7f010000000000000000000000000000000000000000000000000000000000000002167effffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff19161415610410576000610413565b60015b60007f01000000000000000000000000000000000000000000000000000000000000000260207f01000000000000000000000000000000000000000000000000000000000000000286600160148110151561046a57fe5b1a7f010000000000000000000000000000000000000000000000000000000000000002167effffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff191614156104bd5760006104c0565b60015b60007f01000000000000000000000000000000000000000000000000000000000000000260107f01000000000000000000000000000000000000000000000000000000000000000287600160148110151561051757fe5b1a7f010000000000000000000000000000000000000000000000000000000000000002167effffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff1916141561056a57600061056d565b60015b60007f01000000000000000000000000000000000000000000000000000000000000000260087f0100000000000000000000000000000000000000000000000000000000000000028860016014811015156105c457fe5b1a7f010000000000000000000000000000000000000000000000000000000000000002167effffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff1916141561061757600061061a565b60015b60007f01000000000000000000000000000000000000000000000000000000000000000260047f01000000000000000000000000000000000000000000000000000000000000000289600160148110151561067157fe5b1a7f010000000000000000000000000000000000000000000000000000000000000002167effffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff191614156106c45760006106c7565b60015b60007f01000000000000000000000000000000000000000000000000000000000000000260027f0100000000000000000000000000000000000000000000000000000000000000028a600160148110151561071e57fe5b1a7f010000000000000000000000000000000000000000000000000000000000000002167effffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff19161415610771576000610774565b60015b60007f01000000000000000000000000000000000000000000000000000000000000000260017f0100000000000000000000000000000000000000000000000000000000000000028b60016014811015156107cb57fe5b1a7f010000000000000000000000000000000000000000000000000000000000000002167effffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff1916141561081e576000610821565b60015b0101010101010191508160ff16606434020290508084019350806004600082825401925050819055505b5b8360056000828254019250508190555083600160003373ffffffffffffffffffffffffffffffffffffffff1673ffffffffffffffffffffffffffffffffffffffff168152602001908152602001600020600082825401925050819055503373ffffffffffffffffffffffffffffffffffffffff163073ffffffffffffffffffffffffffffffffffffffff167fddf252ad1be2c89b69c2b068fc378daa952ba7f163c4a11628f55a4df523b3ef866040518082815260200191505060405180910390a35b50505050005b341561092057600080fd5b610928610dab565b6040518080602001828103825283818151815260200191508051906020019080838360005b8381101561096857808201518184015260208101905061094d565b50505050905090810190601f1680156109955780820380516001836020036101000a031916815260200191505b509250505060405180910390f35b34156109ae57600080fd5b6109e3600480803573ffffffffffffffffffffffffffffffffffffffff16906020019091908035906020019091905050610dee565b604051808215151515815260200191505060405180910390f35b3415610a0857600080fd5b610a10610f7c565b6040518082815260200191505060405180910390f35b3415610a3157600080fd5b610a39610f82565b6040518082815260200191505060405180910390f35b3415610a5a57600080fd5b610aae600480803573ffffffffffffffffffffffffffffffffffffffff1690602001909190803573ffffffffffffffffffffffffffffffffffffffff16906020019091908035906020019091905050610f88565b604051808215151515815260200191505060405180910390f35b3415610ad357600080fd5b610adb6112c3565b604051808260ff1660ff16815260200191505060405180910390f35b3415610b0257600080fd5b610b0a6112cc565b005b3415610b1757600080fd5b610b43600480803573ffffffffffffffffffffffffffffffffffffffff16906020019091905050611343565b6040518082815260200191505060405180910390f35b3415610b6457600080fd5b610b6c61138c565b005b3415610b7957600080fd5b610b81611404565b6040518080602001828103825283818151815260200191508051906020019080838360005b83811015610bc1578082015181840152602081019050610ba6565b50505050905090810190601f168015610bee5780820380516001836020036101000a031916815260200191505b509250505060405180910390f35b3415610c0757600080fd5b610c0f611447565b6040518082815260200191505060405180910390f35b3415610c3057600080fd5b610c65600480803573ffffffffffffffffffffffffffffffffffffffff1690602001909190803590602001909190505061144d565b604051808215151515815260200191505060405180910390f35b3415610c8a57600080fd5b610c9261166a565b604051808581526020018481526020018381526020018215151515815260200194505050505060405180910390f35b3415610ccc57600080fd5b610cd4611697565b604051808215151515815260200191505060405180910390f35b3415610cf957600080fd5b610d44600480803573ffffffffffffffffffffffffffffffffffffffff1690602001909190803573ffffffffffffffffffffffffffffffffffffffff169060200190919050506116aa565b6040518082815260200191505060405180910390f35b3415610d6557600080fd5b610d91600480803573ffffffffffffffffffffffffffffffffffffffff16906020019091905050611731565b604051808215151515815260200191505060405180910390f35b610db3611944565b6040805190810160405280601781526020017f4d79204b69647320456475636174696f6e20546f6b656e000000000000000000815250905090565b6000808214158015610e7d57506000600260003373ffffffffffffffffffffffffffffffffffffffff1673ffffffffffffffffffffffffffffffffffffffff16815260200190815260200160002060008573ffffffffffffffffffffffffffffffffffffffff1673ffffffffffffffffffffffffffffffffffffffff1681526020019081526020016000205414155b15610e8b5760009050610f76565b81600260003373ffffffffffffffffffffffffffffffffffffffff1673ffffffffffffffffffffffffffffffffffffffff16815260200190815260200160002060008573ffffffffffffffffffffffffffffffffffffffff1673ffffffffffffffffffffffffffffffffffffffff168152602001908152602001600020819055508273ffffffffffffffffffffffffffffffffffffffff163373ffffffffffffffffffffffffffffffffffffffff167f8c5be1e5ebec7d5bd14f71427d1e84f3dd0314c0f7b2291e5b200ac8c7c3b925846040518082815260200191505060405180910390a3600190505b92915050565b60035481565b60055481565b600080600080600080606460003690501015610fa357600080fd5b6000871415610fb557600095506112b7565b600160008a73ffffffffffffffffffffffffffffffffffffffff1673ffffffffffffffffffffffffffffffffffffffff168152602001908152602001600020549450600260008a73ffffffffffffffffffffffffffffffffffffffff1673ffffffffffffffffffffffffffffffffffffffff16815260200190815260200160002060003373ffffffffffffffffffffffffffffffffffffffff1673ffffffffffffffffffffffffffffffffffffffff168152602001908152602001600020549350868510159250868410159150600160008973ffffffffffffffffffffffffffffffffffffffff1673ffffffffffffffffffffffffffffffffffffffff1681526020019081526020016000205487600160008b73ffffffffffffffffffffffffffffffffffffffff1673ffffffffffffffffffffffffffffffffffffffff16815260200190815260200160002054011090508280156111115750815b801561111b575080155b156112b25786600160008a73ffffffffffffffffffffffffffffffffffffffff1673ffffffffffffffffffffffffffffffffffffffff1681526020019081526020016000206000828254019250508190555086600160008b73ffffffffffffffffffffffffffffffffffffffff1673ffffffffffffffffffffffffffffffffffffffff1681526020019081526020016000206000828254039250508190555086600260008b73ffffffffffffffffffffffffffffffffffffffff1673ffffffffffffffffffffffffffffffffffffffff16815260200190815260200160002060003373ffffffffffffffffffffffffffffffffffffffff1673ffffffffffffffffffffffffffffffffffffffff168152602001908152602001600020600082825403925050819055508773ffffffffffffffffffffffffffffffffffffffff168973ffffffffffffffffffffffffffffffffffffffff167fddf252ad1be2c89b69c2b068fc378daa952ba7f163c4a11628f55a4df523b3ef896040518082815260200191505060405180910390a3600195506112b7565b600095505b50505050509392505050565b60006012905090565b6000809054906101000a900473ffffffffffffffffffffffffffffffffffffffff1673ffffffffffffffffffffffffffffffffffffffff163373ffffffffffffffffffffffffffffffffffffffff1614151561132757600080fd5b60008060146101000a81548160ff021916908315150217905550565b6000600160008373ffffffffffffffffffffffffffffffffffffffff1673ffffffffffffffffffffffffffffffffffffffff168152602001908152602001600020549050919050565b6000809054906101000a900473ffffffffffffffffffffffffffffffffffffffff1673ffffffffffffffffffffffffffffffffffffffff163373ffffffffffffffffffffffffffffffffffffffff161415156113e757600080fd5b6001600060146101000a81548160ff021916908315150217905550565b61140c611944565b6040805190810160405280600481526020017f4d544b4500000000000000000000000000000000000000000000000000000000815250905090565b60045481565b60008060008060446000369050101561146557600080fd5b60008514156114775760009350611661565b600160003373ffffffffffffffffffffffffffffffffffffffff1673ffffffffffffffffffffffffffffffffffffffff168152602001908152602001600020549250848310159150600160008773ffffffffffffffffffffffffffffffffffffffff1673ffffffffffffffffffffffffffffffffffffffff1681526020019081526020016000205485600160008973ffffffffffffffffffffffffffffffffffffffff1673ffffffffffffffffffffffffffffffffffffffff168152602001908152602001600020540110905081801561154f575080155b1561165c5784600160003373ffffffffffffffffffffffffffffffffffffffff1673ffffffffffffffffffffffffffffffffffffffff1681526020019081526020016000206000828254039250508190555084600160008873ffffffffffffffffffffffffffffffffffffffff1673ffffffffffffffffffffffffffffffffffffffff168152602001908152602001600020600082825401925050819055508573ffffffffffffffffffffffffffffffffffffffff163373ffffffffffffffffffffffffffffffffffffffff167fddf252ad1be2c89b69c2b068fc378daa952ba7f163c4a11628f55a4df523b3ef876040518082815260200191505060405180910390a360019350611661565b600093505b50505092915050565b600080600080600354600554600454600060149054906101000a900460ff16935093509350935090919293565b600060149054906101000a900460ff1681565b6000600260008473ffffffffffffffffffffffffffffffffffffffff1673ffffffffffffffffffffffffffffffffffffffff16815260200190815260200160002060008373ffffffffffffffffffffffffffffffffffffffff1673ffffffffffffffffffffffffffffffffffffffff16815260200190815260200160002054905092915050565b60008060008060009054906101000a900473ffffffffffffffffffffffffffffffffffffffff1673ffffffffffffffffffffffffffffffffffffffff163373ffffffffffffffffffffffffffffffffffffffff1614151561179157600080fd5b8391508173ffffffffffffffffffffffffffffffffffffffff166370a08231306000604051602001526040518263ffffffff167c0100000000000000000000000000000000000000000000000000000000028152600401808273ffffffffffffffffffffffffffffffffffffffff1673ffffffffffffffffffffffffffffffffffffffff168152602001915050602060405180830381600087803b151561183757600080fd5b6102c65a03f1151561184857600080fd5b5050506040518051905090508173ffffffffffffffffffffffffffffffffffffffff1663a9059cbb6000809054906101000a900473ffffffffffffffffffffffffffffffffffffffff16836000604051602001526040518363ffffffff167c0100000000000000000000000000000000000000000000000000000000028152600401808373ffffffffffffffffffffffffffffffffffffffff1673ffffffffffffffffffffffffffffffffffffffff16815260200182815260200192505050602060405180830381600087803b151561192057600080fd5b6102c65a03f1151561193157600080fd5b5050506040518051905092505050919050565b6020604051908101604052806000815250905600a165627a7a72305820452eddcdd3016aa2e6ed731e9e892479cf3b3d58b30492649f7bbf6b880431e30029"
gascap: 100000
```

Specification Template
----------------------

The above specification mentions only the relevant and essential part of the entire configuration (i.e., the VM and network state) to be succinct and close to the high-level specification ERC20-K.

We present the other part of the configuration, which, combined with the above, forms the complete specification to be passed into the underlying theorem prover.

```{.k .tmpl}
module {module}-SPEC
  imports ETHEREUM-SIMULATION

  rule
    <k> {k} </k>
    <exit-code> 1 </exit-code>
    <mode> NORMAL </mode>
    <schedule> DEFAULT </schedule> // TODO: pick a right one
    <analysis> .Map </analysis> // not part of evm

    <ethereum>
      <evm>
        <output> _ </output>
        <memoryUsed> 0 => _ </memoryUsed>
        <callDepth> CALL_DEPTH </callDepth>
        <callStack> _ => _ </callStack>
        <interimStates> _ </interimStates>
        <substateStack> _ </substateStack>
        <callLog> .Set </callLog> // for vmtest only

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
          <gas> {gas} </gas>
          <previousGas> _ => _ </previousGas>

          <static> false </static> // NOTE: non-static call
        </txExecState>

        <substate>
          <selfDestruct> _ </selfDestruct>
          <log>
            {log}
          </log>
          <refund> {refund} </refund> // TODO: more detail
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
        <activeAccounts> ACCT_ID |-> false _:Map </activeAccounts>

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
       // ... // TODO: fix
        </accounts>

        <txOrder> _ </txOrder>
        <txPending> _ </txPending>
        <messages> _ </messages>
      </network>
    </ethereum>
    requires 0 <=Int ACCT_ID    andBool ACCT_ID    <Int (2 ^Int 160)
     andBool 0 <=Int CALLER_ID  andBool CALLER_ID  <Int (2 ^Int 160)
     andBool 0 <=Int ORIGIN_ID  andBool ORIGIN_ID  <Int (2 ^Int 160)
     andBool 0 <=Int CALL_DEPTH andBool CALL_DEPTH <Int 1024
     {requires}

{comments}
```

Below are an abstract semantics of the four instruction, LT, GT, EQ, and ISZERO, that improves the performance of the underlying theorem prover’s symbolic reasoning by avoiding unnecessary case analyses.

```{.k .tmpl}
  // to avoid unnecessary case analyses
  rule <k> LT W0 W1 => bool2int(W0  <Int W1) ~> #push ... </k> [trusted]
  rule <k> GT W0 W1 => bool2int(W0  >Int W1) ~> #push ... </k> [trusted]
  rule <k> EQ W0 W1 => bool2int(W0 ==Int W1) ~> #push ... </k> [trusted]
  rule <k> ISZERO W => bool2int(W  ==Int 0 ) ~> #push ... </k> [trusted]

endmodule
```
