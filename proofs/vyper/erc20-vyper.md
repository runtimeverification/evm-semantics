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

```{.k .totalSupply}
k: #execute => (RETURN RET_ADDR:Int 32 ~> _)

callData: #abiCallData("totalSupply", .TypedArgs)
```

`<localMem>` cell specifies that the local memory is empty in the beginning, but in the end, it will contain some contents including the return value `TOTAL`, the total supply.

The other entries are represented by the wildcard symbol `_`, meaning that they are not relevant to the correctness.

```{.k .totalSupply}
localMem:
      .Map
    =>
    (
      .Map[ RET_ADDR := #asByteStackInWidth(TOTAL, 32) ]
      _:Map
    )
```

`<gas>` cell specifies the maximum gas amount. Here we give a loose upper-bound for the demonstration purpose. In practice, one should set a reasonable amount of the gas limit to see if the program does not consume too much gas ensuring no gas leakage.

```{.k .totalSupply}
gas:
    /* G */ 100000 => _
```

`<log>` cell specifies that no log is generated during the execution.

```{.k .totalSupply}
log:
    /* _ */ .List
```

`<refund>` cell specifies that no gas is refunded. Note that it does not mean it consumes all the provided gas. The gas refund happens only for some situation, e.g., re-claiming (i.e., garbage-collecting) unused storage entries.

```{.k .totalSupply}
refund:
    /* _ */ 0
```

`<storage>` cell specifies that the value of `totaySupply` is `TOTAL` and other entries are not relevant (could be arbitrary values). Note that `pos(totalSupply) = 2`.

```{.k .totalSupply}
storage:
    2 |-> TOTAL
    _:Map
```

The side-condition specifies both the minimum and the maximum values of the symbolic values based on their types.

```{.k .totalSupply}
requires:
    andBool 0 <=Int TOTAL     andBool TOTAL     <Int (2 ^Int 256)

epilogue:
```




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

`<storage>` cell specifies that the value of `balances[OWNER]` is `BAL`, which is in our interest. Note that `pos(balances) = 0`.

```{.k .balanceOf}
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

`<storage>` cell specifies that the value of `allowances[OWNER][SPENDER]` is `ALLOWANCE`, where `pos(allowances) = 1`.

```{.k .allowance}
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
    sha3(sha3(1) +Word CALLER_ID) +Word SPENDER |-> (_:Int => VALUE)
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
```

There are two sub-cases depending on whether the caller is equal to the recipient. 

#### Sub-case 1: the caller `CALLER_ID` is different from the recipient `TO_ID`.

```{.k .transfer-success}
[1]
```

`<storage>` cell specifies that the amount of `VALUE` is transferred from `balances[CALLER_ID]` to `balances[TO_ID]`.

```{.k .transfer-success}
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

```{.k .transfer-success}
    andBool VALUE <=Int BAL_FROM
    andBool BAL_TO +Int VALUE <Int (2 ^Int 256) // viper overflow check: (VALUE ==Int 0 xorBool BAL_TO +Word VALUE >Int BAL_TO)
    andBool RET_VAL ==Int 1
```

#### Sub-case 2: the caller `CALLER_ID` is equal to the recipient `TO_ID`.

```{.k .transfer-success}
[2]
```

`<storage>` cell specifies that `balances[CALLER_ID]` is not changed since the value is transferred to himself.

```{.k .transfer-success}
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

```{.k .transfer-success}
    andBool VALUE <=Int BAL_FROM
    andBool RET_VAL ==Int 1
```



### Case of failure

```{.k .transfer-failure}
[DEFAULT]
```

`<k>` cell specifies that an exception will be thrown for the failure case.

```{.k .transfer-failure}
k: #execute => #exception

callData: #abiCallData("transfer", #address(TO_ID), #uint256(VALUE))
```

The local memory is not relevant at all in this case.

```{.k .transfer-failure}
localMem:
    .Map => _:Map

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

#### Sub-case 1: the caller `CALLER_ID` is different from the recipient `TO_ID`.

```{.k .transfer-failure}
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

```{.k .transfer-failure}
    andBool ( VALUE >Int BAL_FROM
     orBool   BAL_TO +Int VALUE >=Int (2 ^Int 256) ) // viper overflow check: ( VALUE =/=Int 0 andBool BAL_TO +Word VALUE <Int BAL_TO )
```

#### Sub-case 2: the caller `CALLER_ID` is equal to the recipient `TO_ID`.

```{.k .transfer-failure}
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

```{.k .transfer-failure}
    andBool VALUE >Int BAL_FROM
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
```

#### Sub-case 1: the sender `FROM_ID` is different from the recipient `TO_ID`.

```{.k .transferFrom-success}
[1]
```

`<storage>` cell specifies that the amount of `VALUE` will be transferred from `balances[FROM_ID]` to `balances[TO_ID]`, and the amount is deducted from `allowances[FROM_ID][CALLER_ID]` correspondingly.

```{.k .transferFrom-success}
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

```{.k .transferFrom-success}
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

```{.k .transferFrom-failure}
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

```{.k .transferFrom-failure}
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

```{.k .transferFrom-failure}
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


Specification Template
----------------------

```{.k .tmpl}
module {MODULE}-SPEC
  imports ETHEREUM-SIMULATION

  rule
    <k> {K} </k>
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
          <program>
            #asMapOpCodes(#dasmOpCodes(#parseByteStack(
              "0x600035601c52740100000000000000000000000000000000000000006020526f7fffffffffffffffffffffffffffffff6040527fffffffffffffffffffffffffffffffff8000000000000000000000000000000060605274012a05f1fffffffffffffffffffffffffdabf41c006080527ffffffffffffffffffffffffed5fa0e000000000000000000000000000000000060a05263d0e30db06000511415610168573460008112585761014052336101605261016051600060c052602060c02001546101405161016051600060c052602060c020015401116101405115176100e657600080fd5b6101405161016051600060c052602060c02001540161016051600060c052602060c020015560025461014051600254011161014051151761012657600080fd5b610140516002540160025561014051610180526101605160007fddf252ad1be2c89b69c2b068fc378daa952ba7f163c4a11628f55a4df523b3ef6020610180a3005b632e1a7d4d6000511415610260576020600461014037341561018957600080fd5b33610160526101405161016051600060c052602060c020015410156101ad57600080fd5b6101405161016051600060c052602060c02001540361016051600060c052602060c02001556101405160025410156101e457600080fd5b61014051600254036002556000600060006000600160605161014051806040519013585780919012585702610160516000f161021f57600080fd5b61014051610180526000610160517fddf252ad1be2c89b69c2b068fc378daa952ba7f163c4a11628f55a4df523b3ef6020610180a3600160005260206000f3005b6318160ddd600051141561028657341561027957600080fd5b60025460005260206000f3005b6370a0823160005114156102cd57602060046101403734156102a757600080fd5b60043560205181101558575061014051600060c052602060c020015460005260206000f3005b63a9059cbb60005114156103e057604060046101403734156102ee57600080fd5b60043560205181101558575033610180526101605161018051600060c052602060c0200154101561031e57600080fd5b6101605161018051600060c052602060c02001540361018051600060c052602060c020015561014051600060c052602060c02001546101605161014051600060c052602060c0200154011161016051151761037857600080fd5b6101605161014051600060c052602060c02001540161014051600060c052602060c0200155610160516101a05261014051610180517fddf252ad1be2c89b69c2b068fc378daa952ba7f163c4a11628f55a4df523b3ef60206101a0a3600160005260206000f3005b6323b872dd6000511415610559576060600461014037341561040157600080fd5b600435602051811015585750602435602051811015585750336101a0526101a05161014051600160c052602060c0200160c052602060c02001546101c0526101805161014051600060c052602060c0200154101561045e57600080fd5b6101805161014051600060c052602060c02001540361014051600060c052602060c020015561016051600060c052602060c02001546101805161016051600060c052602060c020015401116101805115176104b857600080fd5b6101805161016051600060c052602060c02001540161016051600060c052602060c0200155610180516101c05110156104f057600080fd5b610180516101c051036101a05161014051600160c052602060c0200160c052602060c0200155610180516101e05261016051610140517fddf252ad1be2c89b69c2b068fc378daa952ba7f163c4a11628f55a4df523b3ef60206101e0a3600160005260206000f3005b63095ea7b360005114156105ef576040600461014037341561057a57600080fd5b6004356020518110155857503361018052610160516101405161018051600160c052602060c0200160c052602060c0200155610160516101a05261014051610180517f8c5be1e5ebec7d5bd14f71427d1e84f3dd0314c0f7b2291e5b200ac8c7c3b92560206101a0a3600160005260206000f3005b63dd62ed3e600051141561064f576040600461014037341561061057600080fd5b6004356020518110155857506024356020518110155857506101605161014051600160c052602060c0200160c052602060c020015460005260206000f3005b"
            ),DEFAULT))
          </program>
          <programBytes>
            #parseByteStack(
              "0x600035601c52740100000000000000000000000000000000000000006020526f7fffffffffffffffffffffffffffffff6040527fffffffffffffffffffffffffffffffff8000000000000000000000000000000060605274012a05f1fffffffffffffffffffffffffdabf41c006080527ffffffffffffffffffffffffed5fa0e000000000000000000000000000000000060a05263d0e30db06000511415610168573460008112585761014052336101605261016051600060c052602060c02001546101405161016051600060c052602060c020015401116101405115176100e657600080fd5b6101405161016051600060c052602060c02001540161016051600060c052602060c020015560025461014051600254011161014051151761012657600080fd5b610140516002540160025561014051610180526101605160007fddf252ad1be2c89b69c2b068fc378daa952ba7f163c4a11628f55a4df523b3ef6020610180a3005b632e1a7d4d6000511415610260576020600461014037341561018957600080fd5b33610160526101405161016051600060c052602060c020015410156101ad57600080fd5b6101405161016051600060c052602060c02001540361016051600060c052602060c02001556101405160025410156101e457600080fd5b61014051600254036002556000600060006000600160605161014051806040519013585780919012585702610160516000f161021f57600080fd5b61014051610180526000610160517fddf252ad1be2c89b69c2b068fc378daa952ba7f163c4a11628f55a4df523b3ef6020610180a3600160005260206000f3005b6318160ddd600051141561028657341561027957600080fd5b60025460005260206000f3005b6370a0823160005114156102cd57602060046101403734156102a757600080fd5b60043560205181101558575061014051600060c052602060c020015460005260206000f3005b63a9059cbb60005114156103e057604060046101403734156102ee57600080fd5b60043560205181101558575033610180526101605161018051600060c052602060c0200154101561031e57600080fd5b6101605161018051600060c052602060c02001540361018051600060c052602060c020015561014051600060c052602060c02001546101605161014051600060c052602060c0200154011161016051151761037857600080fd5b6101605161014051600060c052602060c02001540161014051600060c052602060c0200155610160516101a05261014051610180517fddf252ad1be2c89b69c2b068fc378daa952ba7f163c4a11628f55a4df523b3ef60206101a0a3600160005260206000f3005b6323b872dd6000511415610559576060600461014037341561040157600080fd5b600435602051811015585750602435602051811015585750336101a0526101a05161014051600160c052602060c0200160c052602060c02001546101c0526101805161014051600060c052602060c0200154101561045e57600080fd5b6101805161014051600060c052602060c02001540361014051600060c052602060c020015561016051600060c052602060c02001546101805161016051600060c052602060c020015401116101805115176104b857600080fd5b6101805161016051600060c052602060c02001540161016051600060c052602060c0200155610180516101c05110156104f057600080fd5b610180516101c051036101a05161014051600160c052602060c0200160c052602060c0200155610180516101e05261016051610140517fddf252ad1be2c89b69c2b068fc378daa952ba7f163c4a11628f55a4df523b3ef60206101e0a3600160005260206000f3005b63095ea7b360005114156105ef576040600461014037341561057a57600080fd5b6004356020518110155857503361018052610160516101405161018051600160c052602060c0200160c052602060c0200155610160516101a05261014051610180517f8c5be1e5ebec7d5bd14f71427d1e84f3dd0314c0f7b2291e5b200ac8c7c3b92560206101a0a3600160005260206000f3005b63dd62ed3e600051141561064f576040600461014037341561061057600080fd5b6004356020518110155857506024356020518110155857506101605161014051600160c052602060c0200160c052602060c020015460005260206000f3005b"
            )
          </programBytes>

          <id> ACCT_ID </id> // contract owner
          <caller> CALLER_ID </caller> // who called this contract; in the begining, origin

          <callData> {CALLDATA} </callData>

          <callValue> 0 </callValue>
          <wordStack> .WordStack => _ </wordStack>
          <localMem>
            {LOCALMEM}
          </localMem>
          <pc> 0 => _ </pc>
          <gas> {GAS} </gas> // NOTE: user provided
          <previousGas> _ => _ </previousGas>

          <static> false </static> // NOTE: non-static call
        </txExecState>

        <substate>
          <selfDestruct> /* _ */ .Set </selfDestruct>
          <log>
            {LOG}
          </log>
          <refund> {REFUND} </refund>
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
            <code>
              #parseByteStack(
              "0x600035601c52740100000000000000000000000000000000000000006020526f7fffffffffffffffffffffffffffffff6040527fffffffffffffffffffffffffffffffff8000000000000000000000000000000060605274012a05f1fffffffffffffffffffffffffdabf41c006080527ffffffffffffffffffffffffed5fa0e000000000000000000000000000000000060a05263d0e30db06000511415610168573460008112585761014052336101605261016051600060c052602060c02001546101405161016051600060c052602060c020015401116101405115176100e657600080fd5b6101405161016051600060c052602060c02001540161016051600060c052602060c020015560025461014051600254011161014051151761012657600080fd5b610140516002540160025561014051610180526101605160007fddf252ad1be2c89b69c2b068fc378daa952ba7f163c4a11628f55a4df523b3ef6020610180a3005b632e1a7d4d6000511415610260576020600461014037341561018957600080fd5b33610160526101405161016051600060c052602060c020015410156101ad57600080fd5b6101405161016051600060c052602060c02001540361016051600060c052602060c02001556101405160025410156101e457600080fd5b61014051600254036002556000600060006000600160605161014051806040519013585780919012585702610160516000f161021f57600080fd5b61014051610180526000610160517fddf252ad1be2c89b69c2b068fc378daa952ba7f163c4a11628f55a4df523b3ef6020610180a3600160005260206000f3005b6318160ddd600051141561028657341561027957600080fd5b60025460005260206000f3005b6370a0823160005114156102cd57602060046101403734156102a757600080fd5b60043560205181101558575061014051600060c052602060c020015460005260206000f3005b63a9059cbb60005114156103e057604060046101403734156102ee57600080fd5b60043560205181101558575033610180526101605161018051600060c052602060c0200154101561031e57600080fd5b6101605161018051600060c052602060c02001540361018051600060c052602060c020015561014051600060c052602060c02001546101605161014051600060c052602060c0200154011161016051151761037857600080fd5b6101605161014051600060c052602060c02001540161014051600060c052602060c0200155610160516101a05261014051610180517fddf252ad1be2c89b69c2b068fc378daa952ba7f163c4a11628f55a4df523b3ef60206101a0a3600160005260206000f3005b6323b872dd6000511415610559576060600461014037341561040157600080fd5b600435602051811015585750602435602051811015585750336101a0526101a05161014051600160c052602060c0200160c052602060c02001546101c0526101805161014051600060c052602060c0200154101561045e57600080fd5b6101805161014051600060c052602060c02001540361014051600060c052602060c020015561016051600060c052602060c02001546101805161016051600060c052602060c020015401116101805115176104b857600080fd5b6101805161016051600060c052602060c02001540161016051600060c052602060c0200155610180516101c05110156104f057600080fd5b610180516101c051036101a05161014051600160c052602060c0200160c052602060c0200155610180516101e05261016051610140517fddf252ad1be2c89b69c2b068fc378daa952ba7f163c4a11628f55a4df523b3ef60206101e0a3600160005260206000f3005b63095ea7b360005114156105ef576040600461014037341561057a57600080fd5b6004356020518110155857503361018052610160516101405161018051600160c052602060c0200160c052602060c0200155610160516101a05261014051610180517f8c5be1e5ebec7d5bd14f71427d1e84f3dd0314c0f7b2291e5b200ac8c7c3b92560206101a0a3600160005260206000f3005b63dd62ed3e600051141561064f576040600461014037341561061057600080fd5b6004356020518110155857506024356020518110155857506101605161014051600160c052602060c0200160c052602060c020015460005260206000f3005b"
              )
            </code>
            <storage>
              {STORAGE}
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
     {REQUIRES}

{EPILOGUE}

  // to avoid unnecessary case split
  rule <k> LT W0 W1 => bool2int(W0  <Int W1) ~> #push ... </k> [trusted]
  rule <k> GT W0 W1 => bool2int(W0  >Int W1) ~> #push ... </k> [trusted]
  rule <k> EQ W0 W1 => bool2int(W0 ==Int W1) ~> #push ... </k> [trusted]
  rule <k> ISZERO W => bool2int(W  ==Int 0 ) ~> #push ... </k> [trusted]

endmodule
```
