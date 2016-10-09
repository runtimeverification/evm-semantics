---
title: Maude Model of EVM
...



EVM Execution
=============

Local State
-----------

```maude
fmod EVM-LOCALSTATE is
    including NAT .

    sort Word .
    subsort Word < Nat .
    sorts WordStack WordStack? .
    subsort WordStack < WordStack? .

    sorts Mem MemAddr MemRange .
    subsorts Nat < MemAddr .

    sort LocalState .
    sorts StackOp LocalOp .
    subsort StackOp < LocalOp .
```

Local storage is in terms of words, which are wrapped at $2^256$.

```maude
    var N : Nat .
    ceq N = N rem (2 ^ 256) if N > (2 ^ 256) .
    cmb N : Word if N < (2 ^ 256) .
    --- this seems like an expensive membership check
```

### Word Stack

The local-stack is a word-addressed byte array, where stack operations happen at
the size of words. It is not to exceed 1024 in size.

```maude
    op .WordStack : -> WordStack [ctor] .
    op _:_        : Word    WordStack -> WordStack [ctor] .
    op _[_]       : StackOp WordStack -> WordStack .

    op stackSize : WordStack -> Nat .
    var W : Word . var WS : WordStack .
    -----------------------------------
    eq stackSize(.WordStack) = 0 .
    eq stackSize(W : WS)     = s(stackSize(WS)) .

    var WS? : WordStack? .
    ----------------------
    cmb WS? : WordStack if stackSize(WS?) <= 1024 .
```

All of these stack operators decrease the size of the stack, so they are safe
for the 1024 stack-size limit. Note that anything of sort `StackOp` *must* have
this property because of the defintion of `_[_] : StackOp WordStack -> WordStack`.

```maude
    ops ADD MUL SUB EXP DIV MOD SDIV SMOD ADDMOD MULMOD SIGNEXTEND LT GT SLT SGT
        EQ ISZERO AND OR XOR NOT BYTE SHA3 POP : -> StackOp .
```

Here we define the semantics of these operators over the local word stack.
Commented out semantic lines are not yet implemented, so we can't handle them.

```maude
    vars V0 V1 V2 : Word .
    var  VS       : WordStack .

    eq ADD [ V0 : V1 : VS ] = (V0 + V1) : VS .
    --- eq SUB [ V0 : V1 : VS ] = (V0 - V1) : VS .
    eq MUL [ V0 : V1 : VS ] = (V0 * V1) : VS .
    eq EXP [ V0 : V1 : VS ] = (V0 ^ V1) : VS .
    eq DIV [ V0 : V1 : VS ] = (if V1 == 0 then 0 else (V0 quo V1) fi) : VS .
    eq MOD [ V0 : V1 : VS ] = (if V1 == 0 then 0 else (V0 rem V1) fi) : VS .
    eq ADDMOD [ V0 : V1 : V2 : VS ] = (if V2 == 0 then 0 else (V0 + V1) rem V2 fi) : VS .
    eq MULMOD [ V0 : V1 : V2 : VS ] = (if V2 == 0 then 0 else (V0 * V1) rem V2 fi) : VS .

    --- eq SDIV [ V0 : V1 : VS ] = sdiv(V0,V1) : VS .
    --- eq SMOD [ V0 : V1 : VS ] = smod(V0,V1) : VS .
    --- eq SIGNEXTEND [ V0 : V1 : VS ] = signextend(V0,V1) : VS .

    eq LT     [ V0 : V1 : VS ] = (if V0 < V1 then 1 else 0 fi) : VS .
    eq GT     [ V0 : V1 : VS ] = (if V0 > V1 then 1 else 0 fi) : VS .
    --- eq SLT    [ V0 : V1 : VS ] = slt(V0,V1) : VS .
    --- eq SGT    [ V0 : V1 : VS ] = sgt(V0,V1) : VS .
    eq EQ     [ V0 : V1 : VS ] = (if V0 == V1 then 1 else 0 fi) : VS .
    eq ISZERO [ V0 : VS ]      = (if V0 == 0 then 1 else 0 fi) : VS .

    --- eq NOT [ V0 : VS ]      = not(V0)     : VS .
    --- eq OR  [ V0 : V1 : VS ] = or(V0, V1)  : VS .
    --- eq AND [ V0 : V1 : VS ] = and(V0, V1) : VS .
    --- eq XOR [ V0 : V1 : VS ] = xor(V0, V1) : VS .
    --- These are bit-wise operators.

    --- eq BYTE [ V0 : V1 : VS ] = byte(V0, V1) : VS .
    --- eq SHA3 [ V0 : V1 : VS ] = sha3(V0, V1) : VS .

    eq POP [ V0 : VS ] = VS .
```

### Local Memory

The local memory is an array of words. I am using a cons-list of words to
represent them, and have defined list-update and list-slice operators for
updating/accessing elements of the memory.

```maude
    op mt   : -> Mem .
    op __   : Word Mem -> Mem [prec 40] .
    -------------------------------------
    vars V V' : Word .
    vars A A' : Word .
    vars M M' : Mem .

    op _++_ : Mem Mem  -> Mem [prec 50] .
    -------------------------------------
    eq mt ++ M    = M .
    eq M ++ mt    = M .
    eq (V M) ++ M = V (M ++ M) .
```

The single-element memory read/update is defined here. Note that accessing a
single element of memory is linear in the address (ie. expensive).

```maude
    op _[_]    : Mem Word -> Word .
    op _[_:=_] : Mem Word Word -> Mem .
    -----------------------------------
    eq mt[A]             = 0 .
    eq (V M)[0]          = V .
    eq (V M)[s(A)]       = M[A] .
    eq (V M)[0 := V']    = V' M .
    eq (V M)[s(A) := V'] = V (M[A := V']) .
```

The list-slice access will take a chunk of the memory starting at the first
index (before the colon), and going until the element *before* the second index
(after the colon). It is linear in the ending address of the list. If the list
we're slicing from does not have enough elements, it is extended with zeros
implicitely.

```maude
    op drop : Word Mem -> Mem .
    op take : Word Mem -> Mem .
    ---------------------------
    eq drop(0, M)      = M .
    eq drop(A, mt)     = mt .
    eq drop(s(A), V M) = drop(A,M) .
    eq take(0, M)      = mt .
    eq take(s(A), mt)  = 0 take(A, mt) .
    eq take(s(A), V M) = V take(A, M) .

    op _.._    : Word Word -> MemRange .
    op _[_]    : Mem MemRange -> Mem .
    op _[_:=_] : Mem MemRange Mem -> Mem .
    --------------------------------------
    eq M[A .. A']       = if A < A' then take(sd(A,A'), drop(A,M)) else mt fi .
    eq M[A .. A' := M'] = if A < A' then take(A,M) ++ (take(sd(A,A'), M') ++ drop(A', M)) else M fi .
```

### Local State (Stack and Memory)

```maude
    op <_|_> : WordStack Mem -> LocalState .

    --- all of these decrease/leave-same stack size
    ops MLOAD MSTORE MSTORES SLOAD SSTORE
        : -> LocalOp .

    --- control flow
    ops JUMP JUMP1 JUMPDEST CREATE CALL CALLCODE RETURN DELEGATECALL SUICIDE
        : -> LocalOp .

    op _[_]  : LocalOp LocalState -> [LocalState] .

    --- Local State Semantics
    var SO : StackOp .
    eq SO [ < VS | M > ] = < SO [ VS ] | M > .


    --- all of these increase stack-size by 1
    op PUSH[_] : Nat -> LocalOp .
    op DUP[_]  : Nat -> LocalOp .
    op SWAP[_] : Nat -> LocalOp .
    --- PUSH[1-32], DUP[1-16], SWAP[1-16]
endfm
```

EVM State
---------

```maude
fmod EVM-STATE is
    protecting NAT .
    protecting EVM-LOCALSTATE .

    sort PC .
    subsort Nat < PC .
    sorts OpCode Program .
    subsort LocalOp < OpCode < Program .

    sorts CallID CallState CallFrame CallStack .

    op <_,_|_> : Program PC LocalState -> CallState .

    op pc : Nat -> PC .

    op <_|_> : CallID CallState -> CallFrame .

    op .CallStack : -> CallStack .
    op _:_        : CallFrame CallStack -> CallStack .
endfm

fmod EVM-EXEC is
    extending EVM-STATE .

    ops PC GAS GASLIMIT MSIZE 

    --- accessors
    ops ADDRESS BALANCE ORIGIN CALLER CALLVALUE CALLDATALOAD CALLDATASIZE
        CALLDATACOPY CODESIZE CODECOPY GASPRICE EXTCODESIZE EXTCODECOPY
        MSIZE BLOCKHASH COINBASE TIMESTAMP NUMBER DIFFICULTY GASLIMIT PC GAS
        : -> OpCode .

    op LOG[_]  : Nat -> OpCode .
    --- LOG[0-4]


    op skip : -> Program .
    op _:_  : Nat OpCode -> Program .
    op _;_  : Program Program -> Program [assoc comm id: skip] .
endfm
```


EVM Network
===========


```maude
fmod EVM-WORLD is
    protecting QID .
    protecting NAT .

    sorts Nonce Wei Hash .
    subsort Nat < Nonce .
    subsort Nat < Wei .
    subsort Nat < Hash .

    sorts AccountID AccountField .
    subsort Qid < AccountID .
    sorts Account Accounts .
    subsort Account < Accounts .

    op nonce[_]       : Nonce -> AccountField .
    op balance[_]     : Wei   -> AccountField .
    op storageRoot[_] : Hash  -> AccountField .
    op codeHash[_]    : Hash  -> AccountField .

    op __ : AccountField AccountField -> AccountField [assoc comm] .

    op _|->_ : AccountID AccountField -> Account .

    op mt  : -> Accounts .
    op _;_ : Accounts Accounts -> Accounts [assoc comm id: mt prec 60] .
endfm
```
