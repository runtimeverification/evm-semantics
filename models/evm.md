---
title: Maude Model of EVM
...



EVM Execution
=============

Local State
-----------

```maude
fmod EVM-LOCALSTATE is
    protecting INT .
    protecting NAT .

    sort Word .
    subsort Int < Word .
    sorts WordStack WordStack? .
    subsort WordStack < WordStack? .

    sorts Mem MemAddr MemRange .
    subsorts Nat < MemAddr .

    sort LocalState .
    sorts StackOp LocalOp .
    subsort StackOp < LocalOp .
```

### Word Stack Syntax

```maude
    op sgn : Int -> Int .
    ---------------------
    var I : Int .
    eq sgn(I) = if I < 0 then -1 else 1 fi .

    op .WordStack : -> WordStack [ctor] .
    op _:_        : Word    WordStack -> WordStack [ctor] .
    op _[_]       : StackOp WordStack -> WordStack? .

    --- stack operators (all of these decrease stack size)
    ops ADD MUL SUB EXP DIV MOD SDIV SMOD ADDMOD MULMOD SIGNEXTEND LT GT SLT SGT
        EQ ISZERO AND OR XOR NOT BYTE SHA3 POP : -> StackOp .
```

### Word Stack Semantics

```maude
    vars I0 I1 I2 : Int .
    vars V V'     : Word .
    var  VS       : WordStack .

    eq ADD [ I0 : I1 : VS ] = (I0 + I1) : VS .
    eq SUB [ I0 : I1 : VS ] = (I0 - I1) : VS .
    eq MUL [ I0 : I1 : VS ] = (I0 * I1) : VS .
    eq EXP [ I0 : I1 : VS ] = (I0 ^ I1) : VS .
    eq DIV [ I0 : I1 : VS ] = (if I1 == 0 then 0 else (I0 quo I1) fi) : VS .
    eq MOD [ I0 : I1 : VS ] = (if I1 == 0 then 0 else (I0 rem I1) fi) : VS .
    eq ADDMOD [ I0 : I1 : I2 : VS ] = (if I2 == 0 then 0 else (I0 + I1) rem I2 fi) : VS .
    eq MULMOD [ I0 : I1 : I2 : VS ] = (if I2 == 0 then 0 else (I0 * I1) rem I2 fi) : VS .

    --- eq SDIV [ I0 : I1 : VS ] = sdiv(I0,I1) : VS .
    --- eq SMOD [ I0 : I1 : VS ] = smod(I0,I1) : VS .
    --- eq SIGNEXTEND [ I0 : I1 : VS ] = signextend(I0,I1) : VS .

    eq LT     [ I0 : I1 : VS ] = (if I0 < I1 then 1 else 0 fi) : VS .
    eq GT     [ I0 : I1 : VS ] = (if I0 > I1 then 1 else 0 fi) : VS .
    --- eq SLT    [ I0 : I1 : VS ] = slt(I0,I1) : VS .
    --- eq SGT    [ I0 : I1 : VS ] = sgt(I0,I1) : VS .
    eq EQ     [ I0 : I1 : VS ] = (if I0 == I1 then 1 else 0 fi) : VS .
    eq ISZERO [ I0 : VS ]      = (if I0 == 0 then 1 else 0 fi) : VS .

    --- eq NOT [ I0 : VS ]      = not(I0)     : VS .
    --- eq OR  [ I0 : I1 : VS ] = or(I0, I1)  : VS .
    --- eq AND [ I0 : I1 : VS ] = and(I0, I1) : VS .
    --- eq XOR [ I0 : I1 : VS ] = xor(I0, I1) : VS .
    --- These are bit-wise operators.

    --- eq BYTE [ I0 : I1 : VS ] = byte(I0, I1) : VS .
    --- eq SHA3 [ I0 : I1 : VS ] = sha3(I0, I1) : VS .

    eq POP [ V : VS ] = VS .
```

### Local Memory Syntax

```maude
    op mt : -> Mem .
    op __ : Word Mem -> Mem [prec 40] .

    op _[_]    : Mem MemAddr -> Word .
    op _[_:=_] : Mem MemAddr Word -> Mem .

    op _:_     : MemAddr MemAddr -> MemRange .
    op _[_]    : Mem MemRange -> Mem .
    op _[_:=_] : Mem MemRange Mem -> Mem .
    --------------------------------------
    vars N N' : Nat .
    vars A A' : MemAddr .
    var  M    : Mem .
```

### Local Memory Semantics

```maude
    eq mt[A]             = 0 .
    eq (V M)[0]          = V .
    eq (V M)[s(N)]       = M[N] .
    eq (V M)[0 := V']    = V' M .
    eq (V M)[s(N) := V'] = V (M[N := V']) .

    ceq M[N : N']           = mt if N' <= N .
    eq  mt[0 : s(N')]       = 0 (mt[0 : N']) .
    eq  (V M)[0 : s(N')]    = V (M[0 : N']) .
    eq  (V M)[s(N) : s(N')] = M[N : N'] .
```

### Local State

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
