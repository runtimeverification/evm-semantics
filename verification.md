KEVM Verification
=================

Using K's reachability logic theorem prover, we're able to verify many properties about EVM programs as reachability claims.
This module defines some helpers which make writing specifications simpler.

```{.k .java}
requires "evm.k"

module VERIFICATION
    imports EVM
```

This `smt-lemma` helps Z3 reason about stack over/under flow.

```{.k .java}
    rule #sizeWordStack ( _ , _ ) >=Int 0 => true [smt-lemma]
    rule #sizeWordStack ( WS , N:Int )
      => #sizeWordStack ( WS , 0 ) +Int N
      requires N =/=K 0
      [lemma]
```

Sum to N
--------

As a demonstration of simple reachability claims involing a circularity, we prove the EVM [Sum to N](proofs/sum-to-n.md) program correct.
This program sums the numbers from 1 to N (for sufficiently small N), including pre-conditions dis-allowing integer under/overflow and stack overflow.

```{.k .java}
    syntax Map ::= "sumTo" "(" Int ")" [function]
 // ---------------------------------------------
    rule sumTo(N)
      => #asMapOpCodes( PUSH(1, 0) ; PUSH(32, N)                // s = 0 ; n = N
                      ; JUMPDEST                                // label:loop
                      ; DUP(1) ; ISZERO ; PUSH(1, 52) ; JUMPI   // if n == 0, jump to end
                      ; DUP(1) ; SWAP(2) ; ADD                  // s = s + n
                      ; SWAP(1) ; PUSH(1, 1) ; SWAP(1) ; SUB    // n = n - 1
                      ; PUSH(1, 35) ; JUMP                      // jump to loop
                      ; JUMPDEST                                // label:end
                      ; .OpCodes
                      ) [macro]
```

Hacker Gold (HKG) Token Smart Contract
--------------------------------------

Several proofs about the [HKG Token functions](proofs/hkg.md) have been performed.
These helper constants make writing the proof claims simpler/cleaner.

```{.k .java}
    syntax Int ::= "%ACCT_1_BALANCE" [function]
                 | "%ACCT_2_BALANCE" [function]
                 | "%ACCT_1_ALLOWED" [function]
                 | "%ACCT_2_ALLOWED" [function]
                 | "%ACCT_ID"        [function]
                 | "%CALLER_ID"      [function]
                 | "%ORIGIN_ID"      [function]
                 | "%COINBASE_VALUE" [function]

    rule %ACCT_1_ALLOWED => 90140393717854041204577419487481777019768054268415728047989462811209962694062 [macro]
    rule %ACCT_2_BALANCE => 7523342389551220067180060596052511116626922476768911452708464109912271601147  [macro]
    rule %ACCT_1_BALANCE => 73276140668783822097736045772311176946506324369098798920944620499663575949472 [macro]
    rule %ACCT_2_ALLOWED => 89883370637028415006891042932604780869171597379948077832163656920795299088269 [macro]
    rule %ACCT_ID        => 87579061662017136990230301793909925042452127430                               [macro]
    rule %CALLER_ID      => 428365927726247537526132020791190998556166378203                              [macro]
    rule %ORIGIN_ID      => 116727156174188091019688739584752390716576765452                              [macro]
    rule %COINBASE_VALUE => 244687034288125203496486448490407391986876152250                              [macro]
    syntax WordStack ::= "%HKG_ProgramBytes"       [function]
                       | "%HKG_ProgramBytes_buggy" [function]
    syntax Map ::= "%HKG_Program"       [function]
                 | "%HKG_Program_buggy" [function]

    rule %HKG_ProgramBytes       => #parseByteStack("0x60606040526000357c0100000000000000000000000000000000000000000000000000000000900463ffffffff168063095ea7b31461006757806323b872dd146100be57806370a0823114610134578063a9059cbb1461017e578063dd62ed3e146101d5575bfe5b341561006f57fe5b6100a4600480803573ffffffffffffffffffffffffffffffffffffffff1690602001909190803590602001909190505061023e565b604051808215151515815260200191505060405180910390f35b34156100c657fe5b61011a600480803573ffffffffffffffffffffffffffffffffffffffff1690602001909190803573ffffffffffffffffffffffffffffffffffffffff16906020019091908035906020019091905050610331565b604051808215151515815260200191505060405180910390f35b341561013c57fe5b610168600480803573ffffffffffffffffffffffffffffffffffffffff169060200190919050506105b2565b6040518082815260200191505060405180910390f35b341561018657fe5b6101bb600480803573ffffffffffffffffffffffffffffffffffffffff169060200190919080359060200190919050506105fc565b604051808215151515815260200191505060405180910390f35b34156101dd57fe5b610228600480803573ffffffffffffffffffffffffffffffffffffffff1690602001909190803573ffffffffffffffffffffffffffffffffffffffff1690602001909190505061076a565b6040518082815260200191505060405180910390f35b600081600260003373ffffffffffffffffffffffffffffffffffffffff1673ffffffffffffffffffffffffffffffffffffffff16815260200190815260200160002060008573ffffffffffffffffffffffffffffffffffffffff1673ffffffffffffffffffffffffffffffffffffffff168152602001908152602001600020819055508273ffffffffffffffffffffffffffffffffffffffff163373ffffffffffffffffffffffffffffffffffffffff167f8c5be1e5ebec7d5bd14f71427d1e84f3dd0314c0f7b2291e5b200ac8c7c3b925846040518082815260200191505060405180910390a3600190505b92915050565b600081600160008673ffffffffffffffffffffffffffffffffffffffff1673ffffffffffffffffffffffffffffffffffffffff16815260200190815260200160002054101580156103fe575081600260008673ffffffffffffffffffffffffffffffffffffffff1673ffffffffffffffffffffffffffffffffffffffff16815260200190815260200160002060003373ffffffffffffffffffffffffffffffffffffffff1673ffffffffffffffffffffffffffffffffffffffff1681526020019081526020016000205410155b801561040a5750600082115b156105a15781600160008673ffffffffffffffffffffffffffffffffffffffff1673ffffffffffffffffffffffffffffffffffffffff1681526020019081526020016000206000828254039250508190555081600160008573ffffffffffffffffffffffffffffffffffffffff1673ffffffffffffffffffffffffffffffffffffffff1681526020019081526020016000206000828254019250508190555081600260008673ffffffffffffffffffffffffffffffffffffffff1673ffffffffffffffffffffffffffffffffffffffff16815260200190815260200160002060003373ffffffffffffffffffffffffffffffffffffffff1673ffffffffffffffffffffffffffffffffffffffff168152602001908152602001600020600082825403925050819055508273ffffffffffffffffffffffffffffffffffffffff168473ffffffffffffffffffffffffffffffffffffffff167fddf252ad1be2c89b69c2b068fc378daa952ba7f163c4a11628f55a4df523b3ef846040518082815260200191505060405180910390a3600190506105ab565b600090506105ab565b5b9392505050565b6000600160008373ffffffffffffffffffffffffffffffffffffffff1673ffffffffffffffffffffffffffffffffffffffff1681526020019081526020016000205490505b919050565b600081600160003373ffffffffffffffffffffffffffffffffffffffff1673ffffffffffffffffffffffffffffffffffffffff168152602001908152602001600020541015801561064d5750600082115b1561075a5781600160003373ffffffffffffffffffffffffffffffffffffffff1673ffffffffffffffffffffffffffffffffffffffff1681526020019081526020016000206000828254039250508190555081600160008573ffffffffffffffffffffffffffffffffffffffff1673ffffffffffffffffffffffffffffffffffffffff168152602001908152602001600020600082825401925050819055508273ffffffffffffffffffffffffffffffffffffffff163373ffffffffffffffffffffffffffffffffffffffff167fddf252ad1be2c89b69c2b068fc378daa952ba7f163c4a11628f55a4df523b3ef846040518082815260200191505060405180910390a360019050610764565b60009050610764565b5b92915050565b6000600260008473ffffffffffffffffffffffffffffffffffffffff1673ffffffffffffffffffffffffffffffffffffffff16815260200190815260200160002060008373ffffffffffffffffffffffffffffffffffffffff1673ffffffffffffffffffffffffffffffffffffffff1681526020019081526020016000205490505b929150505600a165627a7a72305820955d4848f79dc023af4f6c233535c5c8d39532ebe7e7b64adbd933112556edf30029")                 [macro]
    rule %HKG_ProgramBytes_buggy => #parseByteStack("60606040526000357c0100000000000000000000000000000000000000000000000000000000900463ffffffff168063095ea7b31461006a57806323b872dd146100c457806370a082311461013d578063a9059cbb1461018a578063dd62ed3e146101e4575b600080fd5b341561007557600080fd5b6100aa600480803573ffffffffffffffffffffffffffffffffffffffff16906020019091908035906020019091905050610250565b604051808215151515815260200191505060405180910390f35b34156100cf57600080fd5b610123600480803573ffffffffffffffffffffffffffffffffffffffff1690602001909190803573ffffffffffffffffffffffffffffffffffffffff16906020019091908035906020019091905050610343565b604051808215151515815260200191505060405180910390f35b341561014857600080fd5b610174600480803573ffffffffffffffffffffffffffffffffffffffff169060200190919050506105c4565b6040518082815260200191505060405180910390f35b341561019557600080fd5b6101ca600480803573ffffffffffffffffffffffffffffffffffffffff1690602001909190803590602001909190505061060e565b604051808215151515815260200191505060405180910390f35b34156101ef57600080fd5b61023a600480803573ffffffffffffffffffffffffffffffffffffffff1690602001909190803573ffffffffffffffffffffffffffffffffffffffff16906020019091905050610773565b6040518082815260200191505060405180910390f35b600081600260003373ffffffffffffffffffffffffffffffffffffffff1673ffffffffffffffffffffffffffffffffffffffff16815260200190815260200160002060008573ffffffffffffffffffffffffffffffffffffffff1673ffffffffffffffffffffffffffffffffffffffff168152602001908152602001600020819055508273ffffffffffffffffffffffffffffffffffffffff163373ffffffffffffffffffffffffffffffffffffffff167f8c5be1e5ebec7d5bd14f71427d1e84f3dd0314c0f7b2291e5b200ac8c7c3b925846040518082815260200191505060405180910390a3600190505b92915050565b600081600160008673ffffffffffffffffffffffffffffffffffffffff1673ffffffffffffffffffffffffffffffffffffffff1681526020019081526020016000205410158015610410575081600260008673ffffffffffffffffffffffffffffffffffffffff1673ffffffffffffffffffffffffffffffffffffffff16815260200190815260200160002060003373ffffffffffffffffffffffffffffffffffffffff1673ffffffffffffffffffffffffffffffffffffffff1681526020019081526020016000205410155b801561041c5750600082115b156105b35781600160008673ffffffffffffffffffffffffffffffffffffffff1673ffffffffffffffffffffffffffffffffffffffff1681526020019081526020016000206000828254039250508190555081600160008573ffffffffffffffffffffffffffffffffffffffff1673ffffffffffffffffffffffffffffffffffffffff1681526020019081526020016000206000828254019250508190555081600260008673ffffffffffffffffffffffffffffffffffffffff1673ffffffffffffffffffffffffffffffffffffffff16815260200190815260200160002060003373ffffffffffffffffffffffffffffffffffffffff1673ffffffffffffffffffffffffffffffffffffffff168152602001908152602001600020600082825403925050819055508273ffffffffffffffffffffffffffffffffffffffff168473ffffffffffffffffffffffffffffffffffffffff167fddf252ad1be2c89b69c2b068fc378daa952ba7f163c4a11628f55a4df523b3ef846040518082815260200191505060405180910390a3600190506105bd565b600090506105bd565b5b9392505050565b6000600160008373ffffffffffffffffffffffffffffffffffffffff1673ffffffffffffffffffffffffffffffffffffffff1681526020019081526020016000205490505b919050565b600081600160003373ffffffffffffffffffffffffffffffffffffffff1673ffffffffffffffffffffffffffffffffffffffff168152602001908152602001600020541015801561065f5750600082115b156107635781600160003373ffffffffffffffffffffffffffffffffffffffff1673ffffffffffffffffffffffffffffffffffffffff1681526020019081526020016000206000828254039250508190555081600160008573ffffffffffffffffffffffffffffffffffffffff1673ffffffffffffffffffffffffffffffffffffffff168152602001908152602001600020819055508273ffffffffffffffffffffffffffffffffffffffff163373ffffffffffffffffffffffffffffffffffffffff167fddf252ad1be2c89b69c2b068fc378daa952ba7f163c4a11628f55a4df523b3ef846040518082815260200191505060405180910390a36001905061076d565b6000905061076d565b5b92915050565b6000600260008473ffffffffffffffffffffffffffffffffffffffff1673ffffffffffffffffffffffffffffffffffffffff16815260200190815260200160002060008373ffffffffffffffffffffffffffffffffffffffff1673ffffffffffffffffffffffffffffffffffffffff1681526020019081526020016000205490505b929150505600a165627a7a7230582093e640afb442869193a08cf82ed9577e403c7c53a6a95f589e2b673195da102e0029") [macro]
    rule %HKG_Program => #asMapOpCodes(#dasmOpCodes(%HKG_ProgramBytes, DEFAULT))
    rule %HKG_Program_buggy => #asMapOpCodes(#dasmOpCodes(%HKG_ProgramBytes_buggy, DEFAULT))
```

Reasoning Simplifications
-------------------------

We design abstractions that capture the EVM low-level specific details, allowing to specify specifications and reason about properties in a higher level similar to that of the surface languages (e.g., Solidity or Viper) in which smart contracts are written.

### Memory Abstraction

We present an abstraction for the EVM memory to allow the word-level reasoning.
The word is considered as the smallest unit of values in the surface language level (thus in the contract developers’ mind as well), but the EVM memory is byte-addressable.
Our abstraction helps to fill the gap and make the reasoning easier.

Specifically, we introduce uninterpreted function abstractions and refinements for the word-level reasoning.

The term `nthbyteof(v, i, n)` represents the i-th byte of the two's complement representation of v in n bytes (0 being MSB), with discarding high-order bytes when v is not fit in n bytes.

```{.k .java}
    syntax Int ::= nthbyteof ( Int , Int , Int ) [function, smtlib(smt_nthbyteof)]
 // ------------------------------------------------------------------------------
    rule nthbyteof(V, I, N) => nthbyteof(V /Int 256, I, N -Int 1) when N  >Int (I +Int 1) [concrete]
    rule nthbyteof(V, I, N) =>           V modInt 256             when N ==Int (I +Int 1) [concrete]
```

However, we'd like to keep it uninterpreted, if the arguments are symbolic, to avoid the non-linear arithmetic reasoning, which even the state-of-the-art theorem provers cannot handle very well.
Instead, we introduce lemmas over the uninterpreted functional terms.

The following lemmas are used for symbolic reasoning about `MLOAD` and `MSTORE` instructions.
They capture the essential mechanisms used by the two instructions: splitting a word into the byte-array and merging it back to the word.

```{.k .java}
    rule 0 <=Int nthbyteof(V, I, N)          => true
    rule         nthbyteof(V, I, N) <Int 256 => true

    rule #asWord( nthbyteof(V,  0, 32)
                : nthbyteof(V,  1, 32)
                : nthbyteof(V,  2, 32)
                : nthbyteof(V,  3, 32)
                : nthbyteof(V,  4, 32)
                : nthbyteof(V,  5, 32)
                : nthbyteof(V,  6, 32)
                : nthbyteof(V,  7, 32)
                : nthbyteof(V,  8, 32)
                : nthbyteof(V,  9, 32)
                : nthbyteof(V, 10, 32)
                : nthbyteof(V, 11, 32)
                : nthbyteof(V, 12, 32)
                : nthbyteof(V, 13, 32)
                : nthbyteof(V, 14, 32)
                : nthbyteof(V, 15, 32)
                : nthbyteof(V, 16, 32)
                : nthbyteof(V, 17, 32)
                : nthbyteof(V, 18, 32)
                : nthbyteof(V, 19, 32)
                : nthbyteof(V, 20, 32)
                : nthbyteof(V, 21, 32)
                : nthbyteof(V, 22, 32)
                : nthbyteof(V, 23, 32)
                : nthbyteof(V, 24, 32)
                : nthbyteof(V, 25, 32)
                : nthbyteof(V, 26, 32)
                : nthbyteof(V, 27, 32)
                : nthbyteof(V, 28, 32)
                : nthbyteof(V, 29, 32)
                : nthbyteof(V, 30, 32)
                : nthbyteof(V, 31, 32)
                : .WordStack ) => V
      requires 0 <=Int V andBool V <Int pow256
```

Another type of byte-array manipulating operation is used to extract the function signature from the call data.
The function signature is located in the first four bytes of the call data, but there is no atomic EVM instruction that can load only the four bytes, thus some kind of byte-twiddling operations are necessary.

The extraction mechanism varies by language compilers.
For example, in Viper, the first 32 bytes of the call data are loaded into the memory at the starting location 28 (i.e., in the memory range of 28 to 59), and the memory range of 0 to 31, which consists of 28 zero bytes and the four signature bytes, is loaded into the stack.
In Solidity, however, the first 32 bytes of the call data are loaded into the stack, and the loaded word (i.e., a 256-bit integer) is divided by `2^(28*8)` (i.e., left-shifted by 28 bytes), followed by masked by 0xffffffff (i.e., 4 bytes of bit 1’s).

The following lemmas essentially capture the signature extraction mechanisms.
It reduces the reasoning efforts of the underlying theorem prover, factoring out the essence of the byte-twiddling operations.

```{.k .java}
    rule #padToWidth(32, #asByteStack(V)) => #asByteStackInWidth(V, 32)
      requires 0 <=Int V andBool V <Int pow256

    // for Viper
    rule #padToWidth(N, #asByteStack(#asWord(WS))) => WS
      requires #noOverflow(WS) andBool N ==Int #sizeWordStack(WS)

    // for Solidity
    rule #asWord(WS) /Int D => #asWord(#take(#sizeWordStack(WS) -Int log256Int(D), WS))
      requires D modInt 256 ==Int 0 andBool D >=Int 0
       andBool #sizeWordStack(WS) >=Int log256Int(D)
       andBool #noOverflow(WS)

    syntax Bool ::= #noOverflow    ( WordStack ) [function]
                  | #noOverflowAux ( WordStack ) [function]
 // -------------------------------------------------------
    rule #noOverflow(WS) => #sizeWordStack(WS) <=Int 32 andBool #noOverflowAux(WS)

    rule #noOverflowAux(W : WS)     => 0 <=Int W andBool W <Int 256 andBool #noOverflowAux(WS)
    rule #noOverflowAux(.WordStack) => true

    syntax WordStack ::= #asByteStackInWidth    ( Int, Int )                 [function]
                       | #asByteStackInWidthaux ( Int, Int, Int, WordStack ) [function]
 // -----------------------------------------------------------------------------------
    rule #asByteStackInWidth(X, N) => #asByteStackInWidthaux(X, N -Int 1, N, .WordStack)

    rule #asByteStackInWidthaux(X, I, N, WS) => #asByteStackInWidthaux(X, I -Int 1, N, nthbyteof(X, I, N) : WS) when I >Int 0
    rule #asByteStackInWidthaux(X, 0, N, WS) => nthbyteof(X, 0, N) : WS
```

### Abstraction for Hash

We do not model the hash function as an injective function simply because it is not true due to the pigeonhole principle.
Instead, we abstract it as an uninterpreted function that captures the possibility of the hash collision, even if the probability is very small.

However, one can avoid reasoning about the potential collision by assuming all of the hashed values appearing in each execution trace are collision-free.
This can be achieved by instantiating the injectivity property only for the terms appearing in the symbolic execution, in a way analogous to the universal quantifier instantiation.
Hashed locations are essential for the storage layout schemes used to store compound data structures such as maps in the storage.

The following syntactic sugars capture the storage layout schemes of Solidity and Viper.

```{.k .java}
    syntax IntList ::= List{Int, ""}                             [klabel(intList)]
    syntax Int     ::= #hashedLocation( String , Int , IntList ) [function]
 // -----------------------------------------------------------------------
    rule #hashedLocation(LANG, BASE, .IntList) => BASE

    rule #hashedLocation("Viper",    BASE, OFFSET OFFSETS) => #hashedLocation("Viper",    keccakIntList(BASE) +Word OFFSET, OFFSETS)
    rule #hashedLocation("Solidity", BASE, OFFSET OFFSETS) => #hashedLocation("Solidity", keccakIntList(OFFSET BASE),       OFFSETS)

    syntax Int ::= keccakIntList( IntList ) [function]
 // --------------------------------------------------
    rule keccakIntList(VS) => keccak(intList2ByteStack(VS))

    syntax WordStack ::= intList2ByteStack( IntList ) [function]
 // ------------------------------------------------------------
    rule intList2ByteStack(.IntList) => .WordStack
    rule intList2ByteStack(V VS)     => #asByteStackInWidth(V, 32) ++ intList2ByteStack(VS)
      requires 0 <=Int V andBool V <Int pow256
```

### Integer Expression Simplification Rules

We introduce simplification rules that capture arithmetic properties, which reduce the given terms into smaller ones.
These rules help to improve the performance of the underlying theorem prover’s symbolic reasoning.

Below are universal simplification rules that are free to be used in any context.

```{.k .java}
    rule 0 +Int N => N
    rule N +Int 0 => N

    rule N -Int 0 => N

    rule 1 *Int N => N
    rule N *Int 1 => N
    rule 0 *Int _ => 0
    rule _ *Int 0 => 0

    rule N /Int 1 => N

    rule 0 |Int N => N
    rule N |Int 0 => N
    rule N |Int N => N

    rule 0 &Int N => 0
    rule N &Int 0 => 0
    rule N &Int N => N
```

The following simplification rules are local, meant to be used in specific contexts.
The rules are applied only when the side-conditions are met.
These rules are specific to reasoning about EVM programs.

```{.k .java}
    rule (I1 +Int I2) +Int I3 => I1 +Int (I2 +Int I3) when #isConcrete(I2) andBool #isConcrete(I3)
    rule (I1 +Int I2) -Int I3 => I1 +Int (I2 -Int I3) when #isConcrete(I2) andBool #isConcrete(I3)
    rule (I1 -Int I2) +Int I3 => I1 -Int (I2 -Int I3) when #isConcrete(I2) andBool #isConcrete(I3)
    rule (I1 -Int I2) -Int I3 => I1 -Int (I2 +Int I3) when #isConcrete(I2) andBool #isConcrete(I3)

    rule I1 &Int (I2 &Int I3) => (I1 &Int I2) &Int I3 when #isConcrete(I1) andBool #isConcrete(I2)

    // 0xffff...f &Int N = N
    rule MASK &Int N => N  requires MASK ==Int (2 ^Int (log2Int(MASK) +Int 1)) -Int 1 // MASK = 0xffff...f
                            andBool 0 <=Int N andBool N <=Int MASK

    // for gas calculation
    rule A -Int (#ifInt C #then B1 #else B2 #fi) => #ifInt C #then (A -Int B1) #else (A -Int B2) #fi
    rule (#ifInt C #then B1 #else B2 #fi) -Int A => #ifInt C #then (B1 -Int A) #else (B2 -Int A) #fi
```

### Boolean

In EVM, no boolean value exist but instead, 1 and 0 are used to represent true and false respectively.

We introduce an abstraction for that, bool2int, as an uninterpreted function, and provide lemmas over it.

```{.k .java}
    syntax Int ::= bool2int( Bool ) [function] // [smtlib(smt_bool2int)]
 // --------------------------------------------------------------------
    rule bool2int(B) => 1 requires B
    rule bool2int(B) => 0 requires notBool(B)

    rule bool2int(A) |Int bool2int(B) => bool2int(A  orBool B)
    rule bool2int(A) &Int bool2int(B) => bool2int(A andBool B)

    rule bool2int(A)  ==K 0 => notBool(A)
    rule bool2int(A)  ==K 1 => A
    rule bool2int(A) =/=K 0 => A
    rule bool2int(A) =/=K 1 => notBool(A)

    rule chop(bool2int(B)) => bool2int(B)
```

Some lemmas over the comparison operators are also provided.

```{.k .java}
    rule 0 <=Int chop(V)             => true
    rule         chop(V) <Int pow256 => true

    rule 0 <=Int keccak(V)             => true
    rule         keccak(V) <Int pow256 => true

    rule 0 <=Int X &Int Y             => true requires 0 <=Int X andBool X <Int pow256 andBool 0 <=Int Y andBool Y <Int pow256
    rule         X &Int Y <Int pow256 => true requires 0 <=Int X andBool X <Int pow256 andBool 0 <=Int Y andBool Y <Int pow256
endmodule
```
