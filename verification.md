KEVM Verification
=================

Using K's reachability logic theorem prover, we're able to verify many properties about EVM programs as reachability claims. Safety properties (and some of the liveness properties) can be naturally specified in the reachability claims. Liveness properties can be specified by using the reduction to safety properties, while some of the liveness properties can be directly specified in the reachability claims as well.

This module defines some helpers which make writing specifications simpler.

```{.k .java}
requires "evm.k"

module VERIFICATION
    imports EVM
```

Abstractions
------------

We design abstractions that capture the EVM low-level specific details, allowing to specify specifications and reason about properties in a higher level similar to that of the surface languages (e.g., Solidity or Viper) in which smart contracts are written.

### Memory Abstraction

We present an abstraction for the EVM memory to allow the word-level reasoning. The word is considered as the smallest unit of values in the surface language level (thus in the contract developers’ mind as well), but the EVM memory is byte-addressable. Our abstraction helps to fill the gap and make the reasoning easier.

Specifically, we introduce uninterpreted function abstractions and refinements for the word-level reasoning.

The term `nthbyteof(v, i, n)` represents the i-th byte of the two's complement representation of v in n bytes (0 being MSB), with discarding high-order bytes when v is not fit in n bytes.

```{.k .java}
  syntax Int ::= nthbyteof(Int, Int, Int) [function, smtlib(smt_nthbyteof)]
```

Precisely it is defined as follows.

```{.k .java}
  rule nthbyteof(V, I, N) => nthbyteof(V /Int 256, I, N -Int 1) when N  >Int (I +Int 1) [concrete]
  rule nthbyteof(V, I, N) =>           V %Int 256               when N ==Int (I +Int 1) [concrete]
```

However, we'd like to keep it uninterpreted, if the arguments are symbolic, to avoid the non-linear arithmetic reasoning, which even the state-of-the-art theorem provers cannot handle very well.

Instead, we introduce lemmas over the uninterpreted functional terms.

The following lemmas are used for symbolic reasoning about MLOAD and MSTORE instructions. They capture the essential mechanisms used by the two instructions: splitting a word into the byte-array and merging it back to the word.

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
    requires 0 <=Int V andBool V <Int (2 ^Int 256)

  rule #padToWidth(32, #asByteStack(V)) => #asByteStackInWidth(V, 32)
    requires 0 <=Int V andBool V <Int (2 ^Int 256)

  // syntactic sugar
  syntax WordStack ::= #asByteStackInWidth(Int, Int) [function]
                     | #asByteStackInWidthaux(Int, Int, Int, WordStack) [function]
  rule #asByteStackInWidth(X, N) => #asByteStackInWidthaux(X, N -Int 1, N, .WordStack)
  rule #asByteStackInWidthaux(X, I, N, WS) => #asByteStackInWidthaux(X, I -Int 1, N, nthbyteof(X, I, N) : WS) when I >Int 0
  rule #asByteStackInWidthaux(X, 0, N, WS) => nthbyteof(X, 0, N) : WS
```

Another type of byte-array manipulating operation is used to extract the function signature from the call data. The function signature is located in the first four bytes of the call data, but there is no atomic EVM instruction that can load only the four bytes, thus some kind of byte-twiddling operations are necessary.

The extraction mechanism varies by language compilers. For example, in Viper, the first 32 bytes of the call data are loaded into the memory at the starting location 28 (i.e., in the memory range of 28 to 59), and the memory range of 0 to 31, which consists of 28 zero bytes and the four signature bytes, is loaded into the stack. In Solidity, however, the first 32 bytes of the call data are loaded into the stack, and the loaded word (i.e., a 256-bit integer) is divided by `2^(28*8)` (i.e., left-shifted by 28 bytes), followed by masked by 0xffffffff (i.e., 4 bytes of bit 1’s).

The following lemmas essentially capture the signature extraction mechanisms. It reduces the reasoning efforts of the underlying theorem prover, factoring out the essence of the byte-twiddling operations.

```{.k .java}
  // for viper
  rule #padToWidth(N, #asByteStack(#asWord(WS))) => WS
    requires noOverflow(WS) andBool N ==Int #sizeWordStack(WS)

  // for solidity
  rule #asWord(WS) /Int D => #asWord(#take(#sizeWordStack(WS) -Int log256Int(D), WS))
    requires D %Int 256 ==Int 0 andBool D >=Int 0
     andBool #sizeWordStack(WS) >=Int log256Int(D)
     andBool noOverflow(WS)

  // syntactic sugar
  syntax Bool ::= noOverflow(WordStack)    [function]
                | noOverflowAux(WordStack) [function]
  rule noOverflow(WS) => #sizeWordStack(WS) <=Int 32 andBool noOverflowAux(WS)
  rule noOverflowAux(W : WS) => 0 <=Int W andBool W <Int 256 andBool noOverflowAux(WS)
  rule noOverflowAux(.WordStack) => true
```

### Abstraction for Hash

We do not model the hash function as an injective function simply because it is not true due to the pigeonhole principle.

Instead, we abstract it as an uninterpreted function that captures the possibility of the hash collision, even if the probability is very small.

```
  syntax Int ::= keccak ( WordStack ) [function, smtlib(smt_keccak)]
```

However, one can avoid reasoning about the potential collision by assuming all of the hashed values appearing in each execution trace are collision-free. This can be achieved by instantiating the injectivity property only for the terms appearing in the symbolic execution, in a way analogous to the universal quantifier instantiation.

#### Hashed Locations

Hashed locations are essential for the storage layout schemes used to store compound data structures such as maps in the storage. For more details, refer to [EVM-Specific EVM Specification](proofs/erc20.md#storage).

The following syntactic sugars capture the storage layout schemes of Solidity and Viper.

```{.k .java}

  syntax IntList ::= List{Int, ""} [klabel(intList)]

  syntax Int ::= #hashedLocation(String, Int, IntList) [function]
  rule #hashedLocation(LANG, BASE, .IntList) => BASE
  //
  rule #hashedLocation("Viper",    BASE, OFFSET OFFSETS) => #hashedLocation("Viper",    keccakIntList(BASE) +Word OFFSET, OFFSETS)
  rule #hashedLocation("Solidity", BASE, OFFSET OFFSETS) => #hashedLocation("Solidity", keccakIntList(OFFSET BASE),       OFFSETS)

  syntax Int ::= keccakIntList(IntList) [function]
  rule keccakIntList(VS) => keccak(intList2ByteStack(VS))

  syntax WordStack ::= intList2ByteStack(IntList) [function]
  rule intList2ByteStack(.IntList) => .WordStack
  rule intList2ByteStack(V VS) => #asByteStackInWidth(V, 32) ++ intList2ByteStack(VS)
    requires 0 <=Int V andBool V <Int (2 ^Int 256)
```

### Arithmetic Simplification Rules

We introduce simplification rules that capture arithmetic properties, which reduce the given terms into smaller ones. These rules help to improve the performance of the underlying theorem prover’s symbolic reasoning.

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

The following simplification rules are local, meant to be used in specific contexts. The rules are applied only when the side-conditions are met.

These rules are specific to reasoning about EVM programs.

```{.k .java}
  syntax Bool ::= #isConcrete(K) [function, hook(KREFLECTION.isConcrete)]

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
  syntax Int ::= bool2int(Bool) [function] // [smtlib(smt_bool2int)]
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

### Modulo Reduction

Below are simple lemmas for the modulo reduction.

```{.k .java}
  // TODO: change semantics
  rule chop(I) => I modInt /* pow256 */ 115792089237316195423570985008687907853269984665640564039457584007913129639936 [concrete, smt-lemma]

  rule 0 <=Int chop(V)                     => true
  rule         chop(V) <Int /* 2 ^Int 256 */ 115792089237316195423570985008687907853269984665640564039457584007913129639936 => true

  rule 0 <=Int keccak(V)                     => true
  rule         keccak(V) <Int /* 2 ^Int 256 */ 115792089237316195423570985008687907853269984665640564039457584007913129639936 => true

  rule 0 <=Int X &Int Y                     => true     requires 0 <=Int X andBool X <Int (2 ^Int 256) andBool 0 <=Int Y andBool Y <Int (2 ^Int 256)
  rule         X &Int Y <Int /* 2 ^Int 256 */ 115792089237316195423570985008687907853269984665640564039457584007913129639936 => true
                                                        requires 0 <=Int X andBool X <Int (2 ^Int 256) andBool 0 <=Int Y andBool Y <Int (2 ^Int 256)
```

### Wordstack

These lemma abstracts some properties about `#sizeWordStack`:

```{.k .java}
rule #sizeWordStack ( _ , _ ) >=Int 0 => true [smt-lemma]
rule #sizeWordStack ( WS , N:Int )
  => #sizeWordStack ( WS , 0 ) +Int N
  requires N =/=K 0
  [lemma]
```

ABI Calls
---------

Below is the ABI call abstraction, a formalization for ABI encoding of the call data, that helps to keep the specification succinct.

```{.k .java}
    syntax TypedArg ::= "#uint160"      "(" Int ")"
                      | "#address"      "(" Int ")"
                      | "#uint256"      "(" Int ")"

    syntax TypedArgs ::= List{TypedArg, ","}                [klabel(typedArgs)]

    syntax WordStack ::= #abiCallData( String , TypedArgs ) [function]
    rule #abiCallData( FNAME , ARGS )
      => #parseByteStack(substrString(Keccak256(#generateSignature(FNAME, ARGS)), 0, 8))
      ++ #encodeArgs(ARGS)

    syntax String ::= #generateSignature        ( String, TypedArgs)    [function]
                    | #generateSignatureAux     ( String, TypedArgs)    [function]
    rule #generateSignature( FNAME , ARGS ) => #generateSignatureAux(FNAME +String "(", ARGS)
    //
    rule #generateSignatureAux(SIGN, TARGA, TARGB, TARGS)  => #generateSignatureAux(SIGN +String #typeName(TARGA) +String ",", TARGB, TARGS)
    rule #generateSignatureAux(SIGN, TARG, .TypedArgs)     => #generateSignatureAux(SIGN +String #typeName(TARG), .TypedArgs)
    rule #generateSignatureAux(SIGN, .TypedArgs)           => SIGN +String ")"

    syntax String ::= #typeName ( TypedArg ) [function]
    rule #typeName(#uint160( _ ))  => "uint160"
    rule #typeName(#address( _ ))  => "address"
    rule #typeName(#uint256( _ ))  => "uint256"

    syntax WordStack ::= "#encodeArgs" "(" TypedArgs ")" [function]
    rule #encodeArgs(ARG, ARGS)    => #getData(ARG) ++ #encodeArgs(ARGS)
    rule #encodeArgs(.TypedArgs)   => .WordStack

    syntax WordStack ::= "#getData" "(" TypedArg ")" [function]
    rule #getData(#uint160( DATA )) => #asByteStackInWidth( DATA , 32 )
    rule #getData(#address( DATA )) => #asByteStackInWidth( DATA , 32 )
    rule #getData(#uint256( DATA )) => #asByteStackInWidth( DATA , 32 )
```


Sum to N
--------

As a demonstration of simple reachability claims involving a circularity, we prove the EVM [Sum to N](proofs/sum-to-n.md) program correct.
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

```{.k .java}
endmodule
```
