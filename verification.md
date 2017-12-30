KEVM Verification
=================

Using K's reachability logic theorem prover, we're able to verify many properties about EVM programs as reachability claims.
This module defines some helpers which make writing specifications simpler.

```{.k .uiuck}
requires "evm.k"

module VERIFICATION
    imports EVM
```

This `smt-lemma` helps Z3 reason about stack over/under flow.

```{.k .uiuck}
//  rule #sizeWordStack ( _ , _ ) >=Int 0 => true [smt-lemma]
//  rule #sizeWordStack ( WS , N:Int )
//    => #sizeWordStack ( WS , 0 ) +Int N
//    requires N =/=K 0
//    [lemma]

//  rule (X -Int A) -Int B    => X -Int (A +Int B)    [smt-lemma]
//  rule ((X -Int A) >=Int B) => (X >=Int (A +Int B)) [smt-lemma]
//  rule (N +Int X <Int M)    => X <Int (M -Int N)    [smt-lemma]
```

Sum to N
--------

As a demonstration of simple reachability claims involing a circularity, we prove the EVM [Sum to N](proofs/sum-to-n.md) program correct.
This program sums the numbers from 1 to N (for sufficiently small N), including pre-conditions dis-allowing integer under/overflow and stack overflow.

```{.k .uiuck}
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

```{.k .uiuck}
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

    rule %HKG_ProgramBytes       => #parseByteStack("0x60606040526004361061006d576000357c0100000000000000000000000000000000000000000000000000000000900463ffffffff168063095ea7b31461007257806323b872dd146100cc57806370a0823114610145578063a9059cbb14610192578063dd62ed3e146101ec575b600080fd5b341561007d57600080fd5b6100b2600480803573ffffffffffffffffffffffffffffffffffffffff16906020019091908035906020019091905050610258565b604051808215151515815260200191505060405180910390f35b34156100d757600080fd5b61012b600480803573ffffffffffffffffffffffffffffffffffffffff1690602001909190803573ffffffffffffffffffffffffffffffffffffffff1690602001909190803590602001909190505061034a565b604051808215151515815260200191505060405180910390f35b341561015057600080fd5b61017c600480803573ffffffffffffffffffffffffffffffffffffffff169060200190919050506105c6565b6040518082815260200191505060405180910390f35b341561019d57600080fd5b6101d2600480803573ffffffffffffffffffffffffffffffffffffffff1690602001909190803590602001909190505061060f565b604051808215151515815260200191505060405180910390f35b34156101f757600080fd5b610242600480803573ffffffffffffffffffffffffffffffffffffffff1690602001909190803573ffffffffffffffffffffffffffffffffffffffff16906020019091905050610778565b6040518082815260200191505060405180910390f35b600081600260003373ffffffffffffffffffffffffffffffffffffffff1673ffffffffffffffffffffffffffffffffffffffff16815260200190815260200160002060008573ffffffffffffffffffffffffffffffffffffffff1673ffffffffffffffffffffffffffffffffffffffff168152602001908152602001600020819055508273ffffffffffffffffffffffffffffffffffffffff163373ffffffffffffffffffffffffffffffffffffffff167f8c5be1e5ebec7d5bd14f71427d1e84f3dd0314c0f7b2291e5b200ac8c7c3b925846040518082815260200191505060405180910390a36001905092915050565b600081600160008673ffffffffffffffffffffffffffffffffffffffff1673ffffffffffffffffffffffffffffffffffffffff1681526020019081526020016000205410158015610417575081600260008673ffffffffffffffffffffffffffffffffffffffff1673ffffffffffffffffffffffffffffffffffffffff16815260200190815260200160002060003373ffffffffffffffffffffffffffffffffffffffff1673ffffffffffffffffffffffffffffffffffffffff1681526020019081526020016000205410155b80156104235750600082115b156105ba5781600160008673ffffffffffffffffffffffffffffffffffffffff1673ffffffffffffffffffffffffffffffffffffffff1681526020019081526020016000206000828254039250508190555081600160008573ffffffffffffffffffffffffffffffffffffffff1673ffffffffffffffffffffffffffffffffffffffff1681526020019081526020016000206000828254019250508190555081600260008673ffffffffffffffffffffffffffffffffffffffff1673ffffffffffffffffffffffffffffffffffffffff16815260200190815260200160002060003373ffffffffffffffffffffffffffffffffffffffff1673ffffffffffffffffffffffffffffffffffffffff168152602001908152602001600020600082825403925050819055508273ffffffffffffffffffffffffffffffffffffffff168473ffffffffffffffffffffffffffffffffffffffff167fddf252ad1be2c89b69c2b068fc378daa952ba7f163c4a11628f55a4df523b3ef846040518082815260200191505060405180910390a3600190506105bf565b600090505b9392505050565b6000600160008373ffffffffffffffffffffffffffffffffffffffff1673ffffffffffffffffffffffffffffffffffffffff168152602001908152602001600020549050919050565b600081600160003373ffffffffffffffffffffffffffffffffffffffff1673ffffffffffffffffffffffffffffffffffffffff16815260200190815260200160002054101580156106605750600082115b1561076d5781600160003373ffffffffffffffffffffffffffffffffffffffff1673ffffffffffffffffffffffffffffffffffffffff1681526020019081526020016000206000828254039250508190555081600160008573ffffffffffffffffffffffffffffffffffffffff1673ffffffffffffffffffffffffffffffffffffffff168152602001908152602001600020600082825401925050819055508273ffffffffffffffffffffffffffffffffffffffff163373ffffffffffffffffffffffffffffffffffffffff167fddf252ad1be2c89b69c2b068fc378daa952ba7f163c4a11628f55a4df523b3ef846040518082815260200191505060405180910390a360019050610772565b600090505b92915050565b6000600260008473ffffffffffffffffffffffffffffffffffffffff1673ffffffffffffffffffffffffffffffffffffffff16815260200190815260200160002060008373ffffffffffffffffffffffffffffffffffffffff1673ffffffffffffffffffffffffffffffffffffffff168152602001908152602001600020549050929150505600a165627a7a723058207e0ec45a8f499af74c964dd2887d82a5b0f9522a60a1df3f107bddccf74118470029")                 [macro]
    rule %HKG_ProgramBytes_buggy => #parseByteStack("60606040526000357c0100000000000000000000000000000000000000000000000000000000900463ffffffff168063095ea7b31461006a57806323b872dd146100c457806370a082311461013d578063a9059cbb1461018a578063dd62ed3e146101e4575b600080fd5b341561007557600080fd5b6100aa600480803573ffffffffffffffffffffffffffffffffffffffff16906020019091908035906020019091905050610250565b604051808215151515815260200191505060405180910390f35b34156100cf57600080fd5b610123600480803573ffffffffffffffffffffffffffffffffffffffff1690602001909190803573ffffffffffffffffffffffffffffffffffffffff16906020019091908035906020019091905050610343565b604051808215151515815260200191505060405180910390f35b341561014857600080fd5b610174600480803573ffffffffffffffffffffffffffffffffffffffff169060200190919050506105c4565b6040518082815260200191505060405180910390f35b341561019557600080fd5b6101ca600480803573ffffffffffffffffffffffffffffffffffffffff1690602001909190803590602001909190505061060e565b604051808215151515815260200191505060405180910390f35b34156101ef57600080fd5b61023a600480803573ffffffffffffffffffffffffffffffffffffffff1690602001909190803573ffffffffffffffffffffffffffffffffffffffff16906020019091905050610773565b6040518082815260200191505060405180910390f35b600081600260003373ffffffffffffffffffffffffffffffffffffffff1673ffffffffffffffffffffffffffffffffffffffff16815260200190815260200160002060008573ffffffffffffffffffffffffffffffffffffffff1673ffffffffffffffffffffffffffffffffffffffff168152602001908152602001600020819055508273ffffffffffffffffffffffffffffffffffffffff163373ffffffffffffffffffffffffffffffffffffffff167f8c5be1e5ebec7d5bd14f71427d1e84f3dd0314c0f7b2291e5b200ac8c7c3b925846040518082815260200191505060405180910390a3600190505b92915050565b600081600160008673ffffffffffffffffffffffffffffffffffffffff1673ffffffffffffffffffffffffffffffffffffffff1681526020019081526020016000205410158015610410575081600260008673ffffffffffffffffffffffffffffffffffffffff1673ffffffffffffffffffffffffffffffffffffffff16815260200190815260200160002060003373ffffffffffffffffffffffffffffffffffffffff1673ffffffffffffffffffffffffffffffffffffffff1681526020019081526020016000205410155b801561041c5750600082115b156105b35781600160008673ffffffffffffffffffffffffffffffffffffffff1673ffffffffffffffffffffffffffffffffffffffff1681526020019081526020016000206000828254039250508190555081600160008573ffffffffffffffffffffffffffffffffffffffff1673ffffffffffffffffffffffffffffffffffffffff1681526020019081526020016000206000828254019250508190555081600260008673ffffffffffffffffffffffffffffffffffffffff1673ffffffffffffffffffffffffffffffffffffffff16815260200190815260200160002060003373ffffffffffffffffffffffffffffffffffffffff1673ffffffffffffffffffffffffffffffffffffffff168152602001908152602001600020600082825403925050819055508273ffffffffffffffffffffffffffffffffffffffff168473ffffffffffffffffffffffffffffffffffffffff167fddf252ad1be2c89b69c2b068fc378daa952ba7f163c4a11628f55a4df523b3ef846040518082815260200191505060405180910390a3600190506105bd565b600090506105bd565b5b9392505050565b6000600160008373ffffffffffffffffffffffffffffffffffffffff1673ffffffffffffffffffffffffffffffffffffffff1681526020019081526020016000205490505b919050565b600081600160003373ffffffffffffffffffffffffffffffffffffffff1673ffffffffffffffffffffffffffffffffffffffff168152602001908152602001600020541015801561065f5750600082115b156107635781600160003373ffffffffffffffffffffffffffffffffffffffff1673ffffffffffffffffffffffffffffffffffffffff1681526020019081526020016000206000828254039250508190555081600160008573ffffffffffffffffffffffffffffffffffffffff1673ffffffffffffffffffffffffffffffffffffffff168152602001908152602001600020819055508273ffffffffffffffffffffffffffffffffffffffff163373ffffffffffffffffffffffffffffffffffffffff167fddf252ad1be2c89b69c2b068fc378daa952ba7f163c4a11628f55a4df523b3ef846040518082815260200191505060405180910390a36001905061076d565b6000905061076d565b5b92915050565b6000600260008473ffffffffffffffffffffffffffffffffffffffff1673ffffffffffffffffffffffffffffffffffffffff16815260200190815260200160002060008373ffffffffffffffffffffffffffffffffffffffff1673ffffffffffffffffffffffffffffffffffffffff1681526020019081526020016000205490505b929150505600a165627a7a7230582093e640afb442869193a08cf82ed9577e403c7c53a6a95f589e2b673195da102e0029") [macro]

    rule %HKG_Program => #asMapOpCodes(#dasmOpCodes(%HKG_ProgramBytes, DEFAULT))
    rule %HKG_Program_buggy => #asMapOpCodes(#dasmOpCodes(%HKG_ProgramBytes_buggy, DEFAULT))


///////////////
// Viper
///////////////

  rule 0 |Int N => N
  rule N |Int 0 => N

  rule 0 &Int N => 0
  rule N &Int 0 => 0

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

//// for viper-specific addition overflow check
//rule bool2int(B ==K 0) |Int bool2int(chop(A +Int B) >Int A) => 1
//  requires A +Int B <Int /* pow256 */ 115792089237316195423570985008687907853269984665640564039457584007913129639936
//   andBool 0 <=Int A andBool A <Int /* pow256 */ 115792089237316195423570985008687907853269984665640564039457584007913129639936
//   andBool 0 <=Int B andBool B <Int /* pow256 */ 115792089237316195423570985008687907853269984665640564039457584007913129639936
////
//rule chop(A +Int B) >Int A => false
//  requires A +Int B >=Int /* pow256 */ 115792089237316195423570985008687907853269984665640564039457584007913129639936
//   andBool 0 <=Int A andBool A <Int /* pow256 */ 115792089237316195423570985008687907853269984665640564039457584007913129639936
//   andBool 0 <=Int B andBool B <Int /* pow256 */ 115792089237316195423570985008687907853269984665640564039457584007913129639936

//// TODO: remove by resolving chop?
//rule chop(A -Int B) +Int B => A
//  requires A >=Int B
//   andBool 0 <=Int A andBool A <Int /* pow256 */ 115792089237316195423570985008687907853269984665640564039457584007913129639936
//   andBool 0 <=Int B andBool B <Int /* pow256 */ 115792089237316195423570985008687907853269984665640564039457584007913129639936

  // for gas calculation
  rule A -Int (#ifInt C #then B1 #else B2 #fi) => #ifInt C #then (A -Int B1) #else (A -Int B2) #fi
  rule (#ifInt C #then B1 #else B2 #fi) -Int A => #ifInt C #then (B1 -Int A) #else (B2 -Int A) #fi

  // TODO: change semantics
  rule chop(I) => I modInt /* pow256 */ 115792089237316195423570985008687907853269984665640564039457584007913129639936 [concrete, smt-lemma]

  syntax Int ::= nthbyteof(Int, Int, Int) [function, smtlib(smt_nthbyteof)]

  rule nthbyteof(V, I, N) => nthbyteof(V /Int 256, I, N -Int 1) when N  >Int (I +Int 1) [concrete]
  rule nthbyteof(V, I, N) =>           V %Int 256               when N ==Int (I +Int 1) [concrete]

  rule 0 <=Int nthbyteof(V, I, N)          => true
  rule         nthbyteof(V, I, N) <Int 256 => true

  rule 0 <=Int chop(V)                     => true
  rule         chop(V) <Int /* 2 ^Int 256 */ 115792089237316195423570985008687907853269984665640564039457584007913129639936 => true

  // syntactic sugar
  syntax WordStack ::= int2wordstack(Int, Int) [function]
                     | int2wordstackaux(Int, Int, Int, WordStack) [function]
  rule int2wordstack(X, N) => int2wordstackaux(X, N -Int 1, N, .WordStack)
  rule int2wordstackaux(X, I, N, WS) => int2wordstackaux(X, I -Int 1, N, nthbyteof(X, I, N) : WS) when I >Int 0
  rule int2wordstackaux(X, 0, N, WS) => nthbyteof(X, 0, N) : WS

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

  rule #asByteStack(V) => int2wordstack(V, 32)
    requires 0 <=Int V andBool V <Int (2 ^Int 256)

  // for extracting first four bytes of function signature
  rule #asByteStack(#asWord(WS)) => WS
    requires noOverflow(WS)

  syntax Bool ::= noOverflow(WordStack)    [function]
                | noOverflowAux(WordStack) [function]
  rule noOverflow(WS) => #sizeWordStack(WS) <=Int 32 andBool noOverflowAux(WS)
  rule noOverflowAux(W : WS) => 0 <=Int W andBool W <Int 256 andBool noOverflowAux(WS)
  rule noOverflowAux(.WordStack) => true



  // for medeling collision-free hash function
  syntax Int ::= hash(Int) [smtlib(smt_hash)]

  syntax Int ::= sha3(Int) [function]
  rule sha3(V) => keccak(#padToWidth(32, #asByteStack(V)))

  rule keccak( nthbyteof(V,  0, 32)
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
             : .WordStack ) => hash(V)
    requires 0 <=Int V andBool V <Int (2 ^Int 256)
```
The corresponding operations perform manipulations on
byte represetnations of words.

- An aligned division operation can be attained via byte shifts.
- Consider `B1: B2: B3: .WordStack` is bytes based word stack. Division by
256 is `B1: B2: .WordStack`. It doesn't matter if B3 is symbolic, as long as B3 <= 255.
- The rule only applies on `#asWord`, which only operates over byte-stacks.

```{.k .uiuck}

  rule chop( #asWord( WS ) /Int D ) => #asWord( #take(#sizeWordStack( WS ) -Int log256Int( D ), WS) )
    requires D %Int 256 ==Int 0

```
- The corresponding Lemmas operate over `&Int` and `chop`
- X &Int (2^a - 1) == X, given X <= (2^a - 1)

```{.k .uiuck}
   rule chop(X &Int Y)    => X &Int Y    requires (X <Int pow256) orBool (Y <Int pow256)

   // &Int Associativity
   rule X &Int (Y &Int Z) => (X &Int Y) &Int Z

   rule X &Int Y          => Y           requires    (((2 ^Int (log2Int(X) +Int 1)) -Int 1) ==Int X)
                                          andBool      (Y <=Int X)

endmodule
```
