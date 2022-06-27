# 1. Bihu

## 1.1. Improvements

Two previously failing tests now passing

```
tests/specs/bihu/forwardToHotWallet-success-1-spec.k    10m 13s
tests/specs/bihu/forwardToHotWallet-success-2-spec.k    10m 21s
```

## 1.2. Changes to codebase

The following simplification was made an smt-lemma (in [`tests/specs/lemmas.k`](./specs/lemmas.k))

```
rule 0 <=Int chop(_V) => true [simplification, smt-lemma]
```

In addition, the following function has been annotated with `no-evaluators` (in [`tests/specs/bihu/verification.k`](./specs/bihu/verification.k))

```
syntax Int ::= "#accumulatedReleasedTokens" "(" Int "," Int "," Int "," Int ")"  [function, no-evaluators]
```

to silence no-evaluation warnings emitted by the Haskell back-end. 

## 1.3. Remaining failing tests

One more test is failing, [`tests/specs/bihu/collectToken-spec.k`](./specs/bihu/collectToken-spec.k), after 2h 14m, reporting a (very likely) infeasible branch, with
```
<statusCode>
    EVMC_INVALID_INSTRUCTION
</statusCode>
```
but I cannot find the source of infeasibility. I suspect that it has to do something with 

```
[EQ] X <Int chop ( X -Int COLLECTED )
```

where

```
[EQX] X = chop ( Y *Int 10 /Int 100 *Int ( ( NOW -Int START ) modInt 31536000 ) /Int 31536000 +Int COLLECTED +Int BAL -Int Y )
[EQY] Y = #roundpower ( COLLECTED +Int BAL , 90 , 100 , ( NOW -Int START ) /Int 31536000 )
```

with `#rangeUInt(256, X)` and `#rangeUInt(256, COLLECTED)`. Given this, for [EQ] to hold, it must be that `X <Int COLLECTED`, which is probably impossible but I cannot see why, since I cannot quite figure out what `#roundpower` does.

**QUESTION**: In `X`, why `Y *Int 10 /Int 100` and not `Y /Int 10`?

# 2. MCD

## 1.1. Improvements

Twelve previously failing tests now passing:

```
tests/specs/mcd/end-cash-pass-rough-spec.k                          1h 11m 01s
tests/specs/mcd/end-pack-pass-rough-spec.k                             34m 50s
tests/specs/mcd/flapper-tend-guy-diff-pass-rough-spec.k                 1m 38s
tests/specs/mcd/flapper-yank-pass-rough-spec.k                      2h 35m 48s
tests/specs/mcd/flipper-bids-pass-rough-spec.k                         21m 51s
tests/specs/mcd/flopper-dent-guy-diff-tic-not-0-pass-rough-spec.k       2m 07s
tests/specs/mcd/flopper-dent-guy-same-pass-rough-spec.k                    52s
tests/specs/mcd/gemjoin-exit-pass-rough-spec.k                      1h 16m 01s
tests/specs/mcd/pot-join-pass-rough-spec.k                             23m 01s
tests/specs/mcd/vat-fold-pass-rough-spec.k                             56m 20s
tests/specs/mcd/vat-fork-diff-pass-rough-spec.k                     5h 07m 00s
tests/specs/mcd/vat-slip-pass-rough-spec.k                             15m 26s
```

## 1.2. Changes to codebase

### 1.2.1. [hashed-locations.md](../hashed-locations.md)

Added `[simplification]` to the rule below because in one of the outputs `#hashedLocation` was not unfolded in one instance, and it was necessary for it to be unfolded for the test to pass.

```
rule #hashedLocation("Solidity", BASE, OFFSET .IntList) => keccak(#bufStrict(32, OFFSET) ++ #bufStrict(32, BASE))   
     requires #rangeUInt(256, BASE) andBool #rangeUInt(256, OFFSET) [simplification]
```

**TO UNDERSTAND**: Why was `#hashedLocation` not unfolded specifically in that one instance?

### 1.2.2. [verification.k](./specs/mcd/verification.k)

### 1.2.3.1. Reasoning about `chop` for signed 256-bit integers

```
rule { chop(X) #Equals chop(Y) } => { X #Equals Y }
    requires #rangeSInt(256, X) andBool #rangeSInt(256, Y)
    [simplification]

rule { chop ( X ) #Equals chop ( Y ) } => 
    { X #Equals Y } #And { Y <=Int 0 }
    requires (minSInt256 <=Int X) andBool (X <=Int 0) andBool #rangeSInt(256, Y) [simplification]
```

### 1.2.3.2. Buffer reasoning

```
rule { BA1:ByteArray ++ BA2:ByteArray #Equals BA1:ByteArray ++ BA3:ByteArray } => { BA2 #Equals BA3 } [simplification]

rule { BA1:ByteArray ++ (BA2:ByteArray ++ BA3:ByteArray) #Equals BA4:ByteArray ++ BA3:ByteArray } => { BA1 ++ BA2 #Equals BA4 } [simplification]

rule { #buf(32, BY:Int):ByteArray #Equals #buf(32, BZ:Int):ByteArray } => { BY #Equals BZ }
     requires #rangeUInt(256, BY) andBool #rangeUInt(256, BZ) [simplification]

rule { #buf(32, BY:Int):ByteArray #Equals #buf(32, BZ:Int):ByteArray ++ BA2:ByteArray } => 
     { BY #Equals BZ } #And { .ByteArray #Equals BA2 } 
     requires #rangeUInt(256, BY) andBool #rangeUInt(256, BZ) [simplification]

rule { #buf(32, BY:Int):ByteArray ++ BA1:ByteArray #Equals #buf(32, BZ:Int):ByteArray ++ BA2:ByteArray } => 
     { BY #Equals BZ } #And { BA1 #Equals BA2 } 
     requires #rangeUInt(256, BY) andBool #rangeUInt(256, BZ) [simplification]
```

**THOUGHT**: What if `++` were n-ary? Is there a way to match on the last concatenated buffer with current associativity? 

### 1.2.3.3. Map reasoning

```
rule { (M:Map [K <- V1]) #Equals (M [K <- V2]) } => { V1 #Equals V2 }
    [simplification]

rule { M:Map [K <- V1] #Equals M } => 
    { K in_keys(M) } #And { V1 #Equals #lookup (M, K) }
    [simplification]
```

### 1.2.3. [word-pack.k](./specs/mcd/word-pack.k)

### 1.2.3.1. Decomposition of `#WordPack`

Introduced simplifications that describe decomposition of the three `#WordPack` predicates, including ranges of parameters and the symmetry of initial equality, both at the `Int`-level and the ML-level. For example, for `#WordPackUInt48UInt48` the simplifications are as follows:

```
    rule       UINT48_UINT48 ==Int #WordPackUInt48UInt48(UINT48_1, UINT48_2)
            => UINT48_1 ==Int maxUInt48 &Int  UINT48_UINT48
       andBool UINT48_2 ==Int maxUInt48 &Int (UINT48_UINT48 /Int pow48)
       andBool (0 <=Int UINT48_UINT48) andBool (UINT48_UINT48 <Int pow96)
       andBool (0 <=Int UINT48_1) andBool (UINT48_1 <Int pow48)
       andBool (0 <=Int UINT48_2) andBool (UINT48_2 <Int pow48)
       [simplification]

    rule       #WordPackUInt48UInt48(UINT48_1, UINT48_2) ==Int UINT48_UINT48
            => UINT48_1 ==Int maxUInt48 &Int  UINT48_UINT48
       andBool UINT48_2 ==Int maxUInt48 &Int (UINT48_UINT48 /Int pow48)
       andBool (0 <=Int UINT48_UINT48) andBool (UINT48_UINT48 <Int pow96)
       andBool (0 <=Int UINT48_1) andBool (UINT48_1 <Int pow48)
       andBool (0 <=Int UINT48_2) andBool (UINT48_2 <Int pow48)
               [simplification]

    rule    { UINT48_UINT48 #Equals #WordPackUInt48UInt48(UINT48_1, UINT48_2) }
         => { UINT48_1 #Equals maxUInt48 &Int  UINT48_UINT48 }
       #And { UINT48_2 #Equals maxUInt48 &Int (UINT48_UINT48 /Int pow48) }
       #And { 0 <=Int UINT48_UINT48 } #And { UINT48_UINT48 <Int pow96 }
       #And { 0 <=Int UINT48_1 } #And { UINT48_1 <Int pow48 }
       #And { 0 <=Int UINT48_2 } #And { UINT48_2 <Int pow48 }
       [simplification]

    rule    { #WordPackUInt48UInt48(UINT48_1, UINT48_2) #Equals UINT48_UINT48}
         => { UINT48_1 #Equals maxUInt48 &Int  UINT48_UINT48 }
       #And { UINT48_2 #Equals maxUInt48 &Int (UINT48_UINT48 /Int pow48) }
       #And { 0 <=Int UINT48_UINT48 } #And { UINT48_UINT48 <Int pow96 }
       #And { 0 <=Int UINT48_1 } #And { UINT48_1 <Int pow48 }
       #And { 0 <=Int UINT48_2 } #And { UINT48_2 <Int pow48 }
       [simplification]
```

**TO UNDERSTAND**: Are both levels necessary? Could `Int`-level can be lifted to ML-level?

#### 1.2.3.2 [word-pack.k](./specs/mcd/word-pack.k): Arithmetic reasoning 

```
rule maxUInt48 &Int _ /Int C => 0 requires C >Int maxUInt48 [simplification]
rule A /Int pow48 => 0 requires #rangeUInt(48, A) [simplification]
```

## 1.3. Remaining failing tests

There are six tests that are still failing - three I am not able to debug, three I am not able to run.

### 1.3.1. `flopper-file-pass`

Test cannot prove final implication for the case when `[EQ] ABI_what ==Int #string2Word("beg")`. I believe the critical part is 

```
#Not ( 
    #Ceil ( #WordPackUInt48UInt48 ( ABI_data , 0 ) )
  #And
    #Ceil ( #WordPackUInt48UInt48 ( maxUInt48 &Int #lookup ( ACCT_ID_STORAGE , 6 ) , 0 ) )
  #And
    #Ceil ( #WordPackUInt48UInt48 ( maxUInt48 &Int #lookup ( ACCT_ID_STORAGE , 6 ) , ABI_data ) ) )
```

for which it seems there is not enough information to decide. In particular, given `[EQ]`, `ABI_data` is only restricted by `#rangeUInt(256, ABI_data)`, due to

```
requires ((ABI_what =/=Int #string2Word("ttl") andBool ABI_what =/=Int #string2Word("tau")) orBool #rangeUInt(48, ABI_data))
```

which means that `#WordPackUInt48UInt48 ( ABI_data , 0 )` might or might not be defined. I do not quite understand why the above constraints are introduced, possibly because of 

```
<storage> 
    ACCT_ID_STORAGE => 
    ACCT_ID_STORAGE [ #Flopper.beg <- (#if ABI_what ==Int #string2Word("beg") #then ABI_data #else Beg #fi) ] 
                    [ #Flopper.pad <- (#if ABI_what ==Int #string2Word("pad") #then ABI_data #else Pad #fi) ] 
                    [ #Flopper.ttl_tau <- 
                        (#if ABI_what ==Int #string2Word("ttl") 
                            #then #WordPackUInt48UInt48(ABI_data, Tau) 
                            #else (#if ABI_what ==Int #string2Word("tau") 
                                      #then #WordPackUInt48UInt48(Ttl, ABI_data) 
                                      #else #WordPackUInt48UInt48(Ttl, Tau) #fi) #fi) ] 
</storage>
```

Is it possible that definability questions are asked before the `#if`s are resolved (given `[EQ]`)?

### 1.3.2. [`flopper-kick-pass`](./specs/mcd/flopper-kick-pass-rough-spec.k) and [`flopper-tick-pass`](./specs/mcd/flopper-tick-pass-rough-spec.k)

Both tests report infeasible branches, with 

```
<statusCode>
    EVMC_REVERT
</statusCode>
```

The branches are infeasible and the conjunct that is false in the reported final state is of the form:

```
  #Not ( 
    { [SOMETHING TRIVIALLY TRUE] }
  #And
    {
      true
    #Equals
      0 <=Int #lookup ( ACCT_ID_STORAGE , 6 ) /Int pow48
    }
  #And
    {
      true
    #Equals
      #lookup ( ACCT_ID_STORAGE , 6 ) /Int pow48 <Int pow48
    }
  #And
    {
      true
    #Equals
      TIME +Int #lookup ( ACCT_ID_STORAGE , 6 ) /Int pow48 <Int pow48
    } )
```

where `#lookup ( ACCT_ID_STORAGE , 6 ) /Int pow48` corresponds to the variable `Ttl` in the spec, meant to be bounded by `requires #rangeUInt(48, Ttl)`, but the corresponding constraints are not in the reported final state for some reason. The same goes for `Tau`, and also the constraints that I would expect to come from the decomposition of `#WordPackUInt48UInt48(Ttl, Tau)`.

### 1.3.3. Other tests

Finally, I am not able to run the three following tests:

```
tests/specs/mcd/vat-frob-diff-zero-dart-pass-rough-spec.k
tests/specs/mcd/vow-cage-deficit-pass-rough-spec.k
tests/specs/mcd/vow-cage-surplus-pass-rough-spec.k
```

due to continuously getting:

```
[Error] Critical: Could not start z3 process (IOException: Cannot run program "z3": /dev/null (Too many open files))
```

which does appear stochastically for the other tests as well, but with sufficiently many attempts I am able to run the other tests.