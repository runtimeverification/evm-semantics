KEVM Infinite Gas
=================

Here we use the construct `#gas` to represent positive infinity, while tracking the gas formula through execution.
This allows (i) computing final gas used, and (ii) never stopping because of out-of-gas.
Note that the argument to `#gas(_)` is just metadata tracking the current gas usage, and is not meant to be compared to other values.
As such, any `#gas(G)` and `#gas(G')` are the _same_ positive infinite, regardless of the values `G` and `G'`.
In particular, this means that `#gas(_) <Int #gas(_) => false`, and `#gas(_) <=Int #gas(_) => true`, regardless of the values contained in the `#gas(_)`.

```k
requires "evm.md"

module INFINITE-GAS
    imports INFINITE-GAS-JAVA
    imports INFINITE-GAS-HASKELL
endmodule

module INFINITE-GAS-JAVA [kast]
    imports INFINITE-GAS-COMMON
    imports K-REFLECTION

    rule #gas(_) <=Int C => false requires #isConcrete(C) [simplification]
    rule C <=Int #gas(_) => true  requires #isConcrete(C) [simplification]

    // TODO: figure out how to safely use these to replace the associativity
    //       rules in lemmas.k by organizing them into int-simplification.k
    rule C1 +Int S2 => S2 +Int C1 requires #isConcrete(C1) andBool notBool #isConcrete(S2) [simplification]

    rule S1 +Int (C2 -Int S3) => (S1 -Int S3) +Int C2 requires #isConcrete(C2) andBool (notBool #isConcrete(S1)) andBool (notBool #isConcrete(S3)) [simplification]
    rule S1 -Int (C2 -Int S3) => (S1 +Int S3) -Int C2 requires #isConcrete(C2) andBool (notBool #isConcrete(S1)) andBool (notBool #isConcrete(S3)) [simplification]

    rule (I1 +Int C2) +Int S3 => (I1 +Int S3) +Int C2 requires #isConcrete(C2) andBool notBool #isConcrete(S3) [simplification]
    rule (I1 +Int C2) -Int S3 => (I1 -Int S3) +Int C2 requires #isConcrete(C2) andBool notBool #isConcrete(S3) [simplification]
    rule (I1 -Int C2) +Int S3 => (I1 +Int S3) -Int C2 requires #isConcrete(C2) andBool notBool #isConcrete(S3) [simplification]
    rule (I1 -Int C2) -Int S3 => (I1 -Int S3) -Int C2 requires #isConcrete(C2) andBool notBool #isConcrete(S3) [simplification]

    rule (S1 +Int C2) +Int C3 => S1 +Int (C2 +Int C3) requires #isConcrete(C2) andBool #isConcrete(C3) andBool notBool #isConcrete(S1) [simplification]
    rule (S1 +Int C2) -Int C3 => S1 +Int (C2 -Int C3) requires #isConcrete(C2) andBool #isConcrete(C3) andBool notBool #isConcrete(S1) [simplification]
    rule (S1 -Int C2) +Int C3 => S1 +Int (C3 -Int C2) requires #isConcrete(C2) andBool #isConcrete(C3) andBool notBool #isConcrete(S1) [simplification]
    rule (S1 -Int C2) -Int C3 => S1 -Int (C2 +Int C3) requires #isConcrete(C2) andBool #isConcrete(C3) andBool notBool #isConcrete(S1) [simplification]
endmodule

module INFINITE-GAS-JAVA-EXTRA [kast]
    imports INFINITE-GAS-JAVA

    // These lemmas conflict with a lemma in `bihu` proofs about `chop(I1 + (I2 - I3))`.
    // Because these are just for Java backend, we pull them out and re-include them where they are needed (`mcd` and `benchmarks`).
    // When Java backend is removed, we can delete this module anyway.

    rule S1 +Int (S2 +Int I3) => (S1 +Int S2) +Int I3 requires (notBool #isConcrete(S1)) andBool (notBool #isConcrete(S2)) [simplification]
    rule S1 +Int (S2 -Int I3) => (S1 +Int S2) -Int I3 requires (notBool #isConcrete(S1)) andBool (notBool #isConcrete(S2)) [simplification]
    rule S1 -Int (S2 +Int I3) => (S1 -Int S2) -Int I3 requires (notBool #isConcrete(S1)) andBool (notBool #isConcrete(S2)) [simplification]
    rule S1 -Int (S2 -Int I3) => (S1 -Int S2) +Int I3 requires (notBool #isConcrete(S1)) andBool (notBool #isConcrete(S2)) [simplification]
endmodule

module INFINITE-GAS-HASKELL [kore]
    imports INFINITE-GAS-COMMON

    rule #gas(_) <=Int _C => false [concrete(_C), simplification]
    rule _C <=Int #gas(_) => true  [concrete(_C), simplification]

    rule { #gas(_) #Equals #gas(_) } => #Top [simplification]
endmodule

module INFINITE-GAS-COMMON
    imports EVM

 // Generic rules

    rule (notBool (A andBool B)) andBool A => (notBool B) andBool A                      [simplification]
    rule #if B #then C +Int C1 #else C +Int C2 #fi => C +Int #if B #then C1 #else C2 #fi [simplification]

 // Symbolic Gas

    syntax Int ::= #gas ( Int ) [function, total, no-evaluators, klabel(infGas), symbol, smtlib(infGas)]
 // ----------------------------------------------------------------------------------------------------
    rule #gas(G) +Int G' => #gas(G +Int G') requires 0 <=Int G' orBool 0 -Int G' <Int #gas(G)  [simplification]
    rule G +Int #gas(G') => #gas(G +Int G') requires 0 <=Int G  orBool 0 -Int G  <Int #gas(G') [simplification]

    rule #gas(G) -Int G'       => #gas(G -Int G') requires 0 <=Int G' andBool G' <Int #gas(G) [simplification]
    rule #gas(G) -Int #gas(G') => #gas(G -Int G')                                             [simplification]

    rule #gas(G) *Int G' => #gas(G *Int G') requires 0 <=Int G' [simplification]
    rule G *Int #gas(G') => #gas(G *Int G') requires 0 <=Int G  [simplification]

    rule #gas(G) /Int G' => #gas(G /Int G') requires 0  <Int G' andBool G' <Int #gas(G)  [simplification]
    rule G /Int #gas(G') => 0               requires 0 <=Int G  andBool G  <Int #gas(G') [simplification]

    rule #gas(#gas(G)) => #gas(G) [simplification]
    rule #gas(#gas(G) +Int G') => #gas(G +Int G') [simplification]

    rule minInt(#gas(G), #gas(G'))              => #gas(minInt(G, G'))              [simplification]
    rule #if B #then #gas(G) #else #gas(G') #fi => #gas(#if B #then G #else G' #fi) [simplification]

    rule _ <=Int #gas(_)        => true  [simplification]
    rule         #gas(_) <Int _ => false [simplification]

    rule I         <Int #gas(_) => true requires I <=Int pow256                         [simplification]
    rule I *Int I' <Int #gas(G) => true requires I <Int #gas(G) andBool I' <Int #gas(G) [simplification]

    rule #gas(G) <=Int I +Int I' => false requires                     notBool (#gas(G) <=Int I orBool #gas(G) <=Int I') [simplification]
    rule #gas(G) <=Int I -Int I' => false requires                     notBool (#gas(G) <=Int I orBool #gas(G) <=Int I') [simplification]
    rule #gas(G) <=Int I *Int I' => false requires                     notBool (#gas(G) <=Int I orBool #gas(G) <=Int I') [simplification]
    rule #gas(G) <=Int I /Int I' => false requires I' =/=Int 0 andBool notBool (#gas(G) <=Int I orBool #gas(G) <=Int I') [simplification]

    rule 0 <=Int #memoryUsageUpdate(MU, START, WIDTH)              => true requires 0 <=Int MU      andBool 0 <=Int START       andBool 0     <=Int WIDTH   [simplification]
    rule         #memoryUsageUpdate(MU, START, WIDTH) <Int #gas(G) => true requires MU <Int #gas(G) andBool START  <Int #gas(G) andBool WIDTH  <Int #gas(G) [simplification]

    rule #memoryUsageUpdate(#memoryUsageUpdate(MU, START1, WIDTH1), START2, WIDTH2) => #memoryUsageUpdate(MU, START1, WIDTH1)
      requires #rangeUInt(256, MU) andBool 0 <Int WIDTH1 andBool 0 <Int WIDTH2
       andBool START2 +Int WIDTH2 <=Int START1 +Int WIDTH1
      [simplification]

    rule #memoryUsageUpdate(#memoryUsageUpdate(MU, START1, WIDTH1), START2, WIDTH2) => #memoryUsageUpdate(MU, START2, WIDTH2)
      requires #rangeUInt(256, MU) andBool 0 <Int WIDTH1 andBool 0 <Int WIDTH2
       andBool START1 +Int WIDTH1 <Int START2 +Int WIDTH2
      [simplification]

    rule 0 <=Int Csload(_, _)       => true  [simplification]
    rule Csload(_, _) <Int #gas(_)  => true  [simplification]
    rule #gas(_)  <Int Csload(_, _) => false [simplification]
    rule #gas(_) >=Int Csload(_, _) => true  [simplification]

    rule 0 <=Int Caddraccess(_, _)       => true  [simplification]
    rule Caddraccess(_, _) <Int #gas(_)  => true  [simplification]
    rule #gas(_) <Int Caddraccess(_, _)  => false [simplification]
    rule Caddraccess(_, _) <=Int #gas(_) => true  [simplification]

    rule 0 <=Int Csstore(_, _, _, _)              => true [simplification]
    rule         Csstore(_, _, _, _) <Int #gas(_) => true [simplification]

    rule 0 <=Int Cmem(_, N)              => true requires 0 <=Int N       [simplification]
    rule         Cmem(_, N) <Int #gas(G) => true requires N  <Int #gas(G) [simplification]

    rule Cgascap(SCHED, GAVAIL, GAVAIL, GEXTRA) => #allBut64th(GAVAIL -Int GEXTRA)
      requires 0 <=Int GEXTRA andBool GEXTRA <=Int GAVAIL
       andBool notBool Gstaticcalldepth << SCHED >>
      [simplification]

    rule 0 <=Int Cgascap(_, _, _, _)                    => true                                            [simplification]
    rule G <=Int Cgascap(_, GCAP, #gas(_), _)           => true  requires 0 <=Int G andBool G <=Int GCAP   [simplification]
    rule         Cgascap(_, GCAP, _, _)          <Int G => true  requires 0 <=Int GCAP andBool GCAP <Int G [simplification]
    rule         Cgascap(_, #gas(_), #gas(_), _) <Int _ => false                                           [simplification]

    rule 0 <=Int Cextra(_, _, _, _)              => true [simplification]
    rule         Cextra(_, _, _, _) <Int #gas(_) => true [simplification]
    rule         Cextra(_, _, _, _) <Int pow256  => true [simplification]

    rule #allBut64th(#gas(G))            => #gas(#allBut64th(G))         [simplification]
    rule (G /Int 64) +Int #allBut64th(G) => G                            [simplification]
    // TODO: Questionable lemma
    rule #gas(G) +Int #allBut64th(G')    => #gas(G +Int #allBut64th(G')) [simplification]

    rule 0 <=Int #allBut64th(G)         => true requires 0 <=Int G  [simplification]
    rule         #allBut64th(G) <Int G' => true requires G  <Int G' [simplification]

    rule 0 <=Int _:ScheduleConst < _:Schedule >               => true [simplification]
    rule         _:ScheduleConst < _:Schedule >  <Int #gas(_) => true [simplification]

    rule 0 <=Int G up/Int _                => true requires 0 <=Int G        [simplification]
    rule G         up/Int _  <Int #gas(G') => true requires G  <Int #gas(G') [simplification]

    rule 0 <=Int Csload(_, _)       => true  [simplification]
    rule Csload(_, _) <Int #gas(_)  => true  [simplification]
    rule #gas(_) <Int Csload(_, _)  => false [simplification]
    rule Csload(_, _) <=Int #gas(_) => true  [simplification]

endmodule
```
