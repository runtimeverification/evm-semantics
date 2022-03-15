requires "evm.md"
requires "./int-simplification.k"

 //
 // Infinite Gas
 // Here we use the construct `#gas` to represent positive infinity, while tracking the gas formula through execution.
 // This allows (i) computing final gas used, and (ii) never stopping because of out-of-gas.
 // Note that the argument to `#gas(_)` is just metadata tracking the current gas usage, and is not meant to be compared to other values.
 // As such, any `#gas(G)` and `#gas(G')` are the _same_ positive infinite, regardless of the values `G` and `G'`.
 // In particular, this means that `#gas(_) <Int #gas(_) => false`, and `#gas(_) <=Int #gas(_) => true`, regardless of the values contained in the `#gas(_)`.
 //

module INFINITE-GAS
    imports INT-SIMPLIFICATION
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

    rule S1 +Int (S2 +Int I3) => (S1 +Int S2) +Int I3 requires (notBool #isConcrete(S1)) andBool (notBool #isConcrete(S2)) [simplification]
    rule S1 +Int (S2 -Int I3) => (S1 +Int S2) -Int I3 requires (notBool #isConcrete(S1)) andBool (notBool #isConcrete(S2)) [simplification]
    rule S1 -Int (S2 +Int I3) => (S1 -Int S2) -Int I3 requires (notBool #isConcrete(S1)) andBool (notBool #isConcrete(S2)) [simplification]
    rule S1 -Int (S2 -Int I3) => (S1 -Int S2) +Int I3 requires (notBool #isConcrete(S1)) andBool (notBool #isConcrete(S2)) [simplification]

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

module INFINITE-GAS-HASKELL [kore]
    imports INFINITE-GAS-COMMON

    rule #gas(_) <=Int _C => false [concrete(_C), simplification]
    rule _C <=Int #gas(_) => true  [concrete(_C), simplification]
endmodule

module INFINITE-GAS-COMMON
    imports EVM

 // Generic rules

    rule (notBool (A andBool B)) andBool A => (notBool B) andBool A                      [simplification]
    rule #if B #then C +Int C1 #else C +Int C2 #fi => C +Int #if B #then C1 #else C2 #fi [simplification]

 // Symbolic Gas

    syntax Int ::= #gas ( Int ) [function, functional, no-evaluators, klabel(infGas), symbol, smtlib(infGas)]
 // ---------------------------------------------------------------------------------------------------------

endmodule
