requires "evm.md"

 //
 // Infinite Gas
 // Here we use the construct `#gas` to represent positive infinity, while tracking the gas formula through execution.
 // This allows (i) computing final gas used, and (ii) never stopping because of out-of-gas.
 // Note that the argument to `#gas(_)` is just metadata tracking the current gas usage, and is not meant to be compared to other values.
 // As such, any `#gas(G)` and `#gas(G')` are the _same_ positive infinite, regardless of the values `G` and `G'`.
 // In particular, this means that `#gas(_) <Int #gas(_) => false`, and `#gas(_) <=Int #gas(_) => true`, regardless of the values contained in the `#gas(_)`.
 //

module INFINITE-GAS
    imports INFINITE-GAS-JAVA
    imports INFINITE-GAS-HASKELL
endmodule

module INFINITE-GAS-HASKELL [kore]
    imports INFINITE-GAS-COMMON

    rule #gas(_)  <Int _I => false [concrete(_I), simplification]
    rule #gas(_) <=Int _I => false [concrete(_I), simplification]
    rule #gas(_) >=Int _I => true  [concrete(_I), simplification]
    rule _I <=Int #gas(_) => true  [concrete(_I), simplification]

    rule I1 +Int I2  <Int I3         => I1          <Int I3 -Int I2 [concrete(I2, I3), simplification]
    rule I1          <Int I2 +Int I3 => I1 -Int I3  <Int I2         [concrete(I1, I3), simplification]
    rule I1         <=Int I2 +Int I3 => I1 -Int I3 <=Int I2         [concrete(I1, I3), simplification]

    rule (I1 +Int I2) +Int I3 => (I1 +Int I3) +Int I2 [concrete(I2), symbolic(I3), simplification]
    rule (I1 +Int I2) -Int I3 => (I1 -Int I3) +Int I2 [concrete(I2), symbolic(I3), simplification]
    rule (I1 -Int I2) +Int I3 => (I1 +Int I3) -Int I2 [concrete(I2), symbolic(I3), simplification]
    rule (I1 -Int I2) -Int I3 => (I1 -Int I3) -Int I2 [concrete(I2), symbolic(I3), simplification]

    rule (I1 +Int I2) +Int I3 => I1 +Int (I2 +Int I3) [concrete(I2, I3), symbolic(I1), simplification]
    rule (I1 +Int I2) -Int I3 => I1 +Int (I2 -Int I3) [concrete(I2, I3), symbolic(I1), simplification]
    rule (I1 -Int I2) +Int I3 => I1 +Int (I3 -Int I2) [concrete(I2, I3), symbolic(I1), simplification]
    rule (I1 -Int I2) -Int I3 => I1 -Int (I2 +Int I3) [concrete(I2, I3), symbolic(I1), simplification]
endmodule

module INFINITE-GAS-JAVA [kast]
    imports INFINITE-GAS-COMMON
    imports K-REFLECTION

    rule #gas(_)  <Int I => false requires #isConcrete(I) [simplification]
    rule #gas(_) <=Int I => false requires #isConcrete(I) [simplification]
    rule #gas(_) >=Int I => true  requires #isConcrete(I) [simplification]
    rule I <=Int #gas(_) => true  requires #isConcrete(I) [simplification]

    rule I1 +Int I2  <Int I3         => I1          <Int I3 -Int I2 requires #isConcrete(I2) andBool #isConcrete(I3) [simplification]
    rule I1          <Int I2 +Int I3 => I1 -Int I3  <Int I2         requires #isConcrete(I1) andBool #isConcrete(I3) [simplification]
    rule I1         <=Int I2 +Int I3 => I1 -Int I3 <=Int I2         requires #isConcrete(I1) andBool #isConcrete(I3) [simplification]

    rule (I1 +Int I2) +Int I3 => (I1 +Int I3) +Int I2 requires #isConcrete(I2) andBool notBool #isConcrete(I3) [simplification]
    rule (I1 +Int I2) -Int I3 => (I1 -Int I3) +Int I2 requires #isConcrete(I2) andBool notBool #isConcrete(I3) [simplification]
    rule (I1 -Int I2) +Int I3 => (I1 +Int I3) -Int I2 requires #isConcrete(I2) andBool notBool #isConcrete(I3) [simplification]
    rule (I1 -Int I2) -Int I3 => (I1 -Int I3) -Int I2 requires #isConcrete(I2) andBool notBool #isConcrete(I3) [simplification]

    rule (I1 +Int I2) +Int I3 => I1 +Int (I2 +Int I3) requires #isConcrete(I2) andBool #isConcrete(I3) andBool notBool #isConcrete(I1) [simplification]
    rule (I1 +Int I2) -Int I3 => I1 +Int (I2 -Int I3) requires #isConcrete(I2) andBool #isConcrete(I3) andBool notBool #isConcrete(I1) [simplification]
    rule (I1 -Int I2) +Int I3 => I1 +Int (I3 -Int I2) requires #isConcrete(I2) andBool #isConcrete(I3) andBool notBool #isConcrete(I1) [simplification]
    rule (I1 -Int I2) -Int I3 => I1 -Int (I2 +Int I3) requires #isConcrete(I2) andBool #isConcrete(I3) andBool notBool #isConcrete(I1) [simplification]
endmodule

module INFINITE-GAS-COMMON
    imports EVM

 // Generic rules

    rule (notBool (A andBool B)) andBool A => (notBool B) andBool A                      [simplification]
    rule #if B #then C +Int C1 #else C +Int C2 #fi => C +Int #if B #then C1 #else C2 #fi [simplification]

    rule I -Int I => 0              [simplification]
    rule (I1 -Int I2) +Int I2 => I1 [simplification]

    rule I1 +Int (I2 +Int I3) => (I1 +Int I2) +Int I3 [simplification]
    rule I1 +Int (I2 -Int I3) => (I1 +Int I2) -Int I3 [simplification]
    rule I1 -Int (I2 +Int I3) => (I1 -Int I2) -Int I3 [simplification]
    rule I1 -Int (I2 -Int I3) => (I1 -Int I2) +Int I3 [simplification]

 // Symbolic Gas

    syntax Int ::= #gas ( Int , Int , Int )  [function]  // startGas, nonMemory, memory
 //-----------------------------------------------------------------------------------

    syntax Int ::= #gas ( Int ) [function, functional, no-evaluators, klabel(infGas), symbol, smtlib(infGas)]
 // ---------------------------------------------------------------------------------------------------------
    rule #gas(_, _, _) => #gas(0)

    rule #gas(G) +Int G' => #gas(G +Int G') requires 0 <=Int G' orBool 0 -Int G' <Int #gas(G)  [simplification]
    rule G +Int #gas(G') => #gas(G +Int G') requires 0 <=Int G  orBool 0 -Int G  <Int #gas(G') [simplification]

    rule #gas(G) -Int G' => #gas(G -Int G') requires 0 <=Int G' andBool G' <Int #gas(G) [simplification]

    rule #gas(G) *Int G' => #gas(G *Int G') requires 0 <=Int G' [simplification]
    rule G *Int #gas(G') => #gas(G *Int G') requires 0 <=Int G  [simplification]

    rule #gas(G) /Int G' => #gas(G /Int G') requires 0  <Int G' andBool G' <Int #gas(G)  [simplification]
    rule G /Int #gas(G') => 0               requires 0 <=Int G  andBool G  <Int #gas(G') [simplification]

    rule #gas(#gas(G)) => #gas(G) [simplification]

    rule #gas(G) -Int #gas(G') => #gas(G -Int G') [simplification]

    rule minInt(#gas(G), #gas(G'))              => #gas(minInt(G, G'))              [simplification]
    rule #if B #then #gas(G) #else #gas(G') #fi => #gas(#if B #then G #else G' #fi) [simplification]

    rule #allBut64th(#gas(G)) => #gas(#allBut64th(G)) [simplification]

    rule #gas(_)  <Int #gas(_) => false [simplification]
    rule #gas(_) <=Int #gas(_) => true  [simplification]

    rule #gas(_)  <Int I => false requires I <=Int pow256 [simplification]
    rule #gas(_) <=Int I => false requires I <=Int pow256 [simplification]
    rule #gas(_) >=Int I => true  requires I <=Int pow256 [simplification]

    rule I  <Int #gas(_) => true requires I <=Int pow256 [simplification]
    rule I <=Int #gas(_) => true requires I <=Int pow256 [simplification]

    rule I +Int I' <=Int #gas(G) => true requires                     I <=Int #gas(G) andBool I' <=Int #gas(G) [simplification]
    rule I -Int I' <=Int #gas(G) => true requires                     I <=Int #gas(G) andBool I' <=Int #gas(G) [simplification]
    rule I *Int I' <=Int #gas(G) => true requires                     I <=Int #gas(G) andBool I' <=Int #gas(G) [simplification]
    rule I /Int I' <=Int #gas(G) => true requires I' =/=Int 0 andBool I <=Int #gas(G) andBool I' <=Int #gas(G) [simplification]

    rule #gas(G) <Int I +Int I' => false requires                     notBool (#gas(G) <Int I orBool #gas(G) <Int I') [simplification]
    rule #gas(G) <Int I -Int I' => false requires                     notBool (#gas(G) <Int I orBool #gas(G) <Int I') [simplification]
    rule #gas(G) <Int I *Int I' => false requires                     notBool (#gas(G) <Int I orBool #gas(G) <Int I') [simplification]
    rule #gas(G) <Int I /Int I' => false requires I' =/=Int 0 andBool notBool (#gas(G) <Int I orBool #gas(G) <Int I') [simplification]

    rule #gas(G) <=Int I +Int I' => false requires                     notBool (#gas(G) <=Int I orBool #gas(G) <=Int I') [simplification]
    rule #gas(G) <=Int I -Int I' => false requires                     notBool (#gas(G) <=Int I orBool #gas(G) <=Int I') [simplification]
    rule #gas(G) <=Int I *Int I' => false requires                     notBool (#gas(G) <=Int I orBool #gas(G) <=Int I') [simplification]
    rule #gas(G) <=Int I /Int I' => false requires I' =/=Int 0 andBool notBool (#gas(G) <=Int I orBool #gas(G) <=Int I') [simplification]

    rule minInt(G, G') <Int G''  => G <Int G'' orBool G' <Int G''  [simplification]
    rule G  <Int minInt(G', G'') => G  <Int G' andBool G  <Int G'' [simplification]
    rule G <=Int minInt(G', G'') => G <=Int G' andBool G <=Int G'' [simplification]

    rule 0 <=Int Csstore(_, _, _, _)       => true  [simplification]
    rule Csstore(_, _, _, _) <Int #gas(_)  => true  [simplification]
    rule #gas(_)  <Int Csstore(_, _, _, _) => false [simplification]
    rule #gas(_) >=Int Csstore(_, _, _, _) => true  [simplification]

    rule #gas(_) <Int Cmem(_, _)  => false [simplification]
    rule Cmem(_, _) <=Int #gas(_) => true  [simplification]

    rule 0 <=Int #allBut64th(G)       => true                          [simplification]
    rule #allBut64th(G) <Int #gas(G') => true requires G <Int #gas(G') [simplification]

    rule #gas(G1) +Int (G2 +Int G3) => (#gas(G1) +Int G2) +Int G3 [simplification]
    rule #gas(G1) +Int (G2 -Int G3) => (#gas(G1) +Int G2) -Int G3 [simplification]

endmodule
