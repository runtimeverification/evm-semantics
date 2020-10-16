requires "evm.md"

module INFINITE-GAS
    imports EVM


 // Symbolic Gas

    syntax Int ::= #gas ( Int , Int , Int )  [function]  // startGas, nonMemory, memory
 //-----------------------------------------------------------------------------------

 //
 // Infinite Gas
 // Here we use the construct `#gas` to count _up_ gas used instead of counting down.
 // This allows (i) computing final gas used, and (ii) never stopping because of out-of-gas.
 //

    syntax Int ::= #gas ( Int ) [function, functional, no-evaluators, klabel(infGas), symbol, smtlib(infGas)]
 // ---------------------------------------------------------------------------------------------------------
    rule #gas(_, _, _) => #gas(0)

    rule #gas(G) -Int G' => #gas(G +Int G') [simplification]
    rule #gas(G) +Int G' => #gas(G -Int G') [simplification]

    rule #gas(_)  <Int I => false requires I <=Int pow256 [simplification]
    rule #gas(_) <=Int I => false requires I <=Int pow256 [simplification]
    rule #gas(_) >=Int I => true  requires I <=Int pow256 [simplification]
    rule I <=Int #gas(_) => true  requires I <=Int pow256 [simplification]

    rule #gas(_)  <Int _I => false [concrete(_I), simplification]
    rule #gas(_) <=Int _I => false [concrete(_I), simplification]
    rule #gas(_) >=Int _I => true  [concrete(_I), simplification]
    rule _I <=Int #gas(_) => true  [concrete(_I), simplification]

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

    rule #gas(_) <Int Csstore(_, _, _, _) => false [simplification]
    rule #gas(_) <Int Cmem(_, _)          => false [simplification]

    rule #gas(_) >=Int Csstore(_, _, _, _) => true [simplification]

    rule Cmem(_, _) <=Int #gas(_) => true [simplification]
endmodule
