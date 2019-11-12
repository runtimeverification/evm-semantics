requires "edsl.k"

module VERIFICATION
    imports EDSL

    syntax ByteArray ::= "#generatedCode" [function]

    syntax Map ::= "#mapWithCode" [function]

    rule I -Int 0 => I

    rule 0 +Int I => I

    rule I +Int 0 => I

    rule chop(I) => I requires 0 <=Int I andBool I <Int pow256

    rule #sizeByteArray(#generatedCode) => 0

    rule #sizeWordStack ( WS , N:Int ) => N +Int #sizeWordStack ( WS , 0 )
      requires N =/=K 0

    rule 0 <=Int #sizeWordStack ( _ , _ ) => true [smt-lemma]

endmodule
