requires "evm.md"
requires "lemmas/int-simplification.k"

module VERIFICATION
    imports EVM
    imports INT-SIMPLIFICATION

    rule #sizeWordStack(WS           , N) => #sizeWordStack(WS, 0) +Int N requires N =/=Int 0                [simplification]
    rule #sizeWordStack(WS [ I := _ ], N) => #sizeWordStack(WS, N)        requires I <Int #sizeWordStack(WS) [simplification]
    rule 0 <=Int #sizeWordStack(_ , 0)    => true                                                            [simplification]
    rule #sizeWordStack(_ , 0) <Int N     => false                        requires N <=Int 0                 [simplification]
endmodule
