requires "evm.md"
requires "lemmas/int-simplification.k"

module VERIFICATION
    imports EVM
    imports INT-SIMPLIFICATION

    rule #sizeWordStack(WS [ I := _ ]) => #sizeWordStack(WS) requires I <Int #sizeWordStack(WS) [simplification]
    rule 0 <=Int #sizeWordStack(_)     => true                                                  [simplification]
endmodule
