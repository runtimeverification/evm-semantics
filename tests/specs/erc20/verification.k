requires "edsl.md"
requires "lemmas/lemmas.k"

module VERIFICATION
    imports VERIFICATION-HASKELL
    imports LEMMAS
    imports EVM
endmodule

module VERIFICATION-HASKELL [symbolic, kore]
    imports EDSL
endmodule
