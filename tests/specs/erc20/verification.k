requires "edsl.md"
requires "evm-symbolic.k"
requires "lemmas/lemmas.k"

module VERIFICATION
    imports VERIFICATION-HASKELL
    imports LEMMAS

endmodule

module VERIFICATION-HASKELL [symbolic, kore]
    imports EDSL
endmodule
