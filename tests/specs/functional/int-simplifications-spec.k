requires "edsl.md"
requires "lemmas/lemmas.k"

module VERIFICATION
    imports EDSL
    imports LEMMAS
endmodule

module INT-SIMPLIFICATIONS-SPEC
    imports VERIFICATION

 // minInt/maxInt

    claim [minInt-maxInt-01]: minInt(A, _B)                <Int maxInt(C, _D)               => true requires A <Int C
    claim [minInt-maxInt-02]: minInt(E +Int A, E +Int _B)  <Int maxInt(F +Int C, F +Int _D) => true requires A <Int C andBool E <=Int F
    claim [minInt-maxInt-03]: minInt(_A, B)               <=Int maxInt(_C, D)               => true requires B <=Int D
    claim [minInt-maxInt-04]: minInt(_A +Int E, B +Int E) <=Int maxInt(_C +Int F, D +Int F) => true requires B <=Int D andBool E <=Int F

endmodule
