requires "edsl.md"
requires "lemmas/lemmas.k"

module VERIFICATION
    imports EDSL
    imports LEMMAS

endmodule

module EVM-INT-SIMPLIFICATIONS-SPEC
    imports VERIFICATION

 // up/Int
 // ------

    claim [upInt-01]: ( ((X up/Int Y) *Int Y) <Int X +Int Z )
                           => ( true )
                          requires 0 <Int Y andBool Y <=Int Z

    claim [upInt-refl-lt]: ( ((X up/Int Y) *Int Y) <Int X )
                            => ( false )
                           requires 0 <Int Y

endmodule
