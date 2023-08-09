requires "foundry.md"

module NORMALIZATION-LEMMAS
    imports FOUNDRY

    rule A *Int B => B *Int A [concrete(A), symbolic(B), simplification(40)]

endmodule
