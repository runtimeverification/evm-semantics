requires "edsl.md"
requires "lemmas/lemmas.k"

module VERIFICATION
    imports EDSL
    imports LEMMAS

    syntax StepSort ::= Map | Bytes | Int | Bool
 // --------------------------------------------

    syntax KItem ::= runLemma ( StepSort )
                   | doneLemma( StepSort )
 // --------------------------------------
    rule runLemma( T ) => doneLemma( T )

endmodule

module INT-SIMPLIFICATIONS-SPEC
    imports VERIFICATION

 // minInt/maxInt

    claim [minInt-maxInt-01]:
      <k> runLemma ( minInt(A, _B) <Int maxInt(C, _D) ) => doneLemma ( true ) ... </k>
      requires A <Int C

    claim [minInt-maxInt-02]:
      <k> runLemma ( minInt(E +Int A, E +Int _B) <Int maxInt(F +Int C, F +Int _D) ) => doneLemma ( true ) ... </k>
      requires A <Int C andBool E <=Int F

    claim [minInt-maxInt-03]:
      <k> runLemma ( minInt(_A, B) <=Int maxInt(_C, D) ) => doneLemma ( true ) ... </k>
      requires B <=Int D

    claim [minInt-maxInt-04]:
      <k> runLemma ( minInt(_A +Int E, B +Int E) <=Int maxInt(_C +Int F, D +Int F) ) => doneLemma ( true ) ... </k>
      requires B <=Int D andBool E <=Int F

endmodule
