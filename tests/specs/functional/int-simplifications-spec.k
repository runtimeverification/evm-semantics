requires "verification.k"

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

 // Arithmetic cancellation
 // ------------------------

    claim [cancellation-01]:
      <k> runLemma (
            ( ( ( ( ( X +Int X ) -Int Y ) -Int ( X -Int Y ) ) -Int Y ) -Int ( X -Int Y ) )
          ) => doneLemma (
            0
          ) ... </k>

    claim [cancellation-02]:
      <k> runLemma (
            ( ( A +Int ( ( B -Int A ) +Int B ) ) -Int ( B +Int B ) )
          ) => doneLemma (
            0
          ) ... </k>

    claim [div-div]: <k> runLemma ( ( A /Int B ) /Int 1024 ) => doneLemma ( 0 ) ... </k>
        requires 0 <=Int A andBool 0 <Int B andBool A <Int ( 1024 *Int B )

 // Booleans
 // ---------

    claim [notBool-or]:
      <k> runLemma (
            notBool ( ( X <Int LOWER ) orBool ( UPPER <=Int X ) )
          ) => doneLemma (
            ( notBool ( X <Int LOWER ) ) andBool ( notBool ( UPPER <=Int X ) )
          ) ...
      </k>

    claim [notBool-and]:
      <k> runLemma (
            notBool ( ( LOWER <=Int X ) andBool ( X <Int UPPER ) )
          ) => doneLemma (
            ( notBool ( LOWER <=Int X ) ) orBool ( notBool ( X <Int UPPER ) )
          ) ...
      </k>

 // Comparisons
 // -----------

    claim [comp-norm-01]:
      <k> runLemma (
            ( ( 20 -Int ( 10 +Int X:Int ) ) -Int 5 ) +Int 3 <=Int 7
          ) =>
          doneLemma (
            1 <=Int X
          ) ...
      </k>

    claim [comp-norm-02]:
      <k> runLemma (
            ( ( 20 -Int ( 10 +Int X:Int ) ) -Int 5 ) +Int 3 <Int 7
          ) =>
          doneLemma (
            1 <Int X
          ) ...
      </k>

    claim [comp-norm-03]:
      <k> runLemma (
            ( ( 20 -Int ( 10 +Int X:Int ) ) -Int 5 ) +Int 3 >Int 7
          ) =>
          doneLemma (
            1 >Int X
          ) ...
      </k>

    claim [comp-norm-04]:
      <k> runLemma (
            ( ( 20 -Int ( 10 +Int X:Int ) ) -Int 5 ) +Int 3 >=Int 7
          ) =>
          doneLemma (
            1 >=Int X
          ) ...
      </k>

    claim [zero-lt-sub]: <k> runLemma ( 0  <Int A -Int B ) => doneLemma ( B  <Int A ) ... </k>
    claim [zero-le-sub]: <k> runLemma ( 0 <=Int A -Int B ) => doneLemma ( B <=Int A ) ... </k>
    claim [zero-gt-sub]: <k> runLemma ( 0  >Int A -Int B ) => doneLemma ( B  >Int A ) ... </k>
    claim [zero-ge-sub]: <k> runLemma ( 0 >=Int A -Int B ) => doneLemma ( B >=Int A ) ... </k>

    claim [sub-gt-zero]: <k> runLemma ( A -Int B  >Int 0 ) => doneLemma ( A  >Int B ) ... </k>
    claim [sub-ge-zero]: <k> runLemma ( A -Int B >=Int 0 ) => doneLemma ( A >=Int B ) ... </k>
    claim [sub-lt-zero]: <k> runLemma ( A -Int B  <Int 0 ) => doneLemma ( A  <Int B ) ... </k>
    claim [sub-le-zero]: <k> runLemma ( A -Int B <=Int 0 ) => doneLemma ( A <=Int B ) ... </k>

    claim [mul-lt-const]: <k> runLemma ( 36 *Int B  <Int 1728 ) => doneLemma ( B  <Int 48 ) ... </k>
    claim [mul-le-const]: <k> runLemma ( 36 *Int B <=Int 1728 ) => doneLemma ( B <=Int 48 ) ... </k>
    claim [mul-gt-const]: <k> runLemma ( 36 *Int B  >Int 1728 ) => doneLemma ( B  >Int 48 ) ... </k>
    claim [mul-ge-const]: <k> runLemma ( 36 *Int B >=Int 1728 ) => doneLemma ( B >=Int 48 ) ... </k>

    claim [const-gt-mul]: <k> runLemma ( 1728  >Int 36 *Int B ) => doneLemma ( 48  >Int B ) ... </k>
    claim [const-ge-mul]: <k> runLemma ( 1728 >=Int 36 *Int B ) => doneLemma ( 48 >=Int B ) ... </k>
    claim [const-lt-mul]: <k> runLemma ( 1728  <Int 36 *Int B ) => doneLemma ( 48  <Int B ) ... </k>
    claim [const-le-mul]: <k> runLemma ( 1728 <=Int 36 *Int B ) => doneLemma ( 48 <=Int B ) ... </k>

    claim [eq-neg]: <k> runLemma ( A ==Int -1 ) => doneLemma ( false ) ... </k>
        requires 0 <=Int A

    claim [nonneg-and-nonzero]: <k> runLemma ( 0 <Int X ) => doneLemma ( true ) ... </k>
        requires 0 <=Int X andBool notBool ( X ==Int 0 )

    claim [le-maxuint256]: <k> runLemma ( X <=Int maxUInt256 ) => doneLemma ( X <Int pow256 ) ... </k>

endmodule
