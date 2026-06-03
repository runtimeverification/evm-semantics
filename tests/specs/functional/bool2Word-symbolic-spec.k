requires "verification.k"

// Without the `b2w-true` / `b2w-false` simplification lemmas in lemmas.k,
// claims 5-6 fail: the path condition implies but does not equate the
// argument, so the function-rule matcher cannot discharge it without SMT.
// With the simplification lemmas, all six claims pass.
module BOOL2WORD-SYMBOLIC-SPEC
    imports VERIFICATION

    claim [b2w-var-true]:
        <k> runLemma ( bool2Word(B:Bool) ) => doneLemma( 1 ) ... </k>
        requires B

    claim [b2w-var-false]:
        <k> runLemma ( bool2Word(B:Bool) ) => doneLemma( 0 ) ... </k>
        requires notBool B

    claim [b2w-expr-eq-true]:
        <k> runLemma ( bool2Word(X >Int Y) ) => doneLemma( 1 ) ... </k>
        requires X >Int Y

    claim [b2w-expr-eq-false]:
        <k> runLemma ( bool2Word(X >Int Y) ) => doneLemma( 0 ) ... </k>
        requires notBool (X >Int Y)

    claim [b2w-implied-true]:
        <k> runLemma ( bool2Word(X >=Int 0) ) => doneLemma( 1 ) ... </k>
        requires X >Int 0

    claim [b2w-implied-false]:
        <k> runLemma ( bool2Word(X <Int 0) ) => doneLemma( 0 ) ... </k>
        requires X >Int 0

 // bool2Word
 // ---------

    // b2w-gt-zero, b2w-lt-b2w, b2w-band-one, b2w-band, b2w-mul-lt-l
    claim [b2w-01]:
      <k> runLemma (
            ( bool2Word( 0 <=Int X:Int ) &Int 1 ) *Int bool2Word( X <Int -5 ) <Int ( bool2Word( 5 <=Int X ) &Int bool2Word( X <=Int 10 ) )
          ) => doneLemma (
            5 <=Int X andBool X <=Int 10
          ) ... </k>

    // b2w-eq-zero, b2w-xor-zero, b2w-xor-one, b2w-xor, b2w-mul-eq-l
    claim [b2w-02]:
      <k> runLemma (
            ( bool2Word( 0 <=Int X:Int ) *Int ( 0 xorInt bool2Word( X <=Int 0 ) ) ) ==Int 1 xorInt ( bool2Word( X <=Int 0 ) xorInt bool2Word( X >=Int 0 ) )
          ) => doneLemma (
            true
          ) ... </k>

    // b2w-lt-one, b2w-bor-one, b2w-mul-le-l
    claim [b2w-03]:
      <k> runLemma (
            ( bool2Word ( 0 <=Int X:Int ) *Int bool2Word( 0 <Int X ) ) <Int 1 |Int bool2Word( X =/=Int X )
          ) => doneLemma (
            X <=Int 0
          ) ... </k>

    // b2w-gt-false, b2w-mul-lt-r
    claim [b2w-04]:
      <k> runLemma (
            ( bool2Word ( notBool X ) *Int 42 ) <Int bool2Word ( Y )
          ) => doneLemma (
            X andBool Y
          ) ... </k>

    // b2w-lt-true
    claim [b2w-05]:
      <k> runLemma (
            bool2Word ( _X ) *Int bool2Word ( _Y ) <Int 42
          ) => doneLemma (
            true
          ) ... </k>

endmodule
