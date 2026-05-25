requires "edsl.md"
requires "lemmas/lemmas.k"

module VERIFICATION
    imports EDSL
    imports LEMMAS

    syntax StepSort ::= Int | Bool
 // ------------------------------

    syntax KItem ::= runLemma ( StepSort ) [symbol(runLemma)]
                   | doneLemma( StepSort )
 // --------------------------------------
    rule runLemma( T ) => doneLemma( T )

endmodule

// Claims 5-6 fail under the legacy `bool2Word(true) => 1` rules: the path
// condition implies but does not equate the argument, so the argument-position
// matcher cannot discharge it without SMT. Side-conditioned rules pass them.
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
endmodule
