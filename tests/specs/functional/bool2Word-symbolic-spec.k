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

//
// Regression tests for symbolic-argument reasoning over bool2Word.
//
// Each of these claims sends a `bool2Word( <Bool expr> )` term whose
// argument is a *Bool expression* (not the literal `true`/`false`)
// and whose path condition entails — but is not syntactically equal to —
// that expression. The claim asserts the term reduces to 0/1.
//
// Under the legacy rules
//     rule bool2Word( true  ) => 1
//     rule bool2Word( false ) => 0
// pattern matching on the argument position does NOT consult the path
// condition / SMT, so symbolic Bool expressions that the path condition
// only *implies* (not equates to true/false) leave bool2Word(_) un-reduced
// and the implication check at the end fails.
//
// Under the side-conditioned rules
//     rule bool2Word( B ) => 1 requires         B ==Bool true
//     rule bool2Word( B ) => 0 requires notBool B ==Bool true
// the matcher binds B unconditionally and the side condition is discharged
// by Kore's full path-condition + SMT reasoning, so these claims pass.
//
module BOOL2WORD-SYMBOLIC-SPEC
    imports VERIFICATION

    // Free Bool variable, path condition equates it to true/false.
    // Both rule forms handle this — Kore canonicalizes `requires B`
    // into substitution B |-> true before reaching bool2Word.
    claim [b2w-var-true]:
        <k> runLemma ( bool2Word(B:Bool) ) => doneLemma( 1 ) ... </k>
        requires B

    claim [b2w-var-false]:
        <k> runLemma ( bool2Word(B:Bool) ) => doneLemma( 0 ) ... </k>
        requires notBool B

    // Argument is a Bool expression directly equated to itself in the
    // path condition. Original rules also pass because Kore can rewrite
    // the goal via the equality.
    claim [b2w-expr-eq-true]:
        <k> runLemma ( bool2Word(X >Int Y) ) => doneLemma( 1 ) ... </k>
        requires X >Int Y

    claim [b2w-expr-eq-false]:
        <k> runLemma ( bool2Word(X >Int Y) ) => doneLemma( 0 ) ... </k>
        requires notBool (X >Int Y)

    // Path condition IMPLIES the argument, but is not syntactically equal
    // to it: `X >Int 0` strictly implies `X >=Int 0`.
    // Original rules FAIL this — pattern-match on `true` in argument
    // position does not invoke SMT to discharge `X >=Int 0` under
    // path condition `X >Int 0`.
    // Side-conditioned rules PASS this — the side condition is checked
    // against the full path condition.
    claim [b2w-implied-true]:
        <k> runLemma ( bool2Word(X >=Int 0) ) => doneLemma( 1 ) ... </k>
        requires X >Int 0

    claim [b2w-implied-false]:
        <k> runLemma ( bool2Word(X <Int 0) ) => doneLemma( 0 ) ... </k>
        requires X >Int 0
endmodule
