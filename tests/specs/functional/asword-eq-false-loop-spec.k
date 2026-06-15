requires "verification.k"

module ASWORD-EQ-FALSE-LOOP-SPEC
    imports VERIFICATION

    // Regression test for the non-terminating `asWord-eq-false` simplification loop
    // (evm-semantics #2859 / kontrol #1153). The offending rule has been removed from
    // `lemmas/evm-int-simplification.k`; these claims guard against it being reintroduced.
    //
    // The removed rule was:
    //     rule [asWord-eq-false]: #asWord(B) ==Int X => false requires X =/=Int #asWord(B) [simplification]
    // It is loop-safe ONLY when `X` is not itself an `#asWord(_)`. When BOTH sides of the
    // `==Int` are `#asWord` terms, applying it rewrites the equality into its own `requires`
    // with the two `#asWord` operands swapped — still `#asWord`-on-the-left — so it matches
    // again, swaps back, and recurses without bound (observed: one request looping >21 min at
    // 96% CPU, the rule nested 5,406 deep in the Kore simplifier).
    //
    // Each claim below asks the simplifier to evaluate an equality with `#asWord` on BOTH
    // sides, known unequal from the path condition. Expected result: `false`, discharged
    // against the path condition. If the looping rule is reintroduced, simplification of the
    // left-hand `runLemma` term loops and the proof TIMES OUT. `asWord-lt-false` /
    // `asWord-le-false` need no analogue: `<Int` / `<=Int` are antisymmetric, so their
    // swapped requires is a different, non-matching relation.

    // Minimal trigger: two symbolic byte-words, known unequal.
    claim [asword-eq-false-symmetric]:
      <k> runLemma ( #asWord ( B1:Bytes ) ==Int #asWord ( B2:Bytes ) ) => doneLemma ( false ) ... </k>
      requires #asWord ( B1 ) =/=Int #asWord ( B2 )

    // The shape actually observed in the CSE proofs: a plain word vs an `#asWord` over a
    // buffer expression (a `+Bytes` of symbolic operands does not reduce, so the right side
    // stays `#asWord`, keeping both operands `#asWord` exactly as in the captured loop term).
    claim [asword-eq-false-buffer]:
      <k> runLemma ( #asWord ( B1:Bytes ) ==Int #asWord ( B2:Bytes +Bytes B3:Bytes ) ) => doneLemma ( false ) ... </k>
      requires #asWord ( B1 ) =/=Int #asWord ( B2 +Bytes B3 )

    // Same hazard reached via `=/=Int` (which desugars to `notBool(_ ==Int_)`), the form in
    // which the loop term appeared inside another rule's requires.
    claim [asword-neq-true-symmetric]:
      <k> runLemma ( #asWord ( B1:Bytes ) =/=Int #asWord ( B2:Bytes ) ) => doneLemma ( true ) ... </k>
      requires #asWord ( B1 ) =/=Int #asWord ( B2 )

endmodule
