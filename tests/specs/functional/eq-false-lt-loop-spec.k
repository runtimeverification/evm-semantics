requires "verification.k"

module EQ-FALSE-LT-LOOP-SPEC
    imports VERIFICATION

    // Regression exemplar for the SECOND CSE non-termination layer (evm-semantics #2859 / kontrol #1153),
    // the one that remains after `asWord-eq-false` is removed. See `evm-semantics-cse-loop-change-request.md`.
    //
    // HOW THIS WAS FOUND: rebuilding KEVM with `asWord-eq-false` deleted (branch `asword-eq-false-loop-fix`,
    // == kontrol-side "variant A") does NOT stop the CSE proofs hanging — proof #4
    // `ArithmeticCallTest.test_double_add_sub_external` still spins >25 min in one `execute` request. The
    // loop simply RELOCATES. Server-side context logging of the hanging request shows two rules dominating,
    // ~16-17k attempts each, in two different engines under the same execute request:
    //
    //   * booster > execute > simplify > … > [eq-false-lt] > smt        (15 865 attempts)
    //       rule [eq-false-lt]: A:Int ==Int B:Int => false requires A <Int B [simplification, concrete(B)]
    //   * kore > execute > constraint > term:90151e4 > <AccountCellMap #Ceil> > success   (17 082 attempts,
    //       re-firing on the SAME constraint term)
    //
    // MECHANISM (a two-engine fixpoint failure, NOT a single self-loop like asWord-eq-false):
    //   1. `#Ceil(<accounts> AccountCellMap)` definedness requires the account ids be DISTINCT, i.e. it emits
    //      predicates of the form `ACCOUNT_ID ==Int <concrete account address> => false`.
    //   2. `eq-false-lt` (concrete RHS) is invited to discharge each one via its side condition
    //      `ACCOUNT_ID <Int <concrete address>`. With ACCOUNT_ID a symbolic account id constrained only to a
    //      range (e.g. `[0, pow160)`) that does NOT decide the comparison, SMT returns (Sat,Sat) —
    //      UNDETERMINED (2 518 such verdicts captured). The rule cannot fire and the predicate cannot reduce.
    //   3. Because the account-distinctness predicate never simplifies to a stable form, the Kore constraint
    //      simplifier never reaches a fixpoint and re-evaluates the AccountCellMap `#Ceil` on the same term
    //      thousands of times — each pass paying a fresh ~500 ms undetermined SMT round-trip per account id.
    //
    // The captured concrete address is `645326474426547203313410069153905908525362434349` (a 160-bit value);
    // the symbolic ids were CALLER_ID, ORIGIN_ID, and the deployed-contract ids.
    //
    // SCOPE / CAVEAT — READ BEFORE RELYING ON THIS:
    //   The faithful trigger is the INTERACTION of AccountCellMap definedness with `eq-false-lt`, driven by
    //   the Kore constraint simplifier's lack of a fixpoint guard. A bare `runLemma(ACCT ==Int <concrete>)`
    //   (claim 1 below) reproduces the EXPENSIVE-UNDETERMINED-SMT step but will most likely return the term
    //   undetermined ONCE rather than spin, because the AccountCellMap `#Ceil` that re-presents the predicate
    //   is absent. Claim 2 adds a two-account `<accounts>` cell so the definedness machinery is in play; this
    //   is the closer reproduction, but whether it spins depends on the backend's constraint-simplification
    //   fixpoint behaviour, which is the real defect. Please run BOTH on the buggy build and report which
    //   actually loops; the primary recommendation to the team is a backend fixpoint/termination guard plus
    //   making `eq-false-lt` cheap (or skipped) when `A <Int B` is undetermined — not a lemma deletion.

    // Claim 1 — the eq-false-lt undetermined-SMT step in isolation (the per-pass cost of the loop).
    // Exactly the captured comparison: symbolic account id vs the concrete address, range-bounded so that
    // `ACCT_ID <Int 645…349` is undetermined.
    claim [eq-false-lt-undetermined-acctid]:
      <k> runLemma ( ACCT_ID:Int ==Int 645326474426547203313410069153905908525362434349 )
       => doneLemma ( ?_RESULT:Bool ) ... </k>
      requires 0 <=Int ACCT_ID andBool ACCT_ID <Int pow160

    // Claim 2 — closer reproduction: two symbolic-id accounts in the <accounts> cell, so evaluating the
    // configuration's definedness invokes the AccountCellMap `#Ceil` that emits the account-distinctness
    // predicate `ACCT_ID_1 ==Int ACCT_ID_2 => false`, which `eq-false-lt` then tries (and fails) to discharge.
    // Both ids are range-bounded but unordered, so the distinctness comparison is undetermined — the captured
    // shape. (Adjust the cell context to match the project's VERIFICATION module if `<accounts>` is wrapped.)
    claim [eq-false-lt-acctmap-definedness]:
      <k> runLemma ( .Bytes ) => doneLemma ( .Bytes ) ... </k>
      <accounts>
        <account> <acctID> ACCT_ID_1:Int </acctID> ... </account>
        <account> <acctID> ACCT_ID_2:Int </acctID> ... </account>
        ...
      </accounts>
      requires 0 <=Int ACCT_ID_1 andBool ACCT_ID_1 <Int pow160
       andBool 0 <=Int ACCT_ID_2 andBool ACCT_ID_2 <Int pow160

endmodule
