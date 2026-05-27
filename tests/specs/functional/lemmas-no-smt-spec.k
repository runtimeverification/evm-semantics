requires "evm.md"
requires "lemmas/lemmas.k"

module VERIFICATION
    imports LEMMAS
    imports EVM

    syntax StepSort ::= Int | Bool
 // ------------------------------

    syntax KItem ::= runLemma ( StepSort ) [symbol(runLemma)]
                   | doneLemma( StepSort )
 // --------------------------------------
    rule <k> runLemma( T ) => doneLemma( T ) ... </k>

endmodule

module LEMMAS-NO-SMT-SPEC
    imports VERIFICATION

 // Arithmetic simplification
 // -------------------------

    claim [int-simpl-01]: <k> runLemma ( 5 +Int X )          => doneLemma ( X +Int 5          ) ... </k>
    claim [int-simpl-02]: <k> runLemma ( X -Int 5 )          => doneLemma ( X +Int (0 -Int 5) ) ... </k>
    claim [int-simpl-03]: <k> runLemma ( (X +Int 3) +Int 5 ) => doneLemma ( X +Int 8          ) ... </k>
    claim [int-simpl-04]: <k> runLemma ( 3 +Int (X +Int 5) ) => doneLemma ( X +Int 8          ) ... </k>
    claim [int-simpl-05]: <k> runLemma ( 5 -Int (X +Int 3) ) => doneLemma ( 2 -Int X          ) ... </k>
    claim [int-simpl-06]: <k> runLemma ( 5 +Int (3 +Int X) ) => doneLemma ( 8 +Int X          ) ... </k>
    claim [int-simpl-07]: <k> runLemma ( 5 +Int (3 -Int X) ) => doneLemma ( 8 -Int X          ) ... </k>
    claim [int-simpl-08]: <k> runLemma ( (5 -Int X) +Int 3 ) => doneLemma ( 8 -Int X          ) ... </k>
    claim [int-simpl-09]: <k> runLemma ( 5 -Int (3 +Int X) ) => doneLemma ( 2 -Int X          ) ... </k>
    claim [int-simpl-10]: <k> runLemma ( 5 -Int (3 -Int X) ) => doneLemma ( 2 +Int X          ) ... </k>
    claim [int-simpl-11]: <k> runLemma ( (X -Int 5) -Int 3 ) => doneLemma ( X -Int 8          ) ... </k>
    claim [int-simpl-12]: <k> runLemma ( 5 &Int (3 &Int X) ) => doneLemma ( 1 &Int X          ) ... </k>

 // Boolean simplification
 // ----------------------

    claim [bool-simpl-01]: <k> runLemma ( (B ==Bool false) ==Bool false ) => doneLemma ( B ) ... </k>

    // Awaiting Haskell backend updates
    claim [bool-simpl-02]: <k> runLemma ( bool2Word( B:Bool ) ==Int 1 )   => doneLemma ( B ==K true ) ... </k>
    claim [bool-simpl-03]: <k> runLemma ( 1 ==Int bool2Word( B:Bool ) )   => doneLemma ( B ==K true ) ... </k>

    claim [bool-eq-not-false]:
      <k> runLemma ( B:Bool ) => doneLemma ( false ) ... </k>
      requires notBool B

    claim [range-empty-neg-start]:
      <k> runLemma ( #range(B:Bytes, 0 -Int 1, 5) ==K .Bytes ) => doneLemma ( true ) ... </k>

    claim [range-empty-zero-width]:
      <k> runLemma ( #range(B:Bytes, 3, 0) ==K .Bytes ) => doneLemma ( true ) ... </k>

 // #asWord comparison — false cases
 // ---------------------------------

    // asWord-lt-false: #asWord(B) < X => false when X <=Int #asWord(B)
    // Here X=0, and 0 <=Int #asWord(B) is always true (asWord-lb), so no extra requires needed.
    claim [asword-lt-false]:
      <k> runLemma ( #asWord(B:Bytes) <Int 0 ) => doneLemma ( false ) ... </k>

    // asWord-le-false: #asWord(B) <=Int X => false when X <Int #asWord(B)
    claim [asword-le-false]:
      <k> runLemma ( #asWord(B:Bytes) <=Int 0 ) => doneLemma ( false ) ... </k>
      requires 0 <Int #asWord(B)

    // asword-eq-false: #asWord(B) ==Int X => false when X =/=Int #asWord(B)
    // X must be symbolic so asword-eq-num (requires concrete(X)) does not fire first.
    claim [asword-eq-false]:
      <k> runLemma ( #asWord(B:Bytes) ==Int X:Int ) => doneLemma ( false ) ... </k>
      requires X =/=Int #asWord(B)

 // eq-false-lt
 // -----------

    // eq-false-lt: A ==Int B => false when A < B is in path conditions (B concrete).
    claim [eq-false-lt]:
      <k> runLemma ( X:Int ==Int 42 ) => doneLemma ( false ) ... </k>
      requires X <Int 42

 // #powByteLen concrete comparison
 // --------------------------------

    // powByteLen-lt-concrete: CONST <Int #powByteLen(N) => true when both concrete.
    // Needed because 2^Int(8*N) is rewritten to #powByteLen(N) even for concrete N,
    // but #powByteLen has no-evaluators, so the comparison cannot self-evaluate.
    claim [powByteLen-lt-concrete]:
      <k> runLemma ( 31 <Int #powByteLen(32) ) => doneLemma ( true ) ... </k>

endmodule
