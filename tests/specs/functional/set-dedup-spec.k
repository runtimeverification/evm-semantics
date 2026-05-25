requires "evm.md"
requires "lemmas/lemmas.k"

module VERIFICATION
    imports LEMMAS
    imports EVM

    syntax StepSort ::= Int | Bool | Set
 // -------------------------------------

    syntax KItem ::= runLemma ( StepSort ) [symbol(runLemma)]
                   | doneLemma( StepSort )
 // --------------------------------------
    rule <k> runLemma( T ) => doneLemma( T ) ... </k>

endmodule

module SET-DEDUP-SPEC
    imports VERIFICATION

 // Set deduplication via |Set and membership
 // ------------------------------------------
 // These claims test the rule:
 //   rule S:Set |Set SetItem(X:Int) => S requires X in S [simplification]
 // together with the supporting membership rules that let the `X in S` side
 // condition discharge when S is written in |Set form.

    // Basic: one duplicate concrete element
    claim [set-dedup-01]:
      <k> runLemma ( A:Set |Set SetItem(1) |Set SetItem(1) )
       => doneLemma ( A:Set |Set SetItem(1) ) ... </k>

    // Two distinct elements, one of which is duplicated
    claim [set-dedup-02]:
      <k> runLemma ( A:Set |Set SetItem(1) |Set SetItem(2) |Set SetItem(1) )
       => doneLemma ( A:Set |Set SetItem(1) |Set SetItem(2) ) ... </k>

    // Both elements are duplicated
    claim [set-dedup-03]:
      <k> runLemma ( A:Set |Set SetItem(1) |Set SetItem(2) |Set SetItem(1) |Set SetItem(2) )
       => doneLemma ( A:Set |Set SetItem(1) |Set SetItem(2) ) ... </k>

    // Duplicate appears after other elements (tests deeper membership check)
    claim [set-dedup-04]:
      <k> runLemma ( A:Set |Set SetItem(1) |Set SetItem(2) |Set SetItem(3) |Set SetItem(1) )
       => doneLemma ( A:Set |Set SetItem(1) |Set SetItem(2) |Set SetItem(3) ) ... </k>

endmodule
