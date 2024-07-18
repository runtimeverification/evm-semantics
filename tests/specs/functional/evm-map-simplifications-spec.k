requires "edsl.md"

module VERIFICATION
    imports EDSL

    syntax StepSort ::= Map | Bytes | Int | Bool
 // --------------------------------------------

    syntax KItem ::= runLemma ( StepSort ) [symbol(runLemma)]
                   | doneLemma( StepSort )
 // --------------------------------------
    rule runLemma( T ) => doneLemma( T )

    syntax KItem ::= runLemmaWithStorage ( StepSort ) [symbol(runLemmaWithStorage)]
                   | doneLemmaWithStorage( StepSort )
 // -------------------------------------------------------------------------------
    rule [match-storage-concrete-keys]:
      <k> runLemmaWithStorage( T ) =>
          doneLemmaWithStorage( T ) ... </k>
      <accounts>
        <account>
            <acctID> 1 </acctID>
            <storage>
              (1 |-> X1)
              (2 |-> X2)
              ...
            </storage>
            ...
         </account>
         ...
      </accounts>

    // rule [match-storage-concrete-and-symbolic-keys]:
    //   <k> runLemmaWithStorage( T ) =>
    //       doneLemmaWithStorage( T ) ... </k>
    //   <accounts>
    //     <account>
    //         <acctID> 1 </acctID>
    //         <storage>
    //           (1 |-> 1)
    //           (2 |-> 2)
    //           (K |-> V)
    //           ...
    //         </storage>
    //         ...
    //      </account>
    //      ...
    //   </accounts>

endmodule

module EVM-MAP-SIMPLIFICATIONS-SPEC
    imports VERIFICATION

    claim [test-map-match]:
      <k> runLemmaWithStorage (
        X:Int
      ) => doneLemmaWithStorage (
        X
      ) ... </k>
      <accounts>
        <account>
            <acctID> 1 </acctID>
            <storage>
              (1 |-> 1)
              (2 |-> 2)
              ...
            </storage>
            ...
          </account>
      </accounts>


    claim [test-map-unify-cstr-empty]:
      <k> runLemma (
        (K |-> V ) .Map ==K M2:Map
      ) => doneLemma (
        `Map:lookup`(M2:Map, K) ==K V andBool .Map ==K M2 [ K <- undef ]
      ) ... </k>

    claim [test-map-unify-cstr]:
      <k> runLemma (
        (K |-> V ) M1:Map ==K M2:Map
      ) => doneLemma (
        `Map:lookup`(M2:Map, K) ==K V andBool M1 ==K M2 [ K <- undef ]
      ) ... </k>


    claim [map-unification-aux-01]:
      <k> runLemma (
        2 in_keys ((0 |-> X0) (1 |-> X1) (2 |-> X2) (3 |-> X3) M1_REST:Map)
      ) => doneLemma (
        true
      ) ... </k>

    claim [map-unification-concrete-reorder-naked]:
      <k> runLemma (
        (0 |-> X0) (1 |-> X1) (2 |-> X2) M1_REST:Map
      ) => doneLemma (
        (2 |-> X2) (1 |-> X1) (0 |-> X0) M1_REST:Map
      ) ... </k>

    claim [map-unification-concrete-reorder-eqK]:
      <k> runLemma (
        (0 |-> X0) (1 |-> X1) (2 |-> X2) M1_REST:Map ==K (2 |-> X2) (1 |-> X1) (0 |-> X0) M1_REST:Map
      ) => doneLemma (
        true
      ) ... </k>

    claim [map-unification-var-and-concrete-reorder-eqK]:
      <k> runLemma (
        (K |-> X0) (1 |-> X1) (2 |-> X2) M1_REST:Map ==K (K |-> X0) (2 |-> X2) (1 |-> X1) M1_REST:Map
      ) => doneLemma (
        true
      ) ... </k>

endmodule
