requires "evm.md"
requires "lemmas/lemmas.k"

module VERIFICATION
    imports EVM
    imports LEMMAS

    syntax StepSort ::= Bytes
 // -------------------------

    syntax KItem ::= runLemma ( StepSort ) [symbol(runLemma)]
                   | doneLemma( StepSort )
 // --------------------------------------
    rule <k> runLemma( T ) => doneLemma( T ) ... </k>

endmodule

module COMPUTE-VALID-JUMP-DESTS-SPEC
    imports VERIFICATION

    // Performance benchmark: concrete prefix, one JUMPDEST, concrete suffix, then 32 symbolic
    // bytes.  The #buf(32, INT_VAR) tail forces Haskell-backend symbolic evaluation rather
    // than pure LLVM concrete evaluation, exposing the O(N) overhead of re-evaluating
    // lengthBytes(PGM) on every loop iteration with the old definition.
    claim [compute-valid-jump-dests-perf]:
        <k> runLemma(#computeValidJumpDests(padRightBytes(.Bytes, 1000, 0) +Bytes (91 : .Bytes) +Bytes padRightBytes(.Bytes, 1000, 0) +Bytes #buf(32, INT_VAR)))
         => doneLemma(?_:Bytes)
        ... </k>
      requires #rangeUInt(256, INT_VAR)

endmodule
