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

    // Fast smoke test: small concrete prefix + one JUMPDEST + small concrete suffix +
    // 32 symbolic bytes.  Use this for quick iteration during development.
    claim [compute-valid-jump-dests-fast]:
        <k> runLemma(#computeValidJumpDests(padRightBytes(.Bytes, 5, 0) +Bytes (91 : .Bytes) +Bytes padRightBytes(.Bytes, 5, 0) +Bytes #buf(32, INT_VAR)))
         => doneLemma(?_:Bytes)
        ... </k>
      requires #rangeUInt(256, INT_VAR)

    // Performance benchmark: large concrete prefix exposes O(N) overhead in any
    // per-iteration re-evaluation of lengthBytes(PGM).  Run without --haskell-logging
    // for true baseline timing.
    claim [compute-valid-jump-dests-perf]:
        <k> runLemma(#computeValidJumpDests(padRightBytes(.Bytes, 1000, 0) +Bytes (91 : .Bytes) +Bytes padRightBytes(.Bytes, 1000, 0) +Bytes #buf(32, INT_VAR)))
         => doneLemma(?_:Bytes)
        ... </k>
      requires #rangeUInt(256, INT_VAR)

endmodule
