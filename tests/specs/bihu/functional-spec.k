requires "verification.k"

module FUNCTIONAL-SPEC-SYNTAX
    imports VERIFICATION

    syntax KItem ::= runLemma ( Step ) | doneLemma ( Step )
 // -------------------------------------------------------
    rule <k> runLemma(S) => doneLemma(S) ... </k>

    syntax Step ::= Bytes | Int | Bool
 // ----------------------------------

endmodule

module FUNCTIONAL-SPEC
    imports FUNCTIONAL-SPEC-SYNTAX

    claim <k> runLemma(#range( _MEM [ 96 := #padToWidth(32, #asByteStack(BS)) ], 96, 32))
           => doneLemma(#buf(32, BS)) ... </k>
      requires #rangeUInt(256, BS)

endmodule
