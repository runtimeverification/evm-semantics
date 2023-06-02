requires "verification.k"

module FUNCTIONAL-SPEC-SYNTAX
    imports VERIFICATION

endmodule

module FUNCTIONAL-SPEC
    imports FUNCTIONAL-SPEC-SYNTAX

    claim (#range( _MEM [ 96 := #padToWidth(32, #asByteStack(BS)) ], 96, 32))
           => (#buf(32, BS))
      requires #rangeUInt(256, BS)

endmodule
