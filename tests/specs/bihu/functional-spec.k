requires "verification.k"

module FUNCTIONAL-SPEC
    imports VERIFICATION

    claim #range( _MEM [ 96 := #padToWidth(32, #asByteStack(BS)) ], 96, 32) => #buf(32, BS) requires #rangeUInt(256, BS)

endmodule
