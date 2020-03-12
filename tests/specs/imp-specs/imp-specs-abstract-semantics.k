requires "evm-imp-specs.k"

module IMP-SPECS-ABSTRACT-SEMANTICS
  imports EVM-IMP-SPECS

  rule #assume R:Bool => .
    ensures R
    [trusted]

endmodule
