requires "evm-symbolic.k"

module ABSTRACT-SEMANTICS-SEGMENTED-GAS
  imports EVM
  imports EVM-SYMBOLIC

  // to avoid unnecessary case analyses
  claim <k> LT W0 W1 => bool2Word(W0  <Int W1) ~> #push ... </k> [trusted]
  claim <k> GT W0 W1 => bool2Word(W0  >Int W1) ~> #push ... </k> [trusted]
  claim <k> EQ W0 W1 => bool2Word(W0 ==Int W1) ~> #push ... </k> [trusted]
  claim <k> ISZERO W => bool2Word(W  ==Int 0 ) ~> #push ... </k> [trusted]

endmodule
