requires "evm-symbolic.k"

module ABSTRACT-SEMANTICS-SEGMENTED-GAS
  imports EVM
  imports EVM-SYMBOLIC

  // to avoid unnecessary case analyses
  claim <k> LT W0 W1 => bool2Word(W0  <Int W1) ~> #push ... </k> [trusted]
  claim <k> GT W0 W1 => bool2Word(W0  >Int W1) ~> #push ... </k> [trusted]
  claim <k> EQ W0 W1 => bool2Word(W0 ==Int W1) ~> #push ... </k> [trusted]
  claim <k> ISZERO W => bool2Word(W  ==Int 0 ) ~> #push ... </k> [trusted]

  // ########################
  // Segmented gas representatioon - #gas construct
  // ########################

  // accumulate the gas cost and never run out of gas
  claim <k> MEM' ~> #deductMemoryGas => . ... </k>
       <gas> #gas(INITGAS, NONMEM, MEM) => #gas(INITGAS, NONMEM, MEM +Int MEM') </gas>
       <callGas> _ => #gas(INITGAS, NONMEM, MEM) </callGas>
    [trusted, matching(#gas)]

  //Will run only if rule above doesn't match
  claim <k> G ~> #deductGas => . ... </k>
       <gas> #gas(INITGAS, NONMEM, MEM) => #gas(INITGAS, NONMEM +Int G, MEM) </gas>
       <callGas> _ => #gas(INITGAS, NONMEM, MEM) </callGas>
    [trusted, matching(#gas)]

endmodule
