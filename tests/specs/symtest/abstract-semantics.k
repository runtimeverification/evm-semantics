requires "verification.k"

module ABSTRACT-SEMANTICS
  imports VERIFICATION

  // to avoid unnecessary case analyses
  rule <k> LT W0 W1 => bool2Word(W0  <Int W1) ~> #push ... </k> [trusted]
  rule <k> GT W0 W1 => bool2Word(W0  >Int W1) ~> #push ... </k> [trusted]
  rule <k> EQ W0 W1 => bool2Word(W0 ==Int W1) ~> #push ... </k> [trusted]
  rule <k> ISZERO W => bool2Word(W  ==Int 0 ) ~> #push ... </k> [trusted]

  rule <k> SHA256 => #end EVMC_SUCCESS ... </k>
       <callData> DATA </callData>
       <output> _ => #buf(32, #sha256(DATA)) </output>
    requires notBool #isConcrete(DATA)
    [trusted]

  // gas abstraction

  // see also verification.k

  rule <k> G':Int ~> #deductGas => . ... </k>
       <gas> #infGas(_ => PCOUNT, M => M +Int 1) </gas>
       <pc> PCOUNT </pc>
      [trusted, matching(#infGas)]

  rule <k> #refund G:Int => . ... </k>
       <gas> #infGas(N, M => M +Int 1) </gas>
      [trusted, matching(#infGas)]

  rule <k> GCALL:Int ~> #allocateCallGas => . ... </k>
       <callGas> _ => GCALL </callGas>
       requires #getKLabelString(GCALL) ==String "#infGas"
      [trusted]
  rule <k> GCALL:Int ~> #allocateCallGas => stuck(GCALL) ... </k>
       requires #getKLabelString(GCALL) =/=String "#infGas"
      [trusted]

  // TODO: fix factor out #else branch to a function and handle it separately
  rule <k> #allocateCreateGas => . ... </k>
       <gas>     #infGas(N,M) => #infGas(N, M +Int 1) </gas>
       <callGas> _            => #infGas(N, M +Int 2) </callGas>
      [trusted, matching(#infGas)]

endmodule
