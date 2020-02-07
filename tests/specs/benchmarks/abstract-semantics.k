requires "abstract-semantics-segmented-gas.k"
requires "evm-symbolic.k"
requires "ecrec-symbolic.k"

module ABSTRACT-SEMANTICS
  imports ABSTRACT-SEMANTICS-SEGMENTED-GAS
  imports EVM-SYMBOLIC
  imports ECREC-SYMBOLIC
  imports EVM

  // ########################
  // EXTCODESIZE
  // ########################

    rule <k> EXTCODESIZE ACCT => #extCodeSize(ACCT) ~> #push ... </k>  [trusted]

endmodule