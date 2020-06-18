requires "edsl.md"

module EVM-SYMBOLIC     [symbolic]
    imports EVM
    imports EDSL

  // ########################
  // Ecrecover
  // ########################

    //Symbolic wrapper over the argument of #ecrec, no implementation.
    syntax Int ::= #symEcrec ( ByteArray )   [function]

    //Symbolic predicate representing whether output of #ecrec is empty. No implementation.
    syntax Bool ::= #ecrecEmpty( ByteArray ) [function]

    // Range for #symEcrec

    //case 0 is never wrapped into #symEcrec(), corresponds to #ecrecEmpty(DATA) == true
    rule 0 <Int   #symEcrec(DATA)             => true

    //that's because the result in concrete semantics is trimmed to Address range.
    rule          #symEcrec(DATA) <Int pow160 => true

    // Lemmas implied by the above, but still required to match side conditions of #padToWidth rule in lemmas.md
    // General range conversion lemmas like below are not an option, dramatic performance decrease:
    //    rule A < pow256 => true requires A < pow160
    rule 0 <=Int  #symEcrec(DATA)             => true
    rule          #symEcrec(DATA) <Int pow256 => true

  // ########################
  // Symbolic Gas
  // ########################

    syntax Int ::= #gas ( Int , Int , Int )  [function]  // startGas, nonMemory, memory
 // -----------------------------------------------------------------------------------

  // ########################
  // Symbolic Call
  // ########################

    syntax Int ::= #extCodeSize ( Int )  [function]
 // -----------------------------------------------

endmodule
