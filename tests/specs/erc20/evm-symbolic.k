requires "edsl.md"

module EVM-SYMBOLIC     [symbolic]
    imports EVM
    imports EDSL

  // ########################
  // Ecrecover
  // todo move to ecrec-symbolic.k when K supports it.
  // ########################

    //Symbolic wrapper over the argument of #ecrec, no implementation.
    syntax Int ::= #symEcrec ( WordStack )   [function]

    //Symbolic predicate representing whether output of #ecrec is empty. No implementation.
    syntax Bool ::= #ecrecEmpty( WordStack ) [function]

    // Range for #symEcrec

    //case 0 is never wrapped into #symEcrec(), corresponds to #ecrecEmpty(DATA) == true
    rule 0 <Int   #symEcrec(_)             => true [simplification]

    //that's because the result in concrete semantics is trimmed to Address range.
    rule          #symEcrec(_) <Int pow160 => true [simplification]

    // Lemmas implied by the above, but still required to match side conditions of #padToWidth rule in lemmas.md
    // General range conversion lemmas like below are not an option, dramatic performance decrease:
    //    rule A < pow256 => true requires A < pow160
    rule 0 <=Int  #symEcrec(_)             => true [simplification]
    rule          #symEcrec(_) <Int pow256 => true [simplification]

  // ########################
  // Symbolic Call
  // ########################

 // PC helps to differentiate different calls to the same account.
 // TODO: include the calldata as the argument.
    syntax Bool ::= #callSuccess ( Int , Int )  [function]  // pc, accountTo
                  | #callFailure ( Int , Int )  [function]  // pc, accountTo
 // ------------------------------------------------------------------------

    syntax Int ::= #callResult ( Int , Int )  [function]  // pc, accountTo
 // ----------------------------------------------------------------------


    syntax Int ::= #extCodeSize ( Int )  [function]
 // -----------------------------------------------

 // ERC20 transfer(address,uint256)
 // pc, to addr
    syntax Bool ::= #tokenTransferCallSuccess ( Int , Int ) [function]
                  | #tokenTransferCallFailure ( Int , Int ) [function]
 // ------------------------------------------------------------------

 // 3rd argument: <timestamp> NOW </timestamp> variable hack to force to generate Z3 query
    syntax Int ::= #tokenTransferCallReturnSize  ( Int , Int , Int ) [function]
                 | #tokenTransferCallReturnValue ( Int , Int , Int ) [function]
 // ---------------------------------------------------------------------------

endmodule
