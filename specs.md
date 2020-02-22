Statements for imperative proofs (SOLAR-style)
====================

```k
requires "evm.k"

module EVM-SPECS
    imports ID
    imports EVM

    configuration
      <kevm-specs>
        <kevm/>
        <commandVars> .Map </commandVars>
      </kevm-specs>

/*org.kframework.utils.errorsystem.KEMException: [Error] Critical: Cannot compute least sort of term:
  _;;__EVM-PROOFS( OR (R_K0:Id,{366}) OR (R_HOLE:Id,{80}),,  OR (R_K1:Ids,{80}) OR (R_HOLE:Ids,{366})).
Possible sorts are [Ids, KResult]
.All terms must have a unique least sort; consider assigning unique KLabels to overloaded productions.*/
    /*syntax Ids ::= List{Id,";;"}     [strict, cons("Ids1ListSyn"), hybrid]
    syntax EthereumCommand ::= "var" Ids
    rule var IDs => . //Required only to distinguish EVM-PROOFS vars from spec rule vars.
*/

    syntax EthereumCommand ::= "saveOutput" Id
    rule <k> saveOutput X => . ...</k>
         <output> OUT </output>
         <commandVars> VARS => VARS[X <- OUT] </commandVars>

    syntax EthereumCommand ::= "saveEthereum" Id
    rule <k> saveEthereum X => . ...</k>
         <ethereum> ETH </ethereum>
         <commandVars> VARS => VARS[X <- ETH] </commandVars>

    syntax EthereumCommand ::= "restoreEthereum" Id
    rule <k> restoreEthereum X => . ...</k>
         (<ethereum> _ </ethereum> => <ethereum> ETH </ethereum>)
         <commandVars>... X |-> ETH ...</commandVars>

    syntax KResult ::= ByteArray

    syntax Exp ::= "getVar" Id
                  | KResult
    rule <k> getVar X => VARS[X] ...</k>
         <commandVars> VARS </commandVars>

    syntax EthereumCommand ::= "assertEq" Exp Exp [strict]
    rule assertEq V1:KResult V2:KResult => .
      requires V1 ==K V2

    syntax EthereumCommand ::= "assumeEq" Exp Exp [strict]
    //ensures doesn't seem to have effect. Making this rule spec rule.
    /*rule assumeEq V1:KResult V2:KResult => .
      ensures V1 ==K V2*/

    //Copied from driver.md
    syntax EthereumCommand ::= "failure" String
 // -------------------------------------------------------
    rule <k>          failure _ => . ... </k>
    rule <k> #halt ~> failure _ => . ... </k>

endmodule
```
