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
                  | Exp "==S" Exp [seqstrict] 
                  | KResult
    rule <k> getVar X => VARS[X] ...</k>
         <commandVars> VARS </commandVars>

    rule R1:KResult ==S R2:KResult => R1 ==K R2

    syntax EthereumCommand ::= "#assert" Exp [strict]
                             | "#assertFailure" Exp
    rule #assert R:Bool => .
      requires R

    rule #assert R:Bool => #assertFailure R
      requires notBool R

syntax EthereumCommand ::= "#assume" Exp [strict]

    //Copied from driver.md
    syntax EthereumCommand ::= "failure" String
 // -------------------------------------------------------
    rule <k>          failure _ => . ... </k>
    rule <k> #halt ~> failure _ => . ... </k>

    //Shortcut for #mkCall and required setup
    syntax EthereumCommand ::= "#mkCallShortcut" Id Int Int ByteArray Id
    rule <k> #mkCallShortcut V_CONF_BACKUP CALLER_ID ACCT_ID ARGS V_SAVEOUT_ID
          => restoreEthereum V_CONF_BACKUP
          ~> #mkCall CALLER_ID ACCT_ID ACCT_ID PARSEDCODE 0 ARGS false
          ~> failure "failure"
          ~> saveOutput V_SAVEOUT_ID
        ...</k>
        <acctID> ACCT_ID </acctID>
        <code> PARSEDCODE </code>

    syntax Exp ::= #sizeWordStackExp ( Exp ) [strict]
    rule #sizeWordStackExp(WS:WordStack) => #sizeWordStack(WS)

endmodule
```
