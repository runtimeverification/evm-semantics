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
    //Dummy command at the beginning of <k> to ensure execution doesn't start with a spec rule 
    syntax EthereumCommand ::= "#dummy"
    rule #dummy => .

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

// Specifications expression language
// ======================================================================

    syntax KResult ::= ByteArray | StatusCode | List | Map

    syntax Exp ::= Exp "==S"  Exp  [seqstrict]
                 | Exp "=/=S" Exp  [seqstrict] 
                 | KResult

    rule R1:KResult ==S  R2:KResult => R1 ==K  R2
    rule R1:KResult =/=S R2:KResult => R1 =/=K R2

    // Boolean expressions
    syntax Exp ::= Exp "&&S" Exp [seqstrict, left]
                 > Exp "||S" Exp [seqstrict, left]

    rule R1:Bool &&S R2:Bool => R1 andBool R2
    rule R1:Bool ||S R2:Bool => R1 orBool R2

    syntax Exp ::= "#getStatusCode"
                 | "#getOutput"
                 | "#getLog"
                 | "#getRefund"
                 | #getStorage ( Int )
                 | #var( Id )
  
    rule <k> #getStatusCode => SC ...</k>
         <statusCode> SC </statusCode>

    rule <k> #getOutput => OUT ...</k>
         <output> OUT </output>

    rule <k> #getLog => L ...</k>
         <log> L </log>

    rule <k> #getRefund => R ...</k>
         <refund> R </refund>

    rule <k> #getStorage(ACCT_ID) => S ...</k>
         <acctID> ACCT_ID </acctID>
         <storage> S </storage>

    rule <k> #var(X) => VARS[X] ...</k>
         <commandVars> VARS </commandVars>

endmodule
```
