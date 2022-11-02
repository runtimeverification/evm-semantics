Scripting language for imperative specifications (SOLAR-style)
==============================================================

```k
requires "evm.md"

module EVM-IMP-SPECS
    imports ID
    imports EVM

    configuration
      <kevm-specs>
        <kevm/>
        <commandVars> .Map </commandVars>
      </kevm-specs>
```

Core specification language
---------------------------

```k
    syntax EthereumCommand ::= "#assert" Exp [strict]
                             | "#assertFailure" Exp
    rule <k> #assert R:Bool => . ... </k>
      requires R

    rule <k> #assert R:Bool => #assertFailure R ... </k>
      requires notBool R

    syntax EthereumCommand ::= "#assume" Exp [strict]

    //Adapted from driver.md `failure`
    syntax EthereumCommand ::= "#takeHalt" String
 // ---------------------------------------------
    rule <k>          #takeHalt _ => . ... </k>
    rule <k> #halt ~> #takeHalt _ => . ... </k>

    //Shortcut for #mkCall and required setup
    syntax EthereumCommand ::= "#mkCallShortcut" Id Int Int ByteArray Id
    rule <k> #mkCallShortcut V_CONF_BACKUP CALLER_ID ACCT_ID ARGS V_SAVEOUT_ID
          => #restoreEthereum V_CONF_BACKUP
          ~> #mkCall CALLER_ID ACCT_ID ACCT_ID PARSEDCODE 0 ARGS false
          ~> #takeHalt "failure"
          ~> #saveOutput V_SAVEOUT_ID
         ...
         </k>
        <acctID> ACCT_ID </acctID>
        <code> PARSEDCODE </code>

    //Dummy command at the beginning of <k> to ensure execution doesn't start with a spec rule 
    syntax EthereumCommand ::= "#dummy"
    rule <k> #dummy => . ... </k>
```

Configuration access commands
-----------------------------

```k
    syntax EthereumCommand ::= "#saveEthereum" Id
    rule <k> #saveEthereum X => . ... </k>
         <ethereum> ETH </ethereum>
         <commandVars> VARS => VARS[X <- ETH] </commandVars>

    syntax EthereumCommand ::= "#restoreEthereum" Id
    rule <k> #restoreEthereum X => . ... </k>
         (<ethereum> _ </ethereum> => <ethereum> ETH </ethereum>)
         <commandVars>... X |-> ETH ...</commandVars>

    syntax EthereumCommand ::= "#saveOutput" Id
    rule <k> #saveOutput X => . ... </k>
         <output> OUT </output>
         <commandVars> VARS => VARS[X <- OUT] </commandVars>

    syntax EthereumCommand ::= "#saveStorage" Int Id
    rule <k> #saveStorage ACCT_ID X => . ... </k>
         <acctID> ACCT_ID </acctID>
         <storage> S </storage>
         <commandVars> VARS => VARS[X <- S] </commandVars>

    syntax EthereumCommand ::= "#saveLog" Id
    rule <k> #saveLog X => . ... </k>
         <log> L </log>
         <commandVars> VARS => VARS[X <- L] </commandVars>

    syntax EthereumCommand ::= "#saveRefund" Id
    rule <k> #saveRefund X => . ... </k>
         <refund> R </refund>
         <commandVars> VARS => VARS[X <- R] </commandVars>
```

Specification expression language
---------------------------------

```k
    syntax KResult ::= ByteArray | StatusCode | List | Map

    syntax Exp ::= Exp "==S"  Exp  [seqstrict]
                 | Exp "=/=S" Exp  [seqstrict]
                 | Exp "+List" Exp [seqstrict]
                 | KResult

    rule <k> R1:KResult ==S  R2:KResult => R1 ==K  R2 ...</k>
    rule <k> R1:KResult =/=S R2:KResult => R1 =/=K R2 ...</k>
    rule <k> L1:List +List L2:List      => L1 L2      ...</k>

    // Boolean expressions
    syntax Exp ::= Exp "&&S" Exp [seqstrict, left]
                 > Exp "||S" Exp [seqstrict, left]

    rule <k> R1:Bool &&S R2:Bool => R1 andBool R2 ... </k>
    rule <k> R1:Bool ||S R2:Bool => R1 orBool R2  ... </k>

    // Configuration access and other helpers
    syntax Exp ::= "#getStatusCode"
                 | "#getOutput"
                 | "#getLog"
                 | "#getRefund"
                 | #getStorage ( Int )
                 | #var( Id )
                 | #sizeByteArrayExp ( Exp ) [strict]

    rule <k> #getStatusCode => SC ... </k>
         <statusCode> SC </statusCode>

    rule <k> #getOutput => OUT ... </k>
         <output> OUT </output>

    rule <k> #getLog => L ... </k>
         <log> L </log>

    rule <k> #getRefund => R ... </k>
         <refund> R </refund>

    rule <k> #getStorage(ACCT_ID) => S ... </k>
         <acctID> ACCT_ID </acctID>
         <storage> S </storage>

    rule <k> #var(X) => VARS[X] ... </k>
         <commandVars> VARS </commandVars>

    rule <k> #sizeByteArrayExp(WS:ByteArray) => #sizeByteArray(WS) ... </k>

endmodule
```
