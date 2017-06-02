Ethereum
========

Ethereum is using the EVM to drive updates over the world state.

```k
requires "evm.k"
requires "evm-dasm.k"
requires "world-state.k"

module ETHEREUM
    imports EVM
    imports EVM-DASM
    imports WORLD-STATE

    configuration <ethereum>
                    <k> . </k>
                    initEvmCell
                    initWorldStateCell
                  </ethereum>

    syntax AcctID ::= Word
    syntax Code   ::= Map
    syntax MsgID  ::= Word

    syntax InternalOp ::= "#pushResponse"
 // -------------------------------------
    rule <op> #pushResponse => RESPONSE ~> #push ... </op>
         <control> #response RESPONSE => . </control>

 // ------------------------------
    rule <op> SLOAD INDEX => #pushResponse ... </op>
         <id> ACCT </id>
         <control> . => #getAccountStorage ACCT INDEX </control>

    rule <op> SSTORE INDEX VALUE => . ... </op>
         <id> ACCT </id>
         <control> . => #setAccountStorage ACCT INDEX VALUE </control>
endmodule
```
