---
title: K Model of EVM Execution Environment
geometry: margin=2.5cm
...


```k
requires "evm-syntax.k"
```


Configuration
=============

We need to define the configuration before defining the semantics of any rules
which span multiple cells.

```k
module EVM-CONFIGURATION
    imports EVM-SYNTAX

    configuration <T>
                    <k> $PGM:EVMSimulation </k>
                    <accounts>
                        <account multiplicity="*">
                            <acctID> 0 </acctID>
                            <program> .Map </program>
                            <storage> .Map </storage>
                        </account>
                    </accounts>
                  </T>
endmodule
```

Loading World Definition
------------------------

This module just takes the parsed world definition (list of accounts and account
to start with) and loads it all into the correct cells of the configuration.

```k
module EVM-SEMANTICS
    imports EVM-CONFIGURATION

    syntax KItem ::= Account | Accounts | EVMSimulation

    rule ACCTS:Accounts START ACCTID => ACCTS ~> ACCTID
    rule ACCT:Account ACCTS:Accounts => ACCT ~> ACCTS
    rule .Accounts => .

    syntax KItem ::= "#setStorage" AcctID Int Storage
                   | "#setProgram" AcctID Int Program

    rule <k> account:
             -   id: ACCT
             -   balance: BALANCE
             -   program: PROGRAM
             -   storage: STORAGE
             => #setStorage ACCT 0 STORAGE ~> #setProgram ACCT 0 PROGRAM
             ...
         </k>
         <accounts>
            ...
            (.Bag => <account>
                    <acctID> ACCT </acctID>
                    <program> .Map </program>
                    <storage> .Map </storage>
                  </account>)
         </accounts>

    rule (#setStorage ACCT N .Storage) => .
    rule <k> #setStorage ACCT (N => N +Int 1) (W0:Word , WS => WS) ... </k>
         <account>
            <acctID> ACCT </acctID>
            <storage> STORAGE:Map (. => N |-> W0) </storage>
            ...
         </account>

    rule (#setProgram ACCT N .Program) => .
    rule <k> #setProgram ACCT (N => N +Int 1) (OpCode:OpCode ; Program => Program) ... </k>
         <account>
            <acctID> ACCT </acctID>
            <program> STORAGE:Map (. => N |-> OpCode) </program>
            ...
         </account>

endmodule
```

```
module EVM-PROGRAM
    imports EVM-CONFIGURATION
    imports EVM-STACK-SEMANTICS
    imports EVM-CALL-SYNTAX

    // result is calculated, put back on stack
    rule <k> (W:Int ~> #push) => . ... </k>
         <wordStack> WS => W : WS </wordStack>

    // these operations load elements from stack for calculation
    // notice that they all either leave stack size alone or decrease it
    // this can push the stackSize past MAX_STACK_SIZE
    rule <k> PUSH W => stackSize(WS) ~> #checkStackSize ~> W ~> #push ... </k>
         <wordStack> WS </wordStack>

    // load/store elements in memory
    rule <k> MLOAD => . ... </k>
         <wordStack> W0 : WS => M : WS </wordStack>
         <localMem> ... W0 |-> M ... </localMem>

    rule <k> MLOAD => . ... </k>
         <wordStack> W0 : WS => 0 : WS </wordStack>
         <localMem> Rho:Map </localMem>
         requires notBool (W0 in keys(Rho))

    rule <k> MSTORE => . ... </k>
         <wordStack> W0 : W1 : WS => WS </wordStack>
         <localMem> ... W0 |-> (_ => W1) ... </localMem>

    rule <k> MSTORE => . ... </k>
         <wordStack> W0 : W1 : WS => WS </wordStack>
         <localMem> Rho:Map (.Map => W0 |-> W1) </localMem>
         requires notBool (W0 in keys(Rho))

    // call another process
    rule <k> CALL => #gatherArgs ARG0 ARGN 0 ~> #mkCall DEST .Map ~> #recieveReturn RET0 RETN ... </k>
         <wordStack> DEST : ETHER : ARG0 : ARGN : RET0 : RETN : WS => WS </wordStack>

    rule <k> #gatherArgs (ARG0 => ARG0 +Word 1) ARGN (N => N +Word 1) ~> #mkCall DEST (RHO:Map (.Map => N |-> M)) ...  </k>
         <localMem> ... ARG0 |-> M ... </localMem>
         requires ARG0 <Int ARGN

    rule <k> #gatherArgs (ARG0 => ARG0 +Word 1) ARGN (N => N +Word 1) ~> #mkCall DEST (RHO:Map (.Map => N |-> 0)) ...  </k>
         <localMem> LM </localMem>
         requires (ARG0 <Int ARGN) andBool (notBool (N in keys(LM)))

    rule #gatherArgs ARG0 ARGN N => .
         requires ARG0 >=Int ARGN
endmodule
```
