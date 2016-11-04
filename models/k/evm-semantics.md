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
    imports EVM-SIMULATION

    configuration <T>
                    <k> $PGM:EVMSimulation </k>
                    <accounts> .Map </accounts>
                  </T>

    rule <k> account:
             -   id: ACCT
             -   balance: BALANCE
             -   program: PROGRAM
             -   storage: STORAGE
             ACCTS:Accounts
             => #setStorage ACCT 0 STORAGE ~> ACCTS
             ...
         </k>
         <accounts> RHO:Map (. => ACCT |-> ( balance : BALANCE
                                           , program : PROGRAM
                                           , storage : .Map
                                           )
                            )
         </accounts>
         requires notBool (ACCT in keys(RHO))

    syntax KItem ::= "#setStorage" AcctID Word Storage

    rule (#setStorage ACCT N .) => .
    rule <k> #setStorage ACCT (N => N +Word 1) ((W0:Word => .) , WS) ... </k>
         <accounts>
            ...
            ACCT |-> ( balance : BALANCE
                     , program : PROGRAM
                     , storage : RHO:Map (. => N |-> W0)
                     )
            ...
         </accounts>

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
