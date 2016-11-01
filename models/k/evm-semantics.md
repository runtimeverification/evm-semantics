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
    imports EVM-PROGRAM-SYNTAX

    syntax AcctID ::= ".AcctID"
    configuration <T>
                    <processes>
                        <process multiplicity="*">
                            <pid> .PID </pid>
                            <k> $PGM:Program </k>
                            <wordStack> .WordStack </wordStack>
                            <localMem> .Map </localMem>
                        </process>
                    </processes>
                    <accounts>
                        <account multiplicity="*">
                            <acctID> .AcctID </acctID>
                            <program> .Program </program>
                            <balance> 0 </balance>
                        </account>
                    </accounts>
                  </T>

endmodule
```

Entire Program
--------------

```k
module EVM-PROGRAM
    imports EVM-CONFIGURATION
    imports EVM-STACK-SEMANTICS
    imports EVM-CALL-SYNTAX

    // result is calculated, put back on stack
    rule <k> (W:Int ~> #push) => . ... </k>
         <wordStack> WS => W : WS </wordStack>

    // these operations load elements from stack for calculation
    // notice that they all either leave stack size alone or decrease it
    rule <k> UOP:UnStackOp => UOP W0 ~> #push ... </k>
         <wordStack> W0 : WS => WS </wordStack>

    rule <k> BOP:BinStackOp => BOP W0 W1 ~> #push ... </k>
         <wordStack> W0 : W1 : WS => WS </wordStack>

    rule <k> TOP:TernStackOp => TOP W0 W1 W2 ~> #push ... </k>
         <wordStack> W0 : W1 : W2 : WS => WS </wordStack>

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
