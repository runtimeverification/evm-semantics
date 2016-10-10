---
title: K Model of EVM Execution Environment
geometry: margin=2.5cm
...


```k
module EVM-CONFIGURATION
    configuration <T>
                    <k> </k>

                    // currently executing EVM program
                    <callFrame> LocalState </callFrame>

                    // list of (FrameNumber, ID)
                    <callStack> .List </callStack>

                    // map from (FrameNumber, ID) |-> LocalState
                    <stackFrames> .Map </stackFrames>

                    // map from ID |-> AccountState
                    <worldState> .Map </worldState>
                  </T>
endmodule
```
