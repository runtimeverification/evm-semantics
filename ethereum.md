Ethereum
========

Ethereum is using the EVM to drive updates over the world state.

```k
requires "evm.k"
requires "world-state.k"

module ETHEREUM
    imports EVM
    imports WORLD-STATE

    configuration <k> . </k>
                  initWorldState
                  initEvm
endmodule
```
