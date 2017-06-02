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
endmodule
```
