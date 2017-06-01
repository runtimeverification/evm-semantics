// EVM Semantics
// =============


requires "execution.k"
requires "world-state.k"


// We need to define the configuration before defining the semantics of any rules
// which span multiple cells.


module EVM
    imports EVM-WORLD-STATE-INTERFACE
    imports EVM-EXECUTION

    configuration <id> .AcctID </id>
                  initEvmCell
                  initWorldStateCell(Init)
endmodule

