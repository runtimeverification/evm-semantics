requires "add-summary.k"
requires "addmod-summary.k"
requires "address-summary.k"
requires "and-summary.k"
requires "balance-normal-summary.k"
requires "balance-owise-summary.k"
requires "blockhash-summary.k"
requires "byte-summary.k"
requires "calldatacopy-summary.k"
requires "calldataload-summary.k"
requires "calldatasize-summary.k"
requires "caller-summary.k"
requires "chainid-summary.k"
requires "codecopy-summary.k"
requires "codesize-summary.k"
requires "coinbase-summary.k"
requires "difficulty-summary.k"
requires "div-summary.k"
requires "dup-summary.k"
requires "eq-summary.k"
requires "evmor-summary.k"
requires "exp-summary.k"
requires "gas-summary.k"
requires "gaslimit-summary.k"
requires "gasprice-summary.k"
requires "gt-summary.k"
requires "invalid-summary.k"
requires "iszero-summary.k"
requires "jumpdest-summary.k"
requires "log-summary.k"
requires "lt-summary.k"
requires "mcopy-summary.k"
requires "mload-summary.k"
requires "mod-summary.k"
requires "msize-summary.k"
requires "mstore-summary.k"
requires "mstore8-summary.k"
requires "mulmod-summary.k"
requires "not-summary.k"
requires "number-summary.k"
requires "origin-summary.k"
requires "pc-summary.k"
requires "pop-summary.k"
requires "prevrandao-summary.k"
requires "push-summary.k"
requires "pushzero-summary.k"
requires "return-summary.k"
requires "returndatacopy-summary.k"
requires "returndatasize-summary.k"
requires "revert-summary.k"
requires "sar-summary.k"
requires "sdiv-summary.k"
requires "selfbalance-summary.k"
requires "sgt-summary.k"
requires "sha3-summary.k"
requires "shl-summary.k"
requires "shr-summary.k"
requires "signextend-summary.k"
requires "sload-summary.k"
requires "slt-summary.k"
requires "smod-summary.k"
requires "sstore-summary.k"
requires "stop-summary.k"
requires "sub-summary.k"
requires "swap-summary.k"
requires "timestamp-summary.k"
requires "tload-summary.k"
requires "tstore-summary.k"
requires "undefined-summary.k"
requires "xor-summary.k"

module KEVM-SUMMARIES
    imports public ADD-SUMMARY
    imports public ADDMOD-SUMMARY
    imports public ADDRESS-SUMMARY
    imports public AND-SUMMARY
    imports public BALANCE-NORMAL-SUMMARY
    imports public BALANCE-OWISE-SUMMARY
    imports public BLOCKHASH-SUMMARY
    imports public BYTE-SUMMARY
    imports public CALLDATACOPY-SUMMARY
    imports public CALLDATALOAD-SUMMARY
    imports public CALLDATASIZE-SUMMARY
    imports public CALLER-SUMMARY
    imports public CHAINID-SUMMARY
    imports public CODECOPY-SUMMARY
    imports public CODESIZE-SUMMARY
    imports public COINBASE-SUMMARY
    imports public DIFFICULTY-SUMMARY
    imports public DIV-SUMMARY
    imports public DUP-SUMMARY
    imports public EQ-SUMMARY
    imports public EVMOR-SUMMARY
    imports public EXP-SUMMARY
    imports public GAS-SUMMARY
    imports public GASLIMIT-SUMMARY
    imports public GASPRICE-SUMMARY
    imports public GT-SUMMARY
    imports public INVALID-SUMMARY
    imports public ISZERO-SUMMARY
    imports public JUMPDEST-SUMMARY
    imports public LOG-SUMMARY
    imports public LT-SUMMARY
    imports public MCOPY-SUMMARY
    imports public MLOAD-SUMMARY
    imports public MOD-SUMMARY
    imports public MSIZE-SUMMARY
    imports public MSTORE-SUMMARY
    imports public MSTORE8-SUMMARY
    imports public MULMOD-SUMMARY
    imports public NOT-SUMMARY
    imports public NUMBER-SUMMARY
    imports public ORIGIN-SUMMARY
    imports public PC-SUMMARY
    imports public POP-SUMMARY
    imports public PREVRANDAO-SUMMARY
    imports public PUSH-SUMMARY
    imports public PUSHZERO-SUMMARY
    imports public RETURN-SUMMARY
    imports public RETURNDATACOPY-SUMMARY
    imports public RETURNDATASIZE-SUMMARY
    imports public REVERT-SUMMARY
    imports public SAR-SUMMARY
    imports public SDIV-SUMMARY
    imports public SELFBALANCE-SUMMARY
    imports public SGT-SUMMARY
    imports public SHA3-SUMMARY
    imports public SHL-SUMMARY
    imports public SHR-SUMMARY
    imports public SIGNEXTEND-SUMMARY
    imports public SLOAD-SUMMARY
    imports public SLT-SUMMARY
    imports public SMOD-SUMMARY
    imports public SSTORE-SUMMARY
    imports public STOP-SUMMARY
    imports public SUB-SUMMARY
    imports public SWAP-SUMMARY
    imports public TIMESTAMP-SUMMARY
    imports public TLOAD-SUMMARY
    imports public TSTORE-SUMMARY
    imports public UNDEFINED-SUMMARY
    imports public XOR-SUMMARY
    
    

endmodule