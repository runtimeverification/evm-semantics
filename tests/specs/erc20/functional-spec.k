requires "verification.k"

module FUNCTIONAL-SPEC
    imports VERIFICATION

    claim #hashedLocation("Solidity", 2, OWNER SPENDER .IntList) => keccak(#bufStrict(32, SPENDER) +Bytes #bufStrict(32, keccak(#bufStrict(32, OWNER) +Bytes #bufStrict(32, 2)))) requires #rangeUInt(256, SPENDER) andBool #rangeUInt(256, OWNER)
endmodule
