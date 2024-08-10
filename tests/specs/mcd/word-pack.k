requires "evm-types.md"

    //
    // The Solidity compiler sometimes packs together multiple arguments into one storage location, for optimized reads/writes.
    // Because the packed variables are all smaller than a `uint256`, they can fit into one word.
    // If you use the pattern `SOMETHING ==K #WordPack*(ARG1, ..., ARGN)` in your side-conditions, you're actually making several assertions about `SOMETHING` and `ARG1 ... ARGN`.
    // First, you're asserting that each `ARGi` can be unpacked from the variable `SOMETHING` using the correct accessors.
    // Second, you're asserting that `SOMETHING` contains no other values than the packed `ARGi` (so we add a range condition to `SOMETHING`).
    // This allows us to turn the side-condition SOMETHING ==K #WordPack*(ARG1, ..., ARGN)` into the more useful side-conditions `ARG1 ==K access1(SOMETHING) andBool ... andBool ARGN ==K accessN(SOMETHING)`.
    // The arguments are packed in reverse order, so that the highest bits are set by the last argument.
    //
    // When updating variables which originally contained `WordPack*`, the Solidity compiler will mask the original value everywhere _except_ where you're updating.
    // Then the update will be bitwise `|Int` with the masked value, and the new value written back.
    // Here we provide the masks which are used by the Solidity compiler, and rules which fold these bitwise updates back up into semantic `#WordPack*` arguments for the purposes of matching the RHS of proofs.
    //

module WORD-PACK
    imports EVM-TYPES
    imports BUF

    syntax Int ::= #WordPackUInt48UInt48     (       Int , Int ) [function]
                 | #WordPackAddrUInt48UInt48 ( Int , Int , Int ) [function]
                 | #WordPackAddrUInt8        (       Int , Int ) [function]
 // -----------------------------------------------------------------------------------------------------------------
    rule #WordPackUInt48UInt48     (        UINT48_1 , UINT48_2 ) => #asWord (       #buf(20, 0) +Bytes #buf(6, UINT48_2) +Bytes #buf(6, UINT48_1) ) requires #rangeUInt(48, UINT48_1) andBool #rangeUInt(48, UINT48_2)
    rule #WordPackAddrUInt48UInt48 ( ADDR , UINT48_1 , UINT48_2 ) => #asWord ( #buf(6, UINT48_2) +Bytes #buf(6, UINT48_1) +Bytes    #buf(20, ADDR) ) requires #rangeAddress(ADDR)      andBool #rangeUInt(48, UINT48_1) andBool #rangeUInt(48, UINT48_2)
    rule #WordPackAddrUInt8        ( ADDR , UINT8               ) => #asWord (       #buf(11, 0) +Bytes #buf(1,    UINT8) +Bytes    #buf(20, ADDR) ) requires #rangeAddress(ADDR)      andBool #rangeUInt(8,     UINT8)

endmodule
