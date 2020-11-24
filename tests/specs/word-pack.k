requires "evm-types.md"

module WORD-PACK
    imports EVM-TYPES

    //
    // The Solidity compiler sometimes packs together multiple arguments into one storage location, for optimized reads/writes.
    // Because the packed variables are all smaller than a `uint256`, they can fit into one word.
    // If you use the pattern `SOMETHING ==K #WordPack*(ARG1, ..., ARGN)` in your side-conditions, you're actually making several assertions about `SOMETHING` and `ARG1 ... ARGN`.
    // First, you're asserting that each `ARGi` can be unpacked from the variable `SOMETHING` using the correct accessors.
    // Second, you're asserting that `SOMETHING` contains no other values than the packed `ARGi` (so we add a range condition to `SOMETHING`).
    // This allows us to turn the side-condition SOMETHING ==K #WordPack*(ARG1, ..., ARGN)` into the more useful side-conditions `ARG1 ==K access1(SOMETHING) andBool ... andBool ARGN ==K accessN(SOMETHING)`.
    // The arguments are packed in reverse order, so that the highest bits are set by the last argument.
    //

    syntax Int ::= #WordPackUInt48UInt48     (       Int , Int ) [function, no-evaluators, smtlib(WordPackUInt48UInt48)]
                 | #WordPackAddrUInt48UInt48 ( Int , Int , Int ) [function, no-evaluators, smtlib(WordPackAddrUInt48UInt48)]
                 | #WordPackAddrUInt8        (       Int , Int ) [function, no-evaluators, smtlib(WordPackAddrUInt8)]
 // -----------------------------------------------------------------------------------------------------------------
    // rule #WordPackUInt48UInt48     (            UINT48_1 , UINT48_2 ) => UINT48_2 *Int pow48 +Int UINT48_1                        requires #rangeUInt(48, UINT48_1) andBool #rangeUInt(48, UINT48_2)
    // rule #WordPackAddrUInt48UInt48 (     ADDR , UINT48_1 , UINT48_2 ) => UINT48_2 *Int pow208 +Int UINT48_1 *Int pow160 +Int ADDR requires #rangeAddress(ADDR) andBool #rangeUInt(48, UINT48_1) andBool #rangeUInt(48, UINT48_2)
    // rule #WordPackAddrUInt8        (     ADDR , UINT8               ) => UINT8 *Int pow160 +Int ADDR                              requires #rangeAddress(ADDR) andBool #rangeUInt(8, UINT_8)

    rule    ADDR_UINT48_UINT48 ==K #WordPackAddrUInt48UInt48(ADDR, UINT48_1, UINT48_2)
         => ADDR     ==Int maxUInt160 &Int  ADDR_UINT48_UINT48
    andBool UINT48_1 ==Int maxUInt48  &Int (ADDR_UINT48_UINT48 /Int pow160)
    andBool UINT48_2 ==Int maxUInt48  &Int (ADDR_UINT48_UINT48 /Int pow208)
    andBool #rangeUInt(256, ADDR_UINT48_UINT48)
      [simplification]

    rule    UINT48_UINT48 ==K #WordPackUInt48UInt48(UINT48_1, UINT48_2)
         => UINT48_1 ==Int maxUInt48 &Int  UINT48_UINT48
    andBool UINT48_2 ==Int maxUInt48 &Int (UINT48_UINT48 /Int pow48)
    andBool #rangeUInt(96, UINT48_UINT48)
      [simplification]

    rule    ADDR_UINT8 ==K #WordPackAddrUInt8(ADDR, UINT8)
         => ADDR  ==Int maxUInt160 &Int  ADDR_UINT8
    andBool UINT8 ==Int maxUInt8   &Int (ADDR_UINT8 /Int pow160)
    andBool #rangeUInt(168, ADDR_UINT8)
      [simplification]

    //
    // When updating variables which originally contained `WordPack*`, the Solidity compiler will mask the original value everywhere _except_ where you're updating.
    // Then the update will be bitwise `|Int` with the masked value, and the new value written back.
    // Here we provide the masks which are used by the Solidity compiler, and rules which fold these bitwise updates back up into semantic `#WordPack*` arguments for the purposes of matching the RHS of proofs.
    //

    syntax Int ::= "maskWordPackUInt48UInt48_1" // pow256 -Int pow96 +Int pow48 -Int 1 == 0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFF000000000000FFFFFFFFFFFF
                 | "maskWordPackUInt48UInt48_2" // pow256 -Int pow48                   == 0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFF000000000000
 // --------------------------------------------------------------------------------------------------------------------------------------------------------
    rule maskWordPackUInt48UInt48_1 => 115792089237316195423570985008687907853269984665561335876943319951794562400255 [macro]
    rule maskWordPackUInt48UInt48_2 => 115792089237316195423570985008687907853269984665640564039457583726438152929280 [macro]

    rule  UINT48_1             |Int (maskWordPackUInt48UInt48_2 &Int UINT48_UINT48) => #WordPackUInt48UInt48( UINT48_1 , (maskWordPackUInt48UInt48_2 &Int UINT48_UINT48) /Int pow48 ) requires #rangeUInt(96, UINT48_UINT48) andBool #rangeUInt(48, UINT48_1) [simplification]
    rule (UINT48_2 *Int pow48) |Int (maxUInt48                  &Int UINT48_UINT48) => #WordPackUInt48UInt48( maxUInt48 &Int UINT48_UINT48 , UINT48_2                               ) requires #rangeUInt(96, UINT48_UINT48) andBool #rangeUInt(48, UINT48_2) [simplification]

    rule (maskWordPackUInt48UInt48_2 &Int UINT48_UINT48) /Int pow48 => maxUInt48 &Int (UINT48_UINT48 /Int pow48) requires #rangeUInt(96, UINT48_UINT48) [simplification]
    rule  maskWordPackUInt48UInt48_1 &Int UINT48_UINT48             => maxUInt48 &Int  UINT48_UINT48             requires #rangeUInt(96, UINT48_UINT48) [simplification]

    //
    // **TODO**: Avoid splitting these lemmas in the 0 second-argument case.
    // The proof which uses these lemmas (flopper-tick-pass-rough) ends up with side-conditions which look like this:
    //  Tic ==K 0 andBool 0 ==K maxUInt48 &Int (#lookup(STORAGE, ADDR) /Int pow160)
    // So if we just have the one rule, then structural matching on the RHS cannot determine that `0` matches `maxUInt48 &Int #lookup(STORAGE, ADDR) /Int pow160)`.
    // This is a consequence of how the Java backend decides to treat substitutions in the side-condition.
    //
    rule (UINT48_2 *Int pow208) |Int (maxUInt208 &Int ADDR_UINT48_UINT48) => #WordPackAddrUInt48UInt48(maxUInt160 &Int ADDR_UINT48_UINT48, maxUInt48 &Int (ADDR_UINT48_UINT48 /Int pow160), UINT48_2) requires #rangeUInt(256, ADDR_UINT48_UINT48) andBool #rangeUInt(48, UINT48_2) andBool maxUInt48 &Int (ADDR_UINT48_UINT48 /Int pow160) =/=Int 0 [simplification]
    rule (UINT48_2 *Int pow208) |Int (maxUInt208 &Int ADDR_UINT48_UINT48) => #WordPackAddrUInt48UInt48(maxUInt160 &Int ADDR_UINT48_UINT48, 0                                              , UINT48_2) requires #rangeUInt(256, ADDR_UINT48_UINT48) andBool #rangeUInt(48, UINT48_2) andBool maxUInt48 &Int (ADDR_UINT48_UINT48 /Int pow160)  ==Int 0 [simplification]

endmodule
