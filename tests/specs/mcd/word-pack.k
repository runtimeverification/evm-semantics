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
    imports WORD-PACK-HASKELL
endmodule

module WORD-PACK-HASKELL [kore]
    imports WORD-PACK-COMMON

    rule    { ADDR_UINT48_UINT48:Int #Equals #WordPackAddrUInt48UInt48(ADDR:Int, UINT48_1:Int, UINT48_2:Int) }
         => { true #Equals (
                        ADDR   ==Int maxUInt160 &Int  ADDR_UINT48_UINT48
              andBool UINT48_1 ==Int maxUInt48  &Int (ADDR_UINT48_UINT48 /Int pow160)
              andBool UINT48_2 ==Int maxUInt48  &Int (ADDR_UINT48_UINT48 /Int pow208)
              andBool #rangeUInt(256, ADDR_UINT48_UINT48)
            ) }
            [simplification]

    rule    { #WordPackAddrUInt48UInt48(ADDR:Int, UINT48_1:Int, UINT48_2:Int) #Equals ADDR_UINT48_UINT48:Int }
         => { true #Equals (
                        ADDR   ==Int maxUInt160 &Int  ADDR_UINT48_UINT48
              andBool UINT48_1 ==Int maxUInt48  &Int (ADDR_UINT48_UINT48 /Int pow160)
              andBool UINT48_2 ==Int maxUInt48  &Int (ADDR_UINT48_UINT48 /Int pow208)
              andBool #rangeUInt(256, ADDR_UINT48_UINT48)
            ) }
            [simplification]

    rule    { UINT48_UINT48 #Equals #WordPackUInt48UInt48(UINT48_1, UINT48_2) }
         => { true #Equals (
                      UINT48_1 ==Int maxUInt48 &Int  UINT48_UINT48
              andBool UINT48_2 ==Int maxUInt48 &Int (UINT48_UINT48 /Int pow48)
              andBool #rangeUInt(96, UINT48_UINT48)
            ) }
            [simplification]

    rule    { #WordPackUInt48UInt48(UINT48_1, UINT48_2) #Equals UINT48_UINT48}
         => { true #Equals (
                      UINT48_1 ==Int maxUInt48 &Int  UINT48_UINT48
              andBool UINT48_2 ==Int maxUInt48 &Int (UINT48_UINT48 /Int pow48)
              andBool #rangeUInt(96, UINT48_UINT48)
            ) }
            [simplification]

    rule    { #WordPackAddrUInt8(ADDR, UINT8) #Equals ADDR_UINT8 }
         => { true #Equals (
                      ADDR  ==Int maxUInt160 &Int  ADDR_UINT8
              andBool UINT8 ==Int maxUInt8   &Int (ADDR_UINT8 /Int pow160)
              andBool #rangeUInt(168, ADDR_UINT8)
            ) }
            [simplification]

    rule    { ADDR_UINT8 #Equals #WordPackAddrUInt8(ADDR, UINT8) }
         => { true #Equals (
                      ADDR  ==Int maxUInt160 &Int  ADDR_UINT8
              andBool UINT8 ==Int maxUInt8   &Int (ADDR_UINT8 /Int pow160)
              andBool #rangeUInt(168, ADDR_UINT8)
              andBool #rangeUInt(160, ADDR)
              andBool #rangeUInt(8, UINT8)
            ) }
            [simplification]

    //
    // #WordPack definedness
    //
    rule #Ceil ( #WordPackAddrUInt48UInt48(ADDR, UINT48_1, UINT48_2) ) =>
       { true
           #Equals
         #rangeUInt(160, ADDR) andBool #rangeUInt(48, UINT48_1) andBool #rangeUInt(48, UINT48_2)
       } [simplification]

    rule #Ceil ( #WordPackUInt48UInt48(UINT48_1, UINT48_2) ) =>
       { true #Equals #rangeUInt(48, UINT48_1) andBool #rangeUInt(48, UINT48_2) } [simplification]

    rule #Ceil ( #WordPackAddrUInt8(ADDR, UINT8) ) =>
      { true #Equals #rangeUInt(160, ADDR) andBool #rangeUInt(8, UINT8) } [simplification]

    rule X |Int 0 => X requires 0 <=Int X [simplification]
    rule 0 &Int X => 0 requires 0 <=Int X [simplification]

endmodule

module WORD-PACK-COMMON
    imports EVM-TYPES

    syntax Int ::= #WordPackUInt48UInt48     (       Int , Int ) [function, no-evaluators, smtlib(WordPackUInt48UInt48)]
                 | #WordPackAddrUInt48UInt48 ( Int , Int , Int ) [function, no-evaluators, smtlib(WordPackAddrUInt48UInt48)]
                 | #WordPackAddrUInt8        (       Int , Int ) [function, no-evaluators, smtlib(WordPackAddrUInt8)]
 // -----------------------------------------------------------------------------------------------------------------
    // rule #WordPackUInt48UInt48     (            UINT48_1 , UINT48_2 ) => UINT48_2 *Int pow48 +Int UINT48_1                        requires #rangeUInt(48, UINT48_1) andBool #rangeUInt(48, UINT48_2)
    // rule #WordPackAddrUInt48UInt48 (     ADDR , UINT48_1 , UINT48_2 ) => UINT48_2 *Int pow208 +Int UINT48_1 *Int pow160 +Int ADDR requires #rangeAddress(ADDR) andBool #rangeUInt(48, UINT48_1) andBool #rangeUInt(48, UINT48_2)
    // rule #WordPackAddrUInt8        (     ADDR , UINT8               ) => UINT8 *Int pow160 +Int ADDR                              requires #rangeAddress(ADDR) andBool #rangeUInt(8, UINT_8)

    syntax Int ::= "maskWordPackUInt48UInt48_1" [macro] // 0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFF000000000000FFFFFFFFFFFF
                 | "maskWordPackUInt48UInt48_2" [macro] // 0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFF000000000000
 // -------------------------------------------------------------------------------------------------------------------------
    rule maskWordPackUInt48UInt48_1 => 115792089237316195423570985008687907853269984665561335876943319951794562400255
    rule maskWordPackUInt48UInt48_2 => 115792089237316195423570985008687907853269984665640564039457583726438152929280

    rule (maskWordPackUInt48UInt48_2 &Int UINT48_UINT48) /Int pow48 => maxUInt48 &Int (UINT48_UINT48 /Int pow48) requires #rangeUInt(96, UINT48_UINT48) [simplification]
    rule  maskWordPackUInt48UInt48_1 &Int UINT48_UINT48             => maxUInt48 &Int  UINT48_UINT48             requires #rangeUInt(96, UINT48_UINT48) [simplification]

    rule (UINT48_2 *Int pow48) |Int (maskWordPackUInt48UInt48_1 &Int UINT48_UINT48) => #WordPackUInt48UInt48( (maskWordPackUInt48UInt48_1 &Int UINT48_UINT48), UINT48_2)              requires #rangeUInt(96, UINT48_UINT48) andBool #rangeUInt(48, UINT48_2) [simplification]
    rule  UINT48_1             |Int (maskWordPackUInt48UInt48_2 &Int UINT48_UINT48) => #WordPackUInt48UInt48( UINT48_1 , (maskWordPackUInt48UInt48_2 &Int UINT48_UINT48) /Int pow48 ) requires #rangeUInt(96, UINT48_UINT48) andBool #rangeUInt(48, UINT48_1) [simplification]
    rule (UINT48_2 *Int pow48) |Int (maxUInt48                  &Int UINT48_UINT48) => #WordPackUInt48UInt48( maxUInt48 &Int UINT48_UINT48 , UINT48_2                               ) requires #rangeUInt(96, UINT48_UINT48) andBool #rangeUInt(48, UINT48_2) [simplification]

    syntax Int ::= "maskWordPackAddrUInt48UInt48_2" [macro] // 0xFFFFFFFFFFFF000000000000FFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFF
                 | "maskWordPackAddrUInt48UInt48_3" [macro] // 0x000000000000FFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFF
 // -----------------------------------------------------------------------------------------------------------------------------
    rule maskWordPackAddrUInt48UInt48_2 => 115792089237315784047431654708638870748305248246218003188207458632603225030655
    rule maskWordPackAddrUInt48UInt48_3 => 411376139330301510538742295639337626245683966408394965837152255

    rule (ADDR |Int (notMaxUInt160 &Int ADDR_UINT48_UINT48)) /Int pow160 => ADDR_UINT48_UINT48 /Int pow160 requires #rangeUInt(256, ADDR_UINT48_UINT48) andBool #rangeAddress(ADDR) [simplification]
    rule (ADDR |Int (notMaxUInt160 &Int ADDR_UINT48_UINT48)) /Int pow208 => ADDR_UINT48_UINT48 /Int pow208 requires #rangeUInt(256, ADDR_UINT48_UINT48) andBool #rangeAddress(ADDR) [simplification]

    rule (UINT48_2 *Int pow208) |Int (maskWordPackAddrUInt48UInt48_3 &Int ADDR_UINT48_UINT48) => #WordPackAddrUInt48UInt48(maxUInt160 &Int ADDR_UINT48_UINT48, maxUInt48 &Int (ADDR_UINT48_UINT48 /Int pow160), UINT48_2) requires #rangeUInt(256, ADDR_UINT48_UINT48) andBool #rangeUInt(48, UINT48_2) [simplification]
    rule (UINT48_1 *Int pow160) |Int (maskWordPackAddrUInt48UInt48_2 &Int ADDR_UINT48_UINT48) => #WordPackAddrUInt48UInt48(maxUInt160 &Int ADDR_UINT48_UINT48, UINT48_1, maxUInt48 &Int (ADDR_UINT48_UINT48 /Int pow208)) requires #rangeUInt(256, ADDR_UINT48_UINT48) andBool #rangeUInt(48, UINT48_1) [simplification]

    rule maxUInt48 &Int (maskWordPackUInt48UInt48_2 &Int A) => 0 requires 0 <=Int A [simplification]

    //
    // #WordPack components
    //
    rule maxUInt160 &Int #WordPackAddrUInt48UInt48(X:Int, _, _) => X [simplification]
    rule maxUInt48 &Int (#WordPackAddrUInt48UInt48(_, Y:Int, _) /Int pow160) => Y [simplification]
    rule #WordPackAddrUInt48UInt48(_, _, Z:Int) /Int pow208 => Z [simplification]

    rule maxUInt48 &Int #WordPackUInt48UInt48 (X:Int , _) => X [simplification]
    rule #WordPackUInt48UInt48 (_, Y:Int) /Int pow48 => Y [simplification]

    rule maxUInt160 &Int #WordPackAddrUInt8 (X:Int , _) => X [simplification]
    rule #WordPackAddrUInt8 (_, Y:Int) /Int pow160 => Y [simplification]

    //
    // #WordPack ranges
    //
    rule 0 <=Int #WordPackAddrUInt48UInt48(_, _, _)     => true [simplification]
    rule #WordPackAddrUInt48UInt48(_, _, _) <Int pow256 => true [simplification]

    rule 0 <=Int #WordPackUInt48UInt48(_, _)    => true [simplification]
    rule #WordPackUInt48UInt48(_, _) <Int pow96 => true [simplification]

    rule 0 <=Int #WordPackAddrUInt8(_, _)     => true [simplification]
    rule #WordPackAddrUInt8(_, _) <Int pow168 => true [simplification]

    //
    // More simplifications surrounding pow48/160
    //
    rule maxUInt48  &Int X:Int => X requires #rangeUInt(48, X)  [simplification]
    rule maxUInt160 &Int X:Int => X requires #rangeUInt(160, X) [simplification]
    
    rule maxUInt48 &Int (X /Int pow48) => X /Int pow48 requires #rangeUInt(96, X) [simplification]

    rule maxUInt48  &Int (A:Int |Int B:Int) => (maxUInt48  &Int A) |Int (maxUInt48  &Int B) requires 0 <=Int A andBool 0 <=Int B [simplification]
    rule maxUInt160 &Int (A:Int |Int B:Int) => (maxUInt160 &Int A) |Int (maxUInt160 &Int B) requires 0 <=Int A andBool 0 <=Int B [simplification]

    rule 0 <=Int X &Int Y => true requires 0 <=Int X andBool 0 <=Int Y [simplification]
    rule X &Int Y <Int Z  => true requires 0 <=Int X andBool 0 <=Int Y andBool (X <Int Z orBool Y <Int Z) [simplification]

    rule X /Int Y => 0 requires 0 <=Int X andBool X <Int Y [simplification]
    rule X &Int (X &Int Y) => X &Int Y requires 0 <=Int X andBool 0 <=Int Y [simplification]
endmodule
