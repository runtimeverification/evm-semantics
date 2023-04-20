// SPDX-License-Identifier: UNLICENSED
pragma solidity =0.8.13;

import "forge-std/Test.sol";

contract ArithmeticTest is Test {
    function max(uint x, uint y) internal pure returns (uint z) {
        if (x < y) {
            return y;
        }
        return x;
    }

    function test_max1(uint a, uint b) external {
        vm.assume(a <= b);
        uint c = max(a, b);
        assertEq(c, b);
    }

    function test_max1_broken(uint a, uint b) external {
        vm.assume(a <= b);
        uint c = max(a, b);
        assertEq(c + 1, a);
    }

    function max2(uint256 x, uint256 y) internal pure returns (uint256) {
        if (x < y && x != 2**100 - 1337) {
            return y;
        }
        return x;
    }

    function test_max2(uint256 x, uint256 y) public {
        uint256 m = max(x, y);
        assertTrue(m >= x && m >= y);
    }

    uint constant MAX_INT = (2 ** 256) - 1;
    uint constant WAD = 10 ** 18;
    uint constant RAY = 10 ** 27;

    function wmul1(uint x, uint y) internal pure returns (uint z) {
        z = ((x * y) + (WAD / 2)) / WAD;
    }

    function wmul2(uint x, uint y) internal pure returns (uint z) {
        z = (x * y) / WAD;
    }

    function wdiv1(uint x, uint y) internal pure returns (uint z) {
        z = ((x * WAD) + (y / 2)) / y;
    }

    function wdiv2(uint x, uint y) internal pure returns (uint z) {
        z = (x * WAD) / y;
    }

    function test_wmul_rounding(uint a, uint b) external {
        uint c1 = wmul1(a, b);
        uint c2 = wmul2(a ,b);
        assertTrue(c2 <= c1);
    }

    function test_wmul_increasing_overflow(uint a, uint b) public {
        uint c = wmul2(a, b);
        assertTrue(a < c && b < c);
    }
    // { true #Equals ( ( 115792089237316195423570985008687907853269984665640564039457584007913129639935 /Int VV0_a_3c5818c8 ) ) <Int VV1_b_3c5818c8 }
    // { true #Equals ( ( maxUInt256 /Int VV0_a_3c5818c8 ) ) <Int VV1_b_3c5818c8 }

    function test_wmul_increasing(uint a, uint b) public {
        if (b <= MAX_INT / a) {
            uint c = wmul2(a, b);
            assertTrue(a < c && b < c);
        }
    }
    // { true #Equals VV0_a_3c5818c8 ==K 0 }

    function test_wmul_increasing_positive(uint a, uint b) public {
        if (0 < a && 0 < b) {
            if (b <= MAX_INT / a) {
                uint c = wmul2(a, b);
                assertTrue(a < c && b < c);
            }
        }
    }
    // { true #Equals ( ( ( ( VV0_a_3c5818c8 *Int VV1_b_3c5818c8 ) ) /Int 1000000000000000000 ) ) <=Int VV0_a_3c5818c8 }

    function test_wmul_increasing_gt_one(uint a, uint b) public {
        if (WAD < a && WAD < b) {
            if (b <= MAX_INT / a) {
                uint c = wmul2(a, b);
                assertTrue(a < c && b < c);
            }
        }
    }
    // #Top

    function test_wmul_weakly_increasing_positive(uint a, uint b) public {
        if (0 < a && 0 < b) {
            if (b <= MAX_INT / a) {
                uint c = wmul2(a, b);
                assertTrue(a <= c && b <= c);
            }
        }
    }
    // { true #Equals VV0_a_3c5818c8 <=Int ( ( chop ( ( ( VV0_a_3c5818c8 *Int VV1_b_3c5818c8 ) ) ) /Int 1000000000000000000 ) ) }
    // { true #Equals VV1_b_3c5818c8 <=Int ( ( chop ( ( ( VV0_a_3c5818c8 *Int VV1_b_3c5818c8 ) ) ) /Int 1000000000000000000 ) ) }
    // { true #Equals VV1_b_3c5818c8 <=Int ( ( 115792089237316195423570985008687907853269984665640564039457584007913129639935 /Int VV0_a_3c5818c8 ) ) }
    // add lemma: rule X *Int Y <Int pow256 => true requires Y <=Int maxUInt256 /Int X [simplification]

    function test_wmul_wdiv_inverse_underflow(uint a, uint b) public {
        if (0 < a && 0 < b) {
            if (b <= MAX_INT / a) {
                uint c = wdiv2(wmul2(a, b), b);
                assertEq(a, c);
            }
        }
    }
    // { true #Equals maxUInt256 /Word ( ( ( ( VV0_a_3c5818c8 *Int VV1_b_3c5818c8 ) ) /Int 1000000000000000000 ) ) <Int 1000000000000000000 }

    // not passing
    function test_wmul_wdiv_inverse(uint a, uint b) public {
        if (WAD < a && WAD < b) {
            if (b <= MAX_INT / a) {
                uint c = wdiv2(wmul2(a, b), b);
                assertEq(a, c);
            }
        }
    }

    function test_wdiv_rounding(uint a, uint b) external {
        uint c1 = wdiv1(a, b);
        uint c2 = wdiv2(a ,b);
        assertTrue(c2 <= c1);
    }

    function test_decreasing_div(uint a, uint b) external {
        uint c1 = wmul1(wdiv1(a, b), b);
        uint c2 = wmul2(wdiv2(a, b), b);
        assertTrue(c1 <= a);
        assertTrue(c2 <= a);
        assertTrue(c2 <= c1);
    }

}
