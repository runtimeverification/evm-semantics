// SPDX-License-Identifier: UNLICENSED
pragma solidity =0.8.13;

import "forge-std/Test.sol";

contract ExamplesTest is Test {
    function setUp() public {}

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

    function test_wmul_strictly_increasing(uint a, uint b) external {
        uint c = wmul2(a, b);
        assertTrue(a < c && b < c);
    }

    function test_wmul_increasing(uint a, uint b) external {
        uint c = wmul2(a, b);
        assertTrue(a <= c && b <= c);
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
