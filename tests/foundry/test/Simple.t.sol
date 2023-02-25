// SPDX-License-Identifier: UNLICENSED
pragma solidity =0.8.13;

import "forge-std/Test.sol";

contract AssertTest is Test {
    function setUp() public {}

    function test_assert_true() public pure {
        assert(true);
    }

    function test_assert_false() public pure {
        assert(false);
    }

    function testFail_assert_true() public pure {
        assert(true);
    }

    function testFail_assert_false() public pure {
         assert(false);
     }

    function testFail_expect_revert() public {
        vm.expectRevert();
        assert(false);
    }

    function test_source_map() public pure returns (uint) {
        uint x = 0;
        uint y = 1;
        uint z = 2;
        uint a = x + y;
        uint b = z - y;
        uint c = a * b;
        return a + b + c;
    }
}
