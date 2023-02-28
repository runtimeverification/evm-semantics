// SPDX-License-Identifier: UNLICENSED
pragma solidity =0.8.13;

import "forge-std/Test.sol";

contract AssertTest is Test {
    uint y;

    function setUp() public {}

    function test_assert_true() public pure {
        assert(true);
    }

    function test_assert_true_branch(uint x) public {
        if (x < 3) {
            y = x;
            assert(true);
        } else {
            y = x - 1;
            assert(true);
        }
        assert(y <= x);
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

    function test_revert_branch(uint x, uint y) public{
        if (x < y) {
            assert(true);
        } else {
            assert(false);
        }
    }

    function sum_N(uint n) pure internal returns (uint) {
        uint s = 0;
        while (0 < n) {
            s = s + n;
            n = n - 1;
        }
        return s;
    }

    function test_sum_10() public returns (uint) {
        return sum_N(10);
    }

    function test_sum_100() public returns (uint) {
        return sum_N(100);
    }

    function test_sum_1000() public returns (uint) {
        return sum_N(1000);
    }
}
