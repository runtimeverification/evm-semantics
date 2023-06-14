// SPDX-License-Identifier: UNLICENSED
pragma solidity =0.8.13;

import "forge-std/Test.sol";

contract AssertTest is Test {
    uint y;

    function setUp() public {}

    function test_failing_branch(uint x) public {
      assert(x >= 100);
    }

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

    function test_revert_branch(uint x, uint y) public{
        if (x < y) {
            assert(true);
        } else {
            assert(false);
        }
    }
}
