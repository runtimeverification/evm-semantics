// SPDX-License-Identifier: UNLICENSED
pragma solidity =0.8.13;

import "forge-std/Test.sol";

contract AssumeTest is Test {
    uint256 MAX_INT = 2**256 - 1;

    function test_assume_true(uint256 a, uint256 b) public {
        vm.assume(a == b);
        assertEq(a, b);
    }

    function test_assume_false(uint256 a, uint256 b) public {
        vm.assume(a != b);
        assertEq(a, b);
    }

    function testFail_assume_true(uint256 a, uint256 b) public {
        vm.assume(a != b);
        assertEq(a, b);
    }

    function testFail_assume_false(uint256 a, uint256 b) public {
        vm.assume(a == b);
        assertEq(a, b);
    }
}