// SPDX-License-Identifier: UNLICENSED
pragma solidity =0.8.13;

import "forge-std/Test.sol";

contract AssertTest is Test {
    function setUp() public {}

    function test_assert_true_subdir() public pure {
        assert(true);
    }
}
