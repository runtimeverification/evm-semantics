// SPDX-License-Identifier: UNLICENSED
pragma solidity =0.8.13;

import "forge-std/Test.sol";

contract AssertTest is Test {

    function test_revert_branch(uint x, uint y) public{
        if (x < y) {
            assert(true);
        } else {
            assert(false);
        }
    }
}
