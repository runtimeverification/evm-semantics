// SPDX-License-Identifier: UNLICENSED
pragma solidity =0.8.13;

import "forge-std/Test.sol";

contract MethodDisambiguateTest is Test {

    function getNumber(uint256 x) public returns(uint256) {
        assertEq(x, x);
        return 1;
    }

    function getNumber(uint32 x) public returns(uint256) {
        assertEq(x, x);
        return 2;
    }

    function test_method_call() public {
        uint256 x = 0;
        assertEq(1, getNumber(x));
    }
}
