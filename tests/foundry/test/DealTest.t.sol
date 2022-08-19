// SPDX-License-Identifier: UNLICENSED
pragma solidity =0.8.13;

import "forge-std/Test.sol";

contract DealTest is Test {

    function testDeal(uint256 value) public {
        address alice = address(1);
        vm.deal(alice, value);
        assertEq(alice.balance, value); // 1000000000000000000
    }
}