// SPDX-License-Identifier: UNLICENSED
pragma solidity ^0.8.13;

import "forge-std/Test.sol";

// contract Token{

// }

contract DealTest is Test {

    function testDeal(uint256 value) public {
//        Token alice = new Token();
        address alice = address(1);
        vm.deal(alice, value);
        assertEq(alice.balance, value);
    }

    // function testDealTwice(uint256 value) public {
    //     address alice = address(1);
    //     vm.deal(alice, value);
    //     assertEq(alice.balance, value);
    //     vm.deal(alice, value + 1);
    //     assertEq(alice.balance, value + 1); 
    // }
}