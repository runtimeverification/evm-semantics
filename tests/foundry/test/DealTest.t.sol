// SPDX-License-Identifier: UNLICENSED
pragma solidity =0.8.13;

import "forge-std/Test.sol";

contract Token{

}

contract DealTest is Test {

    function testDeal(uint256 value) public {
        Token alice = new Token();
        vm.deal(address(alice), value);
        assertEq(address(alice).balance, value);
    }
}